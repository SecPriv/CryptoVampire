#!/usr/bin/env python3
"""
Parallel solver configuration tester for indistinguishability.

Dynamically allocates cores based on solver requirements:
- vampire-enabled configs: all available cores (default: machine core count)
- z3-only: 1 core
- cvc5-only: 1 core
- no-solvers: 1 core (minimal, runs in parallel)

The --cores argument is forwarded to indistinguishability for each test.

Supports checkpointing and resume for interrupted runs.
"""

import asyncio
import subprocess
import os
import sys
import json
import signal
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass, field
from enum import Enum
import argparse
import hashlib

# Discover available cores from the machine
DEFAULT_TOTAL_CORES = os.cpu_count() or 4


class SolverConfig:
    """Solver configuration with core requirements."""
    
    
    # None => all cores
    # Some(x) => x cores
    BASE_CONFIGS = {
        "no-solvers": {"env": {"DISABLE_VAMPIRE": "true", "DISABLE_Z3": "true", "DISABLE_CVC5": "true"}, "cores": 1},
        "all-enabled": {"env": {}, "cores": None},
        "no-vampire": {"env": {"DISABLE_VAMPIRE": "true"}, "cores": 2},
        "no-z3": {"env": {"DISABLE_Z3": "true"}, "cores": None},  # vampire enabled
        "no-cvc5": {"env": {"DISABLE_CVC5": "true"}, "cores": None},  # vampire enabled
        "vampire-only": {"env": {"DISABLE_Z3": "true", "DISABLE_CVC5": "true"}, "cores": None},
        "z3-only": {"env": {"DISABLE_VAMPIRE": "true", "DISABLE_CVC5": "true"}, "cores": 1},
        "cvc5-only": {"env": {"DISABLE_VAMPIRE": "true", "DISABLE_Z3": "true"}, "cores": 1},
    }
    
    @classmethod
    def get_cores(cls, config_name: str, total_cores: int) -> int:
        if cls.BASE_CONFIGS[config_name]["cores"] == None:
            return total_cores
        else:
            return cls.BASE_CONFIGS[config_name]["cores"]
    
    @classmethod
    def get_env(cls, config_name: str) -> Dict[str, str]:
        base_env = os.environ.copy()
        env_vars = cls.BASE_CONFIGS.get(config_name, {}).get("env", {})
        base_env.update(env_vars)
        return base_env


class TestResult(Enum):
    PASS = "PASS"
    FAIL = "FAIL"
    TIMEOUT = "TIMEOUT"
    ERROR = "ERROR"


def parse_max_smt_time(output: str) -> Optional[float]:
    """
    Parse max smt time from tool output.
    
    Expected format in output: "max smt: Xms Yus Zns" or "max smt: Xms" etc.
    Returns the time in milliseconds.
    """
    import re
    
    # Look for "max smt:" followed by time values
    match = re.search(r'max smt:\s*(\d+)ms\s*(\d+)us\s*(\d+)ns', output)
    if match:
        ms = float(match.group(1))
        us = float(match.group(2)) / 1000.0
        ns = float(match.group(3)) / 1000000.0
        return ms + us + ns
    
    # Try simpler format: "max smt: Xms"
    match = re.search(r'max smt:\s*(\d+)ms', output)
    if match:
        return float(match.group(1))
    
    return None


@dataclass
class TestJob:
    """Represents a single test job."""
    config: str
    file: str
    total_cores: int
    cores: int = field(init=False)
    
    def __post_init__(self):
        self.cores = SolverConfig.get_cores(self.config, self.total_cores)
    
    @property
    def id(self) -> str:
        return f"{self.config}:{self.file}"
    
    @property
    def id_hash(self) -> str:
        return hashlib.md5(self.id.encode()).hexdigest()[:8]


@dataclass
class TestOutcome:
    """Result of a test execution."""
    job: TestJob
    result: TestResult
    duration: float
    output: str = ""
    max_smt_ms: Optional[float] = None


class CoreResourceManager:
    """
    Manages core allocation with dynamic scheduling.
    
    Uses a semaphore-like approach but tracks exact core counts.
    """
    
    def __init__(self, total_cores: int = 16):
        self.total_cores = total_cores
        self.available_cores = total_cores
        self.lock = asyncio.Lock()
        self.waiting = asyncio.Event()
    
    async def acquire(self, cores_needed: int) -> bool:
        """
        Acquire cores, waiting if necessary.
        Returns True when cores are acquired.
        """
        # Special case: 0-core jobs can always run
        if cores_needed == 0:
            return True
        
        while True:
            async with self.lock:
                if self.available_cores >= cores_needed:
                    self.available_cores -= cores_needed
                    return True
                # Calculate how many cores we need to be freed
                needed = cores_needed - self.available_cores
            
            # Wait for resources to be freed
            await self.waiting.wait()
    
    async def release(self, cores_needed: int):
        """Release cores back to the pool."""
        if cores_needed == 0:
            return
        
        async with self.lock:
            self.available_cores += cores_needed
        self.waiting.set()  # Wake up waiters
        self.waiting.clear()
    
    @property
    def usage_percent(self) -> float:
        return ((self.total_cores - self.available_cores) / self.total_cores) * 100


class CheckpointManager:
    """Manages checkpointing and resume functionality."""
    
    def __init__(self, checkpoint_file: Path):
        self.checkpoint_file = checkpoint_file
        self.completed: set = set()
        self.results: List[Dict] = []
    
    def load(self):
        """Load checkpoint if exists."""
        if self.checkpoint_file.exists():
            try:
                with open(self.checkpoint_file, 'r') as f:
                    data = json.load(f)
                self.completed = set(data.get('completed', []))
                self.results = data.get('results', [])
                print(f"Loaded checkpoint: {len(self.completed)} completed tests")
            except Exception as e:
                print(f"Warning: Could not load checkpoint: {e}")
    
    def save(self, outcome: TestOutcome):
        """Save a completed test to checkpoint."""
        self.completed.add(outcome.job.id)
        result_dict = {
            'config': outcome.job.config,
            'file': outcome.job.file,
            'result': outcome.result.value,
            'duration': outcome.duration,
        }
        if outcome.max_smt_ms is not None:
            result_dict['max_smt_ms'] = outcome.max_smt_ms
        self.results.append(result_dict)
        
        # Write checkpoint atomically
        temp_file = self.checkpoint_file.with_suffix('.tmp')
        with open(temp_file, 'w') as f:
            json.dump({
                'completed': list(self.completed),
                'results': self.results,
                'timestamp': datetime.now().isoformat(),
            }, f, indent=2)
        temp_file.rename(self.checkpoint_file)
    
    def is_completed(self, job_id: str) -> bool:
        return job_id in self.completed
    
    def cleanup(self):
        """Remove checkpoint file."""
        if self.checkpoint_file.exists():
            self.checkpoint_file.unlink()


class ProgressBar:
    """Simple progress bar without external dependencies."""
    
    def __init__(self, total: int, total_cores: int = 16):
        self.total = total
        self.total_cores = total_cores
        self.current = 0
        self.start_time = datetime.now()
    
    def update(self, completed: int, running: int, cores_used: int):
        self.current = completed
        percent = (completed / self.total * 100) if self.total > 0 else 0
        bar_width = 40
        filled = int(bar_width * completed / self.total) if self.total > 0 else 0
        bar = '█' * filled + '░' * (bar_width - filled)
        
        elapsed = datetime.now() - self.start_time
        elapsed_str = str(elapsed).split('.')[0]  # Remove microseconds
        
        # Clear line and print progress
        sys.stdout.write('\r' + ' ' * 100 + '\r')  # Clear line
        sys.stdout.write(f'[{bar}] {completed}/{self.total} ({percent:.1f}%) | '
                        f'Running: {running} | Cores: {cores_used}/{self.total_cores} | '
                        f'Elapsed: {elapsed_str}')
        sys.stdout.flush()
    
    def finish(self):
        sys.stdout.write('\n')
        sys.stdout.flush()


async def run_test(
    job: TestJob,
    script_dir: Path,
    timeout: int,
    core_manager: CoreResourceManager,
) -> TestOutcome:
    """Run a single test with timeout and resource management."""
    
    binary = script_dir / "indistinguishability"
    if not binary.exists():
        return TestOutcome(
            job=job,
            result=TestResult.ERROR,
            duration=0,
            output="Binary not found"
        )
    
    cmd = [
        str(binary),
        "--scheme-root-directory", str(script_dir),
        "--cores", str(job.cores),
        str(script_dir / job.file)
    ]
    
    env = SolverConfig.get_env(job.config)
    
    start_time = datetime.now()
    max_smt_ms = None
    
    try:
        # Acquire cores before starting
        await core_manager.acquire(job.cores)
        
        process = await asyncio.create_subprocess_exec(
            *cmd,
            env=env,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
            cwd=str(script_dir),
        )
        
        try:
            stdout, stderr = await asyncio.wait_for(
                process.communicate(),
                timeout=timeout
            )
            output = stdout.decode() + stderr.decode()
            
            if process.returncode == 0:
                result = TestResult.PASS
                # Parse max smt time from output on success
                max_smt_ms = parse_max_smt_time(output)
            else:
                result = TestResult.FAIL
                
        except asyncio.TimeoutError:
            # Kill the process on timeout
            try:
                process.kill()
                await process.wait()
            except:
                pass
            result = TestResult.TIMEOUT
            output = "Test timed out"
        
        finally:
            # Release cores after completion
            await core_manager.release(job.cores)
        
    except Exception as e:
        result = TestResult.ERROR
        output = str(e)
    
    end_time = datetime.now()
    duration = (end_time - start_time).total_seconds()
    
    return TestOutcome(
        job=job,
        result=result,
        duration=duration,
        output=output,
        max_smt_ms=max_smt_ms
    )


async def scheduler(
    jobs: List[TestJob],
    script_dir: Path,
    timeout: int,
    total_cores: int,
    checkpoint: Optional[CheckpointManager],
    progress_bar: ProgressBar,
) -> List[TestOutcome]:
    """
    Schedule and run all tests with dynamic core allocation.
    """
    
    core_manager = CoreResourceManager(total_cores)
    results: List[TestOutcome] = []
    running_tasks: Dict[asyncio.Task, TestJob] = {}
    pending_jobs = []
    
    # Filter out already completed jobs
    for job in jobs:
        if checkpoint and checkpoint.is_completed(job.id):
            # Load result from checkpoint
            results.append(TestOutcome(
                job=job,
                result=TestResult.PASS,  # Placeholder, will be updated
                duration=0,
            ))
        else:
            pending_jobs.append(job)
    
    total_jobs = len(jobs)
    
    print(f"Starting {len(pending_jobs)} tests with {total_cores} cores available")
    print(f"Configurations: {len(set(j.config for j in pending_jobs))}")
    print(f"Files: {len(set(j.file for j in pending_jobs))}")
    print()
    
    while pending_jobs or running_tasks:
        # Update progress
        progress_bar.update(
            completed=total_jobs - len(pending_jobs) - len(running_tasks),
            running=len(running_tasks),
            cores_used=total_cores - core_manager.available_cores
        )
        
        # Start new jobs if we have pending jobs and capacity
        # Sort by core requirement: run small jobs first to maximize parallelism
        pending_jobs.sort(key=lambda j: j.cores)
        
        jobs_to_start = []
        for job in pending_jobs:
            if core_manager.available_cores >= job.cores or job.cores == 0:
                jobs_to_start.append(job)
            else:
                # Can't fit this job, but might fit smaller ones
                # Since we sorted, remaining jobs are >= this one's cores
                break
        
        # Start the jobs we can fit
        for job in jobs_to_start:
            pending_jobs.remove(job)
            task = asyncio.create_task(
                run_test(job, script_dir, timeout, core_manager)
            )
            running_tasks[task] = job
        
        if not running_tasks:
            # No running tasks and no jobs started - should not happen
            if pending_jobs:
                print(f"Warning: {len(pending_jobs)} jobs pending but none started")
                await asyncio.sleep(0.1)
            break
        
        # Wait for at least one task to complete
        done, _ = await asyncio.wait(
            running_tasks.keys(),
            return_when=asyncio.FIRST_COMPLETED
        )
        
        # Process completed tasks
        for task in done:
            job = running_tasks.pop(task)
            try:
                outcome = task.result()
                results.append(outcome)
                
                # Save checkpoint
                if checkpoint:
                    checkpoint.save(outcome)
                
            except Exception as e:
                print(f"\nError processing {job.id}: {e}")
                results.append(TestOutcome(
                    job=job,
                    result=TestResult.ERROR,
                    duration=0,
                    output=str(e)
                ))
    
    progress_bar.finish()
    return results


def generate_jobs(
    configs: List[str],
    files: List[str],
    checkpoint: Optional[CheckpointManager],
    total_cores: int,
) -> List[TestJob]:
    """Generate all test jobs, filtering out completed ones."""
    
    jobs = []
    for config in configs:
        for file in files:
            job = TestJob(config=config, file=file, total_cores=total_cores)
            if checkpoint is None or not checkpoint.is_completed(job.id):
                jobs.append(job)
    
    return jobs


def save_results(
    results: List[TestOutcome],
    results_dir: Path,
    timestamp: str,
    total_runtime: float,
):
    """Save results to CSV and report files."""
    
    # Summary CSV
    summary_file = results_dir / f"summary_{timestamp}.csv"
    with open(summary_file, 'w') as f:
        f.write("test_file,config,result\n")
        for outcome in results:
            f.write(f"{outcome.job.file},{outcome.job.config},{outcome.result.value}\n")
    
    # Detailed CSV
    detailed_file = results_dir / f"detailed_{timestamp}.csv"
    with open(detailed_file, 'w') as f:
        f.write("test_file,config,result,time,max_smt_ms,notes\n")
        for outcome in results:
            notes = ""
            if outcome.result == TestResult.TIMEOUT:
                notes = "timeout"
            max_smt = outcome.max_smt_ms if outcome.max_smt_ms is not None else ""
            f.write(f"{outcome.job.file},{outcome.job.config},{outcome.result.value},"
                   f"{outcome.duration:.2f},{max_smt},{notes}\n")
    
    # Generate report
    report_file = results_dir / f"report_{timestamp}.txt"
    
    # Aggregate statistics
    config_stats = {}
    file_stats = {}
    file_max_smt = {}  # Track max smt per file
    max_smt_times = []
    
    for outcome in results:
        config = outcome.job.config
        file = outcome.job.file
        
        if config not in config_stats:
            config_stats[config] = {"PASS": 0, "FAIL": 0, "TIMEOUT": 0, "ERROR": 0}
        config_stats[config][outcome.result.value] += 1
        
        if file not in file_stats:
            file_stats[file] = []
        if outcome.result == TestResult.PASS:
            file_stats[file].append(config)
        
        # Collect max smt times for successful tests
        if outcome.max_smt_ms is not None:
            max_smt_times.append(outcome.max_smt_ms)
            # Track per-file max smt
            if file not in file_max_smt:
                file_max_smt[file] = []
            file_max_smt[file].append(outcome.max_smt_ms)
    
    with open(report_file, 'w') as f:
        f.write("Solver Configuration Test Report\n")
        f.write("=" * 50 + "\n")
        f.write(f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
        f.write(f"Total runtime: {total_runtime/60:.1f} minutes\n")
        f.write("\n")
        
        f.write("Summary by Configuration:\n")
        f.write("-" * 60 + "\n")
        f.write(f"{'Configuration':<20} {'Pass':>8} {'Fail':>8} {'Timeout':>8} {'Total':>8}\n")
        f.write("-" * 60 + "\n")
        
        for config in sorted(config_stats.keys()):
            stats = config_stats[config]
            total = sum(stats.values())
            f.write(f"{config:<20} {stats['PASS']:>8} {stats['FAIL']:>8} "
                   f"{stats['TIMEOUT']:>8} {total:>8}\n")
        
        f.write("\n")
        f.write("Overall Statistics:\n")
        f.write("-" * 30 + "\n")
        total_tests = len(results)
        total_pass = sum(1 for r in results if r.result == TestResult.PASS)
        total_fail = sum(1 for r in results if r.result == TestResult.FAIL)
        total_timeout = sum(1 for r in results if r.result == TestResult.TIMEOUT)
        total_error = sum(1 for r in results if r.result == TestResult.ERROR)
        
        f.write(f"Total tests: {total_tests}\n")
        f.write(f"Passed: {total_pass}\n")
        f.write(f"Failed: {total_fail}\n")
        f.write(f"Timeout: {total_timeout}\n")
        f.write(f"Error: {total_error}\n")
        if total_tests > 0:
            f.write(f"Success rate: {total_pass * 100 / total_tests:.1f}%\n")
        
        f.write("\n")
        
        # Add max SMT statistics
        if max_smt_times:
            f.write("Max SMT Time Statistics:\n")
            f.write("-" * 30 + "\n")
            f.write(f"Tests with SMT data: {len(max_smt_times)}\n")
            f.write(f"Average max SMT: {sum(max_smt_times) / len(max_smt_times):.3f}ms\n")
            f.write(f"Min max SMT: {min(max_smt_times):.3f}ms\n")
            f.write(f"Max max SMT: {max(max_smt_times):.3f}ms\n")
            f.write("\n")
        
        f.write("File Compatibility Matrix:\n")
        f.write("=" * 50 + "\n\n")
        
        for file in sorted(file_stats.keys()):
            passing_configs = file_stats[file]
            all_configs = len(SolverConfig.BASE_CONFIGS)
            
            if len(passing_configs) == all_configs:
                status = "all configs"
            elif len(passing_configs) == 0:
                status = "none"
            else:
                status = ", ".join(sorted(passing_configs))
            
            # Add max smt info if available
            max_smt_info = ""
            if file in file_max_smt and file_max_smt[file]:
                avg_smt = sum(file_max_smt[file]) / len(file_max_smt[file])
                max_of_max = max(file_max_smt[file])
                max_smt_info = f" (avg max smt: {avg_smt:.3f}ms, worst: {max_of_max:.3f}ms)"
            
            f.write(f"{file}: {status}{max_smt_info}\n")
    
    return summary_file, detailed_file, report_file


def main():
    parser = argparse.ArgumentParser(
        description="Parallel solver configuration tester",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s                                    # Test all configs, all files
  %(prog)s --configs no-vampire z3-only       # Test specific configs
  %(prog)s --files basic-hash.scm             # Test specific files
  %(prog)s --timeout 1800                     # 30 minute timeout
  %(prog)s --resume                           # Resume from checkpoint
  %(prog)s --dry-run                          # Show test plan
        """
    )
    
    parser.add_argument(
        '--configs',
        nargs='+',
        choices=list(SolverConfig.BASE_CONFIGS.keys()),
        help='Configurations to test (default: all)'
    )
    
    parser.add_argument(
        '--files',
        nargs='+',
        help='Test files to run (default: all .scm files)'
    )
    
    parser.add_argument(
        '--timeout',
        type=int,
        default=1800,
        help='Timeout per test in seconds (default: 1800 = 30 min)'
    )
    
    parser.add_argument(
        '--cores',
        type=int,
        default=DEFAULT_TOTAL_CORES,
        help=f'Total available cores (default: {DEFAULT_TOTAL_CORES})'
    )
    
    parser.add_argument(
        '--resume',
        action='store_true',
        help='Resume from checkpoint if exists'
    )
    
    parser.add_argument(
        '--checkpoint',
        type=Path,
        default=None,
        help='Checkpoint file path (default: .solver-test-checkpoint.json)'
    )
    
    parser.add_argument(
        '--dry-run',
        action='store_true',
        help='Show test plan without running'
    )
    
    parser.add_argument(
        '--output-dir',
        type=Path,
        default=None,
        help='Output directory for results (default: solver-test-results)'
    )
    
    args = parser.parse_args()
    
    # Setup paths
    script_dir = Path(__file__).parent.resolve()
    results_dir = args.output_dir or (script_dir / "solver-test-results")
    checkpoint_file = args.checkpoint or (script_dir / ".solver-test-checkpoint.json")
    
    # Find test files
    if args.files:
        files = args.files
    else:
        # Find all .scm files
        files = []
        for pattern in ["*.scm", "stateful/*.scm"]:
            files.extend(str(p.relative_to(script_dir)) for p in script_dir.glob(pattern))
        files = sorted(set(files))
    
    # Determine configurations
    if args.configs:
        configs = args.configs
    else:
        configs = list(SolverConfig.BASE_CONFIGS.keys())
    
    # Validate files exist
    missing_files = []
    for file in files:
        if not (script_dir / file).exists():
            missing_files.append(file)
    
    if missing_files:
        print(f"Error: Missing files: {missing_files}")
        sys.exit(1)
    
    # Check binary exists
    binary = script_dir / "indistinguishability"
    if not binary.exists():
        print("Binary not found. Building...")
        try:
            subprocess.run(["make", str(binary.name)], cwd=script_dir, check=True)
        except subprocess.CalledProcessError:
            print("Error: Failed to build binary")
            sys.exit(1)
    
    # Initialize checkpoint manager
    checkpoint = None
    if args.resume or checkpoint_file.exists():
        checkpoint = CheckpointManager(checkpoint_file)
        if args.resume:
            checkpoint.load()
        else:
            print(f"Checkpoint file exists. Use --resume to continue from {checkpoint_file}")
            print(f"Or remove it to start fresh: rm {checkpoint_file}")
            sys.exit(1)
    
    # Generate jobs
    jobs = generate_jobs(configs, files, checkpoint, args.cores)
    
    # Show test plan
    print("Test Plan")
    print("=" * 60)
    print(f"Configurations: {len(configs)}")
    for config in configs:
        cores = SolverConfig.get_cores(config, args.cores)
        print(f"  - {config}: {cores} cores")
    print(f"Files: {len(files)}")
    print(f"Total test combinations: {len(configs) * len(files)}")
    if checkpoint:
        print(f"Already completed: {len(checkpoint.completed)}")
    print(f"Tests to run: {len(jobs)}")
    print(f"Timeout per test: {args.timeout}s ({args.timeout/60:.1f} min)")
    print(f"Available cores: {args.cores}")
    print()
    
    if args.dry_run:
        print("Dry run - not executing tests")
        return
    
    if not jobs:
        print("All tests already completed (from checkpoint)")
        if checkpoint:
            checkpoint.cleanup()
        return
    
    # Create results directory
    results_dir.mkdir(exist_ok=True)
    
    # Run tests
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    progress_bar = ProgressBar(len(jobs) + (len(checkpoint.completed) if checkpoint else 0), args.cores)
    
    print("Starting tests...")
    print()
    
    start_time = datetime.now()
    
    try:
        results = asyncio.run(
            scheduler(
                jobs=jobs,
                script_dir=script_dir,
                timeout=args.timeout,
                total_cores=args.cores,
                checkpoint=checkpoint,
                progress_bar=progress_bar,
            )
        )
    except KeyboardInterrupt:
        print("\n\nInterrupted! Checkpoint saved. Resume with --resume")
        sys.exit(1)
    
    end_time = datetime.now()
    total_runtime = (end_time - start_time).total_seconds()
    
    print()
    print()
    
    # Save results
    summary_file, detailed_file, report_file = save_results(
        results, results_dir, timestamp, total_runtime
    )
    
    # Print summary
    print("Test Complete!")
    print("=" * 60)
    print(f"Total runtime: {total_runtime/60:.1f} minutes")
    print(f"Tests run: {len(results)}")
    
    pass_count = sum(1 for r in results if r.result == TestResult.PASS)
    fail_count = sum(1 for r in results if r.result == TestResult.FAIL)
    timeout_count = sum(1 for r in results if r.result == TestResult.TIMEOUT)
    error_count = sum(1 for r in results if r.result == TestResult.ERROR)
    
    print(f"Passed: {pass_count}")
    print(f"Failed: {fail_count}")
    print(f"Timeout: {timeout_count}")
    print(f"Error: {error_count}")
    
    if len(results) > 0:
        print(f"Success rate: {pass_count * 100 / len(results):.1f}%")
    
    print()
    print("Results saved to:")
    print(f"  Summary:  {summary_file}")
    print(f"  Detailed: {detailed_file}")
    print(f"  Report:   {report_file}")
    
    # Cleanup checkpoint on success
    if checkpoint:
        checkpoint.cleanup()
        print(f"  Checkpoint removed")


if __name__ == "__main__":
    main()
