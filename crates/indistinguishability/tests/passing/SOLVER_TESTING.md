# Parallel Solver Configuration Testing

This directory contains tools for testing which examples pass with which solvers disabled.

## Quick Start

```bash
# Run all tests with all solver configurations (144 test combinations)
make test-solvers-parallel

# Run with custom timeout (30 minutes per test)
make test-solvers-parallel TIMEOUT=1800

# Resume an interrupted run
make test-solvers-parallel RESUME=1
```

## Core Allocation Strategy

The parallel tester uses **dynamic core allocation** to maximize parallelism while respecting solver constraints:

| Configuration     | Cores Used | Parallelism |
|------------------|------------|-------------|
| `all-enabled`     | 16         | 1 at a time |
| `no-vampire`      | 1          | Up to 16    |
| `no-z3`           | 16         | 1 at a time |
| `no-cvc5`         | 16         | 1 at a time |
| `vampire-only`    | 16         | 1 at a time |
| `z3-only`         | 1          | Up to 16    |
| `cvc5-only`       | 1          | Up to 16    |
| `no-solvers`      | 0          | Unlimited   |

**Why?** Vampire is multithreaded and uses all available cores, while z3 and cvc5 are single-threaded.

## Usage Examples

### Test Specific Configurations

```bash
# Test only non-vampire configurations (faster)
make test-solvers-parallel CONFIGS="no-vampire z3-only cvc5-only no-solvers"

# Test only vampire-enabled configurations
make test-solvers-parallel CONFIGS="all-enabled no-z3 no-cvc5 vampire-only"
```

### Test Specific Files

```bash
# Test a single file with all configurations
make test-solvers-parallel FILES="basic-hash.scm"

# Test multiple specific files
make test-solvers-parallel FILES="basic-hash.scm ddh-P.scm ddh-S.scm"
```

### Combined Examples

```bash
# Test 3 files with 2 configurations (6 tests total, runs in parallel)
make test-solvers-parallel CONFIGS="all-enabled no-vampire" FILES="basic-hash.scm hash-lock.scm mw.scm"

# Quick smoke test with short timeout
make test-solvers-parallel CONFIGS="all-enabled" TIMEOUT=300
```

### Resume Interrupted Runs

If a test run is interrupted (Ctrl+C), the checkpoint is automatically saved:

```bash
# Resume from where it left off
make test-solvers-parallel RESUME=1

# Or with custom parameters
make test-solvers-parallel RESUME=1 TIMEOUT=3600
```

### Dry Run (Preview Test Plan)

```bash
# See what would be tested without running
make test-solvers-parallel DRY_RUN=1
```

## Python Script Direct Usage

You can also use the Python script directly:

```bash
# Show help
python3 test-solvers-parallel.py --help

# Test specific configurations
python3 test-solvers-parallel.py --configs all-enabled no-vampire

# Test specific files
python3 test-solvers-parallel.py --files basic-hash.scm hash-lock.scm

# Custom timeout and cores
python3 test-solvers-parallel.py --timeout 3600 --cores 16

# Resume from checkpoint
python3 test-solvers-parallel.py --resume
```

## Output Files

Results are saved to `solver-test-results/`:

- `summary_YYYYMMDD_HHMMSS.csv` - Simple CSV: `test_file,config,result`
- `detailed_YYYYMMDD_HHMMSS.csv` - Detailed CSV with timing: `test_file,config,result,time,notes`
- `report_YYYYMMDD_HHMMSS.txt` - Human-readable report with compatibility matrix

## Progress Bar

The parallel tester shows real-time progress:

```
[████████████████████░░░░░░░░░░░░░░░░░░░░] 5/9 (55.6%) | Running: 4 | Cores: 1/16 | Elapsed: 0:00:00
```

- **Progress bar**: Visual completion percentage
- **Running**: Number of tests currently executing
- **Cores**: Core usage out of 16 total
- **Elapsed**: Time since test start

## Estimated Runtime

With 144 test combinations (8 configs × 18 files) and 30-minute timeout:

- **Best case** (tests complete quickly): ~30-60 minutes
- **Worst case** (all timeout): ~12+ hours (vampire tests must run sequentially)

The parallel scheduler minimizes wall-clock time by:
1. Running 1-core tests (z3-only, cvc5-only, no-vampire) in parallel (up to 16 at once)
2. Running 16-core tests (vampire-enabled) one at a time
3. Dynamically scheduling to maximize core utilization

## Troubleshooting

### Checkpoint Issues

If you want to start fresh instead of resuming:

```bash
rm .solver-test-checkpoint.json
make test-solvers-parallel
```

### Binary Not Found

The script will automatically build the binary if missing. If it fails:

```bash
make indistinguishability
```

### Too Many Timeouts

Increase the timeout:

```bash
make test-solvers-parallel TIMEOUT=3600  # 60 minutes per test
```
