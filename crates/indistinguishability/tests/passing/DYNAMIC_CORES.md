# Dynamic Core Allocation

The parallel solver tester now dynamically manages core allocation based on your machine's capabilities and forwards core counts to the indistinguishability tool.

## Key Features

### 1. Automatic Core Detection
- Defaults to your machine's total core count (`os.cpu_count()`)
- Can be overridden with `--cores <N>` argument

### 2. Dynamic Core Assignment
- **Vampire-enabled configs** (`all-enabled`, `no-z3`, `no-cvc5`, `vampire-only`): Use ALL available cores
- **Single-core configs** (`no-vampire`, `z3-only`, `cvc5-only`, `no-solvers`): Use 1 core each

### 3. Core Forwarding
The `--cores <N>` flag is automatically forwarded to the indistinguishability binary for each test, ensuring Vampire uses the correct number of threads.

## Usage Examples

```bash
# Use all available cores (default behavior)
python3 test-solvers-parallel.py

# Use specific core count
python3 test-solvers-parallel.py --cores 8

# Test with fewer cores to leave resources for other tasks
python3 test-solvers-parallel.py --cores 4 --configs all-enabled

# Mix of configs showing dynamic allocation
python3 test-solvers-parallel.py --configs all-enabled no-vampire z3-only
# - all-enabled: uses all 16 cores (runs alone)
# - no-vampire: uses 1 core (can run 15 in parallel)
# - z3-only: uses 1 core (can run 15 in parallel)
```

## Progress Bar

The progress bar now shows actual core usage:
```
[█████████████░░░░░░░░░░░░░░░░░░░░░░░░░░░] 1/3 (33.3%) | Running: 2 | Cores: 1/16 | Elapsed: 0:00:02
```

Notice:
- `Running: 2` - Two tests running in parallel (both 1-core configs)
- `Cores: 1/16` - Using 1 out of 16 available cores

When a vampire test runs:
```
[██████████████████████████░░░░░░░░░░░░░░] 2/3 (66.7%) | Running: 1 | Cores: 16/16 | Elapsed: 0:00:02
```

- `Running: 1` - Only one test (vampire hogs all cores)
- `Cores: 16/16` - All cores in use

## Scheduling Strategy

The scheduler maximizes parallelism by:

1. **Running 1-core tests in parallel**: Up to 16 single-core tests can run simultaneously
2. **Running vampire tests exclusively**: When a vampire-enabled test starts, it gets all cores
3. **Dynamic queuing**: Tests are queued and started as cores become available

### Example Schedule (16 cores, 3 configs)

```
Time →
[no-vampire: 1 core] [z3-only: 1 core]     ← Run in parallel (2/16 cores used)
[all-enabled: 16 cores]                    ← Runs alone (16/16 cores used)
```

## Implementation Details

### Core Discovery
```python
DEFAULT_TOTAL_CORES = os.cpu_count() or 4
```

### Core Assignment
```python
@classmethod
def get_cores(cls, config_name: str, total_cores: int) -> int:
    if config_name in cls.VAMPIRE_CONFIGS:
        return total_cores  # All cores for vampire
    else:
        return 1  # Single core for others
```

### Command Forwarding
```python
cmd = [
    str(binary),
    "--root-directory", str(script_dir),
    "--cores", str(job.cores),  # Forward core count
    "file", str(script_dir / job.file)
]
```

## Benefits

1. **Adapts to any machine**: Works on 4-core laptops or 64-core servers
2. **No over-provisioning**: Never allocates more cores than available
3. **Optimal parallelism**: Maximizes test throughput
4. **Accurate resource usage**: Vampire gets the cores it expects
5. **Flexible testing**: Can limit cores to simulate different environments

## Migration Notes

- **No breaking changes**: Existing scripts work without modification
- **Default behavior improved**: Now uses all machine cores instead of hardcoded 16
- **More accurate**: Core count matches what Vampire actually uses
