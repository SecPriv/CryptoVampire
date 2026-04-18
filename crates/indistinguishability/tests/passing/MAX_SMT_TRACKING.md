# Max SMT Time Tracking

The parallel solver tester now captures and reports the **max SMT time** metric from successful test runs.

## What is Max SMT Time?

The `max smt` metric reported by the indistinguishability tool represents the longest time spent in a single SMT solver call during the test. This is useful for:
- Identifying performance bottlenecks
- Understanding solver behavior across different configurations
- Comparing the impact of different solvers on proof complexity

## Output Format

### Detailed CSV
The `detailed_*.csv` file now includes a `max_smt_ms` column:

```csv
test_file,config,result,time,max_smt_ms,notes
basic-hash.scm,all-enabled,PASS,2.25,34.48,
hash-lock.scm,all-enabled,PASS,6.66,90.13,
```

### Report Statistics
The text report now includes **Max SMT Time Statistics**:

```
Max SMT Time Statistics:
------------------------------
Tests with SMT data: 3
Average max SMT: 52.546ms
Min max SMT: 33.032ms
Max max SMT: 90.129ms

File Compatibility Matrix:
==================================================

basic-hash.scm: all-enabled (avg max smt: 34.48ms, worst: 34.48ms)
hash-lock.scm: all-enabled (avg max smt: 90.13ms, worst: 90.13ms)
mw.scm: all-enabled (avg max smt: 33.03ms, worst: 33.03ms)
```

## Implementation Details

### Rust Changes (`src/problem/report.rs`)
Added a getter for `max_vampire` duration:
```rust
pub fn get_max_smt_time(&self) -> Duration {
    self.max_vampire
}
```

Registered it in the Scheme module:
```rust
.register_fn("get-max-smt-time", Self::get_max_smt_time)
```

### Scheme Changes (`tests/save-results.scm`)
Updated to capture and save max smt time:
```scheme
(max-smt (report->get-max-smt-time report))
(print-row file name runtime vampire max-smt total hits hit-rate vampire-timeout)
```

### Python Changes (`test-solvers-parallel.py`)
Added parsing function to extract max smt from output:
```python
def parse_max_smt_time(output: str) -> Optional[float]:
    # Parses "max smt: Xms Yus Zns" format
    # Returns time in milliseconds
```

The parser handles formats like:
- `max smt: 34ms 600us 521ns` → 34.600521 ms
- `max smt: 90ms` → 90.0 ms

## Usage

No changes to usage! The max SMT time is automatically captured for all successful tests:

```bash
# Run tests - max SMT is automatically tracked
make test-solvers-parallel

# Check detailed results
cat solver-test-results/detailed_*.csv

# View statistics
cat solver-test-results/report_*.txt
```

## Notes

- Max SMT time is only captured for **successful** tests (PASS)
- Failed, timed out, or errored tests will have empty `max_smt_ms` field
- The metric is preserved across checkpoint/resume cycles
- Statistics are aggregated across all tests and per-file
