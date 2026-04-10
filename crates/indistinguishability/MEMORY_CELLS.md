# Memory Cells Implementation

## Overview

Memory cells provide mutable state in protocol specifications. They allow tracking state that persists across time steps, such as session keys, counters, or protocol state machines.

## Breaking Change: Step Lambda Signature

**Date**: 2026-04-10

The lambda signature for step conditions and messages has changed to support memory cells.

### Old Signature
```scheme
(lambda (in i j) ...)  ; in = macro_input, i,j = step variables
```

### New Signature
```scheme
(lambda (cells in i j) ...)  ; cells = memory cell accessor hashmap
```

### Migration Guide

For existing code that doesn't use memory cells, simply ignore the first parameter:

```scheme
;; Before
(define tag
  (declare-step pbl "tag" (list Index)
    (step p1 (lambda _ mtrue)
      (lambda (in i)
        (tuple (n i) (hash (n i) k))))))

;; After
(define tag
  (declare-step pbl "tag" (list Index)
    (step p1 (lambda _ mtrue)
      (lambda (_ cells in i)  ; or just (_ in i) if not using cells
        (tuple (n i) (hash (n i) k))))))
```

## Usage

### Declaring Memory Cells

```scheme
;; Declare a memory cell with index parameter (array-like)
(define sT (declare-memory-cell pbl "sT" (list Index)))

;; Declare a memory cell with no parameters (single value)
(define counter (declare-memory-cell pbl "counter" '()))
```

### Accessing Memory Cells in Steps

The `cells` parameter is a hashmap that provides access to memory cells at the **previous** time step:

```scheme
(define tag
  (declare-step pbl "tag" (list Index)
    (step p1 (lambda _ mtrue)
      (lambda (cells in i)
        ;; Access sT[i] at previous time step
        (let ((prev-state ((cells sT) i)))
          (tuple
            (G prev-state k-prime)  ; Output
            (H prev-state k))))))   ; New state
```

### Setting Memory Cell Assignments

Use `set-step-assignment!` to specify how memory cells are updated:

```scheme
(bind ((i Index) (p Protocol) (t Time))
  (set-step-assignment! pbl (tag i) p sT '()
    ;; sT(i) := H(sT(i)@t, k)
    (H (macro_memory_cell (sT i) t p) k)))
```

### Complete Example

```scheme
(require "cryptovampire/protocol")
(require "cryptovampire/builtin-functions")

(define pbl (mk-problem 'x))
(define p1 (declare-protocol pbl))
(define p2 (declare-protocol pbl))

;; Declare memory cell
(define sT (declare-memory-cell pbl "sT" (list Index)))

;; Tag process with state
(define tag
  (declare-step pbl "tag" (list Index)
    (step p1 (lambda _ mtrue)
      (lambda (cells in i)
        (tuple
          (G ((cells sT) i) k-prime)  ; Read previous state
          (H ((cells sT) i) k))))     ; Compute new state
    (step p2 (lambda _ mtrue)
      (lambda (cells in i)
        (tuple
          (G ((cells sT) i) k-prime)
          (H ((cells sT) i) k))))))

;; Set assignment: sT(i) := H(sT(i)@pred, k)
(bind ((i Index) (p Protocol) (t Time))
  (set-step-assignment! pbl (tag i) p sT '()
    (H (macro_memory_cell (sT i) t p) k)))
```

## Technical Details

### Time Semantics

- Memory cells accessed via `(cells cell-name)` return the value at **`pred(step-time)`**
- This represents the state **before** the current step executes
- Assignments specify the **new** value that will be stored after the step

### Initialization

Memory cells must be initialized in the `init` step. Use `set-init-step`:

```scheme
(set-init-step pbl
  (step p1 (lambda _ mtrue) (lambda (_ in) mtrue))
  (step p2 (lambda _ mtrue) (lambda (_ in) mtrue)))
```

Note: Initial values are currently handled by the backend. Future versions may support explicit initial value specification.

### Limitations

1. **No mutex/locking**: Memory cell access is not synchronized. Concurrent updates may have undefined semantics.
2. **Only previous time**: Can only access `pred(step-time)`, not arbitrary historical values.
3. **No conditional assignments**: Assignments always execute when the step executes (no "only if condition" support yet).

## Files Modified

- `scheme/libs/protocol.scm` - Added memory cell tracking and `cells` parameter
- `src/input/shared_problem.rs` - Added `declare_memory_cell` and `set_step_assignment` Steel bindings
- `src/protocol/memory_cell.rs` - Memory cell data structures
- `src/protocol/step.rs` - Added `set-step-assignment!` Steel binding
- `src/problem/protocol.rs` - Added `declare_memory_cell` method

## Testing

See `tests/passing/running-ex.scm` for a complete example with memory cells.
