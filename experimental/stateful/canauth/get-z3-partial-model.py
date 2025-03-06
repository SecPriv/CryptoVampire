from z3 import *

# Create a solver
solver = Solver()

# Add some constraints
smt_file_path = "test.smt"
with open(smt_file_path, 'r') as f:
    smt_content = f.read()
solver.from_string(smt_content)

# Set a timeout (in milliseconds)
solver.set("timeout", 1000)

# Check satisfiability
result = solver.check()

# Retrieve and print the partial model if available
if result == sat:
    print("Satisfiable")
    print(solver.model())
elif result == unsat:
    print("Unsatisfiable")
else:
    print("Unknown (timeout or other reason)")
    # Get the best effort model (partial model)
    partial_model = solver.model()
    if partial_model:
        print("Partial model found:")
        print(partial_model)
    else:
        print("No partial model available")