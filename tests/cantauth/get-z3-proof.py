import z3

# Load SMT file
smt_file_path = "test.smt"
with open(smt_file_path, 'r') as f:
    smt_content = f.read()

# Create a Z3 solver instance
z3.set_param('proof', True)
solver = z3.Solver()

# Parse the SMT content
solver.from_string(smt_content)

# Check satisfiability and get a proof
result = solver.check()
if result == z3.unsat:
    proof = solver.proof()
    proof_str = proof.sexpr()
    # print("UNSAT")
    # print("Proof:")
    print(proof_str)
    
    # Save the proof to a dot file for visualization
    # dot_file_path = "proof.dot"
    # with open(dot_file_path, 'w') as f:
    #     # f.write(z3.proof_to_dot(proof))
    
    # # Optionally, visualize the proof using Graphviz
    # # This requires Graphviz to be installed on your system
    # try:
    #     subprocess.run(['dot', '-Tpng', dot_file_path, '-o', 'proof.png'])
    #     print("Proof visualization saved as proof.png")
    # except FileNotFoundError:
    #     print("Graphviz is not installed. Please install Graphviz to visualize the proof.")
elif result == z3.sat:
    model = solver.model()
    print("SAT")
    print("Model:")
    print(model)
else:
    print("UNKNOWN")