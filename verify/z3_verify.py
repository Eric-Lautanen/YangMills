"""Z3 verifier for the verify_proof tool.

Reads SMT-LIB2 from stdin (or a file path argument) and checks satisfiability.
Returns exit code 0 if UNSAT (proof valid), non-zero otherwise.
"""
import sys
import z3


def main() -> int:
    if len(sys.argv) > 1 and sys.argv[1]:
        # Read from file argument
        filename = sys.argv[1]
        with open(filename, 'r') as f:
            smt2_input = f.read()
    else:
        # Read from stdin
        smt2_input = sys.stdin.read()

    if not smt2_input.strip():
        print("Error: No SMT-LIB2 input provided", file=sys.stderr)
        return 1

    solver = z3.Solver()
    solver.from_string(smt2_input)
    result = solver.check()

    if result == z3.unsat:
        print("UNSAT - Proof valid")
        return 0
    elif result == z3.sat:
        print("SAT - Proof invalid (counterexample exists)")
        return 1
    else:
        print(f"UNKNOWN - Solver could not determine satisfiability: {result}")
        return 1


if __name__ == "__main__":
    sys.exit(main())
