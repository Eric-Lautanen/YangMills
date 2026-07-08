# Yang-Mills Millennium Prize

A rigorous, formally verified approach to the Yang-Mills mass gap problem (Clay Millennium Prize).

## Goals

- **Primary**: Construct a rigorous solution to the Yang-Mills existence and mass gap problem using modern mathematical tools (constructive QFT, stochastic quantization, lattice gauge theory, geometric analysis).
- **Secondary**: Produce a fully formalized proof in Lean 4, checked by a proof assistant.

## Project Structure

```
verify/         # Verifier scripts (Lean, Coq, Z3)
src/
  lean/         # Lean 4 formalization
  coq/          # Coq formalization (backup)
  z3/           # SMT-LIB2 benchmarks
docs/           # Documentation and notes
literature/     # Literature survey and references
```

## Progress

See `project_task_list` via the agent tool for current milestone status.

## Verifier Backends

| Backend | Status | Installation |
|---------|--------|-------------|
| Lean 4  | ✅ v4.31.0 | via elan |
| Z3      | ✅ v4.16.0 | via pip install z3-solver |
| Coq     | ❌ Not installed | via opam or Windows installer |

## License

Academic use. No warranty.
