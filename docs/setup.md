# Yang-Mills project setup notes

## Verifier Backends

### Lean 4 (v4.31.0)
- Installed via `elan` (Lean version manager)
- Build command: `lake build`
- Source directory: `src/lean/`
- Library name: `YangMills`

### Z3 (v4.16.0)
- Installed via `pip install z3-solver`
- Python API available via `import z3`

### Coq (not installed)
- Install via `opam` or Windows installer when needed

## Project Structure

```
.
├── src/
│   ├── lean/          # Lean 4 source files
│   │   ├── YangMills.lean        # Top-level module
│   │   └── YangMills/            # Sub-modules
│   ├── coq/           # Coq source files (future)
│   └── z3/            # SMT-LIB2 benchmarks (future)
├── verify/
│   ├── lean.bat       # Lean verifier wrapper
│   ├── coq.bat        # Coq verifier wrapper (requires Coq)
│   └── z3.bat         # Z3 verifier wrapper
├── literature/        # Literature survey notes
├── docs/              # Documentation
├── lakefile.lean      # Lean/Lake configuration
└── .gitignore
```

## verify_proof tool

The `verify_proof` agent tool is a stub. It currently outputs the proof code
for manual verification. The batch scripts in `verify/` can be used for
manual verification:

```cmd
set PATH=%USERPROFILE%\.elan\bin;%PATH%
lean verify/input.lean
```

```cmd
python -c "import z3; z3.main(['z3', 'verify/input.smt2'])"
```
