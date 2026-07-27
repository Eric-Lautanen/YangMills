# Yang-Mills project setup notes

## Verifier Backends

### Lean 4 (v4.32.0-rc1)
- Installed via `elan` (Lean version manager)
- Build command: `lake build`
- Source directory: `src/lean/`
- Library name: `YangMills`
- On Windows, ensure `%USERPROFILE%\.elan\bin` is in `PATH`

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
│   │       ├── Overview.lean           # Status and references
│   │       ├── SpecialUnitary.lean     # SU(N) group
│   │       ├── OSAxioms.lean           # OS axioms skeleton
│   │       ├── GaugeTheory.lean        # Gauge theory foundations
│   │       ├── Lattice.lean            # Lattice gauge theory
│   │       ├── MassGap.lean            # Mass gap definition
│   │       └── Proofs/
│   │           ├── BasicLemmas.lean           # Trace lemmas
│   │           ├── GaugeInvariance.lean       # Gauge invariance
│   │           ├── JacobiIdentity.lean        # Jacobi identity
│   │           ├── LatticeMeasure.lean        # Lattice measure
│   │           └── ReflectionPositivity.lean  # Reflection positivity
│   ├── coq/           # Coq source files (future)
│   └── z3/            # SMT-LIB2 benchmarks (future)
├── verify/
│   ├── lean.bat       # Lean verifier wrapper
│   ├── coq.bat        # Coq verifier wrapper (requires Coq)
│   └── z3.bat         # Z3 verifier wrapper
├── literature/        # Literature survey notes
├── docs/              # Documentation
│   ├── plan.md        # Project plan
│   ├── setup.md       # This file
│   └── strategy.md    # Strategic decisions
├── lakefile.lean      # Lean/Lake configuration
├── lean-toolchain     # Lean version pinning (v4.32.0-rc1)
├── test_import.lean    # Quick import test
└── README.md
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

## Building

```bash
# First time setup
curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

# Build all sources
cd YangMills
lake build

# The build will compile all files including those with sorries.
# Files with sorries compile to .olean with warnings.
```

## Adding new files

Edit `src/lean/YangMills.lean` to import new modules, or add new files to
the `src/lean/YangMills/` directory.
