# Yang-Mills Millennium Prize — Lean 4 Formalization

A Lean 4 formalization effort around the mathematical foundations of quantum
Yang-Mills theory, undertaken with the long-term goal of a formally verified
proof of the Yang-Mills existence and mass gap conjecture (Clay Millennium
Prize Problem).

**Status: the Millennium Prize theorem is NOT proved.** The top-level
statement depends on axioms that encode the open problems
(`continuum_limit_exists`, `mass_gap_axiom`). Any derivation from those axioms
is circular. See `GOALS.md` for the high-level summary and `docs/STATUS.md`
for the detailed proof-state tracking.

---

## Documentation

| Document | Content |
|---|---|
| `GOALS.md` | Project goals and honest current status (start here) |
| `docs/STATUS.md` | Detailed proof-state tracking: axiom table, what's proved, what's incomplete |
| `docs/path_forward.md` | Path forward to close `transferMatrixPositivity_axiom` (6→5 axioms) |
| `docs/honest_frontier_audit.md` | Honest audit: has "6 → 5" actually reduced anything? What would it take to attack the open axioms? |
| `docs/axiom_growth_audit.md` | Chronological reconstruction of every strengthening of `peterWeyl_clebschGordan_plaquette` |
| `docs/transfer_matrix_positivity_design.md` | Design doc for the Lüscher decomposition plan to close `transferMatrixPositivity_axiom` |
| `docs/mathlib_candidates.md` | Running list of possibly-novel / submittable contributions |
| `MATHLIB_SUBMISSION.md` | Packaging of Mathlib candidates for upstream review |
| `docs/gap_analysis.md` | Analysis of obstructions to closing the transfer-matrix positivity axiom |
| `docs/strategy.md` | Overall strategy |
| `docs/plan.md` | High-level project plan |
| `literature/survey.md` | Literature survey |
| `docs/archive/` | Historical/resolved documents (hadd issue, periodic BC plan, found issues, old setup) |

---

## Building

```bash
curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh
cd YangMills
lake build
```

To check what a given theorem actually depends on:

```
#print axioms YourTheoremName
```

Run this on every top-level theorem before describing it as proved.

The standalone Mathlib candidate files (in `mathlib_candidates/`) are not
part of the main `lake build` target. To verify them individually:

```
lake env lean mathlib_candidates/PositiveDefiniteKernelMathlibCandidate.lean
lake env lean mathlib_candidates/PositiveDefiniteMathlibCandidate.lean
```

Both exit 0 with `#print axioms` showing only `propext, Classical.choice,
Quot.sound` (0 `sorry`, 0 custom axiom).

---

## Project structure

```
YangMills/
├── src/lean/
│   ├── YangMills.lean
│   └── YangMills/
│       ├── Overview.lean
│       ├── SpecialUnitary.lean
│       ├── OSAxioms.lean          # os_reconstruction_theorem axiom
│       ├── GaugeTheory.lean
│       ├── Lattice.lean
│       ├── MassGap.lean           # mass_gap_axiom (the conjecture itself)
│       ├── ContinuumLimit.lean    # continuum_limit_exists axiom
│       ├── MassGapProof.lean      # invokes mass_gap_axiom — circular
│       └── Proofs/
│           ├── BasicLemmas.lean
│           ├── GaugeInvariance.lean
│           ├── JacobiIdentity.lean
│           ├── LatticeMeasure.lean
│           ├── PeterWeyl.lean             # re-export → PeterWeyl/ (7 sub-files)
│           ├── PeterWeyl/                 # Peter–Weyl axiom, plaquetteBoltzmannPD
│           ├── PositiveDefinite.lean      # re-export → PositiveDefinite/ (7 sub-files)
│           ├── PositiveDefinite/          # PD function algebra, Schur orthogonality axiom
│           ├── PositiveDefiniteIntegral.lean  # re-export → PositiveDefiniteIntegral/ (4 sub-files)
│           ├── PositiveDefiniteIntegral/  # PD.integral, integralOperator_nonneg, Mercer-PD
│           ├── BoltzmannFactor.lean       # boltzmannFactorPD, fullBoltzmannPD
│           ├── ReflectionPositivity.lean  # re-export → ReflectionPositivity/ (7 sub-files)
│           ├── ReflectionPositivity/      # transferMatrixPositivity_axiom, osG_thetaG_factorization
│           ├── TransferMatrix.lean        # re-export → TransferMatrix/ (10 sub-files)
│           ├── TransferMatrix/            # transferMatrixCorrect, integral_G_thetaG_eq_inner_g_Tg
│           └── MassGapProof.lean
├── mathlib_candidates/             # standalone Mathlib candidate files
├── docs/                          # working documents (status, audits, design)
├── literature/                     # survey
├── proofs/                         # attempts.jsonl — raw AI proof-attempt log, not part of build
├── verify/                         # verification scripts
├── lakefile.lean
├── lean-toolchain
├── GOALS.md
├── MATHLIB_SUBMISSION.md
└── README.md
```

---

## Key design decisions

- Euclidean formulation via Osterwalder–Schrader axioms rather than
  Minkowski Wightman axioms directly, to use reflection positivity and
  stochastic methods.
- Lattice discretization as a bridge between finite approximations and
  continuum QFT (Wilson's lattice gauge theory).
- Four-corner plaquette classification for the Wilson action decomposition,
  to make the reflection symmetry identities hold.
- `SU(N)` for general N ≥ 2 via Mathlib's `Matrix.specialUnitaryGroup`.

## License

Academic use. No warranty.
