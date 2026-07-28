# Yang-Mills Millennium Prize — Lean 4 Formalization

A Lean 4 formalization effort around the mathematical foundations of quantum
Yang-Mills theory, undertaken with the long-term goal of a formally verified
proof of the Yang-Mills existence and mass gap conjecture (Clay Millennium
Prize Problem).

**Status as of this update: the Millennium Prize theorem is NOT proved.**
The top-level statement currently depends on an axiom
(`mass_gap_axiom`) that is logically equivalent to the conjecture itself.
Any derivation from that axiom is circular and should not be read as
progress on the open problem. See "Status of the Millennium Prize Theorem"
below before reading anything else in this document.

> **Maintenance note:** this README must be kept in sync with the actual
> Lean source on every session that touches the proof state (new lemmas,
> new axioms, new sorries, sorries closed, axioms removed). Do not let
> claims here drift ahead of — or behind — what `lake build` and
> `#print axioms` actually report. See "Keeping this README honest" at the
> bottom.

---

## Status of the Millennium Prize Theorem

**Not proved.** The formalization currently rests on **five** axioms (not
four — `MassGapProof.lean`'s module docstring says "four axioms" and then
lists five; that docstring needs fixing too), one of which (`mass_gap_axiom`)
directly encodes the conjecture being proved. Any theorem chain that
terminates in this axiom is not a proof of anything new — it is a
restatement.

| Axiom | Declared in | What it stands in for | Status / concern |
|---|---|---|---|
| `peterWeyl_clebschGordan_plaquette` | `PeterWeyl.lean` | Peter–Weyl theorem + Clebsch–Gordan decomposition for the plaquette Boltzmann factor | Neither is in Mathlib. Defensible as a cited external theorem *if* correctly applied — needs audit. |
| `transferMatrixPositivity_axiom` | `ReflectionPositivity.lean` (**confirmed** — not a `sorry`, and not in `TransferMatrix.lean` despite `Overview.lean` implying otherwise) | Positivity of `∫ G(U)·G(θU) dμ₀` for the periodic-lattice transfer matrix | Docstring gives a real justification chain (plaquette PD ⇒ transfer matrix positive ⇒ integral nonnegative). All abstract sub-steps are now proved (see "Suggested next step" below). The clean factorization `osG_thetaG_factorization` (0 sorries, 0 axioms) shows the axiom is equivalent to `∫ f(U)·f(θU)·exp(-β S_W(U)) dμ ≥ 0`. The full Boltzmann factor `exp(-β S_W)` is proved PD on the full link group by `boltzmannFactorPD` (modulo Peter–Weyl). **Key obstruction**: this integral is NOT the standard PD quadratic form `∫∫ f(g)·conj(f(h))·K(g⁻¹h) dμ dμ ≥ 0` (which follows from PD-ness of `K` and is proved as `integralOperator_nonneg`). It is a *single* integral `∫ f(g)·f(θg)·K(g) dμ` with the geometric reflection `θ` and `K` evaluated at `g` (not `g⁻¹h`). PD-ness of `K` does not imply this is non-negative; the Peter–Weyl character expansion of `K` and character orthogonality are needed to decompose the integrand into `|Fourier coefficients|²`. This is a fundamental mathematical gap, not just formalization work. |
| `os_reconstruction_theorem` | `OSAxioms.lean` | Osterwalder–Schrader reconstruction (OS axioms ⇒ Wightman QFT) | Established published math, not in Mathlib. Only sound to invoke on objects that actually satisfy the OS axioms — depends on the continuum limit existing (see next row). |
| `continuum_limit_exists` | `ContinuumLimit.lean` | Existence of the lattice a→0 continuum limit (Balaban RG / stochastic quantization) | **This axiom *is* the open mathematical core of the problem.** Not a placeholder for something routine — it's the thing nobody has proved. |
| `mass_gap_axiom` | `MassGap.lean` | Positivity of the continuum mass gap | **This is the conjecture itself.** `yang_mills_existence_and_mass_gap` in `MassGapProof.lean` pulls the gap and its positivity directly from this axiom (`let mg := mass_gap_axiom a ha`) without deriving anything from the lattice work — the clearest concrete illustration of the circularity in the codebase. Must not be used in any theorem claimed as a "proof" of the Millennium Prize result. |

Any file, comment, or summary claiming the top-level theorem is "proved"
while it depends on `mass_gap_axiom` is wrong and should be corrected.

### Suggested next step: wire the abstract lemmas into the lattice setup to close `transferMatrixPositivity_axiom`

Unlike the other four axioms, this one looks achievable with what's already
built. Its docstring lays out the chain: the plaquette Boltzmann factor is
positive-definite (`plaquetteBoltzmannPD`, proved modulo the Peter–Weyl
axiom) ⟹ the transfer matrix built from it is a positive operator ⟹ the
integral is nonnegative. All abstract sub-steps are now proved:

1. `PositiveDefinite.integral` — an integral average of PD functions is PD
   (closes "integrate out interior links ⟹ PD kernel").
2. `PositiveDefinite.integralOperator_nonneg` — a PD kernel on a compact
   group defines a positive integral operator
   (`∫∫ f(x)·conj(f(y))·K(x⁻¹y) dμ dμ ≥ 0`; closes "PD kernel ⟹ positive
   operator").  The proof approximates the integral by Riemann sums and
   controls the error via uniform continuity on `G × G`.
3. `PositiveDefiniteKernel.integralOperator_nonneg` — the **Mercer-type**
   generalization: a continuous Mercer-PD kernel on a compact space (no group
   structure needed) defines a positive integral operator.  This removes the
   group-structure requirement that obstructs the group-theoretic version.
4. `boltzmannFactorPD` (`BoltzmannFactor.lean`) — the **full Boltzmann factor**
   `exp(-β S_W) = ∏ exp(-S_p)` is PD on the full link-variable group, via
   `plaquetteContributionPD` (each plaquette factor PD by `comp_hom` from
   `plaquetteBoltzmannPD_inv`) and `PositiveDefinite.finprod` (n-ary Schur
   product).  0 sorries, 0 axioms beyond Peter–Weyl.
5. `osG_thetaG_factorization` (`ReflectionPositivity.lean`) — the clean
   algebraic identity `osG(U)·osG(θU) = f(U)·f(θU)·exp(-β S_W(U))`, showing
   the axiom is equivalent to `∫ f(U)·f(θU)·exp(-β S_W) dμ ≥ 0`.  0 sorries,
   0 axioms.

All are 0 sorries, 0 custom axioms (only Peter–Weyl for the plaquette PD).
The **remaining** work is the fundamental mathematical gap: the integral
`∫ f(U)·f(θU)·exp(-β S_W) dμ` is NOT the standard PD quadratic form
`∫∫ f(g)·conj(f(h))·K(g⁻¹h) dμ dμ ≥ 0` — it is a single integral with the
geometric reflection `θ` and `K` evaluated at `g` (not `g⁻¹h`).  PD-ness of
`K` does not imply this is non-negative; the Peter–Weyl character expansion
of `K` and character orthogonality are needed to decompose the integrand
into `|Fourier coefficients|²`.  Closing it, even leaving
`peterWeyl_clebschGordan_plaquette` as an axiom, would be a genuine reduction
in the codebase's assumption count (five axioms → four).

## What is actually proved (no sorry, no axiom)

### SU(N) and general algebra
- `CompactSpace (SU N)`, `SecondCountableTopology (SU N)`
- `trace_commutator_zero`, `trace_mul_rotate`, `trace_unitary_conj_invariant`,
  `trace_sq_invariant`, `jacobi_identity`
- `adjointAction_preserves_trace_sq`, `adjointAction_preserves_skewHermitian`,
  `adjointAction_preserves_traceless`
- `lagrangian_gauge_invariant`

### Positive-definite function algebra
- `PositiveDefinite.add`, `.smul_nonneg`, `.conj_inv`, `.zero`, `.one`
- `PositiveDefinite.mul` (Schur product theorem / Hadamard product of PSD
  matrices)
- `PositiveDefinite.pow`, `.tendsto`, `.prod`, `.sum`, `.sum'`
- `repCharacter_positiveDefinite`, `fundamentalCharacter_positiveDefinite`,
  `reTrace_positiveDefinite`
- `exp_reTrace_positiveDefinite` (single-link Boltzmann factor; proved
  unconditionally via the power-series / `PositiveDefinite.tendsto` argument —
  no axiom)
- `plaquetteBoltzmannPD` (depends on the `peterWeyl_clebschGordan_plaquette`
  axiom above — flagged, not unconditional)
- `plaquetteBoltzmannPD_inv` (`PeterWeyl.lean`) — the plaquette Boltzmann
  factor with inverse links `exp(c·Re Tr(g₁ g₂ g₃⁻¹ g₄⁻¹))` is PD on
  `SU(N)⁴` (the version needed for the actual lattice plaquette product;
  depends on the Peter–Weyl axiom)
- `boltzmannFactorPD` (`BoltzmannFactor.lean`) — the **full Boltzmann factor**
  `exp(-β S_W) = ∏ exp(-S_p)` is PD on the full link-variable group
  `LinkVariable (SU N) Λ`, via `plaquetteContributionPD` (each plaquette
  factor PD by `comp_hom` from `plaquetteBoltzmannPD_inv`) and
  `PositiveDefinite.finprod` (n-ary Schur product).  0 sorries, 0 axioms
  beyond Peter–Weyl.
- `osG_thetaG_factorization` (`ReflectionPositivity.lean`) — the clean
  algebraic identity `osG(U)·osG(θU) = f(U)·f(θU)·exp(-β S_W(U))`, showing
  `transferMatrixPositivity_axiom` is equivalent to
  `∫ f(U)·f(θU)·exp(-β S_W) dμ ≥ 0`.  0 sorries, 0 axioms.
- `PositiveDefinite.integral` (`PositiveDefiniteIntegral.lean`) — the
  *continuous* analogue of `PositiveDefinite.sum`: an integral average of
  positive-definite functions is positive-definite.  Verified by
  `#print axioms` to depend on no custom axiom (only `propext`,
  `Classical.choice`, `Quot.sound`), 0 sorries.  This closes the "integrate out
  interior links ⟹ the resulting kernel is PD" step of the transfer-matrix
  positivity argument.
- `PositiveDefinite.integralOperator_nonneg` (`PositiveDefiniteIntegral.lean`)
  — for a compact group `G` with probability measure `μ`, a continuous PD
  function `φ`, and a continuous `f`, `∫∫ f(x)·conj(f(y))·φ(x⁻¹y) dμ dμ ≥ 0`.
  The proof approximates the integral by Riemann sums (each non-negative by
  `PositiveDefinite.sum_nonneg_of_map`) and controls the error via uniform
  continuity on `G × G`.  Verified by `#print axioms` to depend on no custom
  axiom, 0 sorries.  This closes the "PD kernel ⟹ positive integral operator"
  step.  Together with `PositiveDefinite.integral`, both abstract sub-steps of
  the transfer-matrix positivity chain are now proved; the remaining work is
  the concrete wiring into the lattice-gauge-theory setup.
- `PositiveDefiniteKernel` (`PositiveDefiniteIntegral.lean`) — Mercer-type
  PD kernel (no group structure needed): `K : X → X → ℂ` with
  `∑ c_i ·conj(c_j)·K(x_i, x_j) ≥ 0` for every finite set and coefficients.
  Building blocks (all 0 sorries, 0 axioms): `PositiveDefiniteKernel.conj_symm`
  (Hermitian symmetry), `.one` (constant-one kernel), `.mul` (Schur/Hadamard
  product theorem), `.smul_nonneg`, `.finprod` (n-ary Schur product), `.comp`
  (PD preserved by composition with `f : X → Y`), `.continuous_comp`
  (continuity preserved by composition), `.sum_nonneg_of_map` (non-injective
  index map), and `PositiveDefinite.toPositiveDefiniteKernel` (group-PD →
  Mercer-PD).
- `PositiveDefiniteKernel.integralOperator_nonneg`
  (`PositiveDefiniteIntegral.lean`) — the Mercer-type generalization: a
  continuous Mercer-PD kernel on a compact space (no group structure needed)
  defines a positive integral operator
  `∫∫ f(x)·conj(f(y))·K(x, y) dμ dμ ≥ 0`.  0 sorries, 0 custom axioms.

**Two independent verification checks were performed on both lemmas:**
1. **`#print axioms`** — confirms no hidden axiom or `sorry` in the dependency
   tree (only `propext`, `Classical.choice`, `Quot.sound`).  This catches
   *undeclared assumptions* but would not catch a subtly wrong-but-compiling
   argument.
2. **Independent code review** — the full proof scripts (lines 78–153 for
   `integral`, lines 172–378 for `integralOperator_nonneg`) were read
   line-by-line and checked for logical soundness: the Fubini swap, the
   a.e.-non-negativity of the PD quadratic-form integrand, the Riemann-sum
   construction, the uniform-continuity error bound, and the final
   `Complex.nonneg_iff` split.  This confirms the *logic* is sound, not just
   that the kernel accepted it.

These are complementary: a clean `#print axioms` alone would not have caught
a wrong-but-still-compiling argument, and a code review alone would not have
caught a silently-introduced axiom.  Both were done.

**Mathlib-absence verification.** Both `PositiveDefinite.integral` and
`PositiveDefinite.integralOperator_nonneg` were checked against the current
Mathlib version (pinned in `lake-manifest.json`) and confirmed **absent** via
multiple independent search angles:

- `PositiveDefinite` as a bare identifier does not exist anywhere in Mathlib
  (the matrix/quadratic-form positive-definiteness machinery Mathlib does have
  — `Matrix.PosDef`, `PosSemidef`, etc. — never touches Haar measure anywhere
  in the codebase; `grep` for the intersection returns zero files).
- Loogle search `IsCompact _ -> _ -> 0 ≤ _` over all 126 declarations
  mentioning both `IsCompact` and `LE.le` returns **no matches** — a genuine
  negative from the search index, not a grep miss.
- Loogle search `0 ≤ ∫ _, _ ∂_` returns 13 hits, every one of which is
  generic integral-nonnegativity from a pointwise-nonnegative integrand
  (`integral_nonneg`, `setIntegral_nonneg`, AE-equality lemmas).  Nothing
  group-theoretic, nothing kernel-based, nothing resembling "PD kernel ⟹
  positive operator."
- Related concepts (Godement's theorem on positive-definite functions,
  Bochner theorem for groups, unitary-representation character machinery,
  convolution on compact groups) are likewise not present under those names.

This is a multi-angle confirmation that these two lemmas are genuinely new to
Mathlib, not a rediscovery of existing infrastructure.  The framing is
therefore "confirmed absent from Mathlib as of this Mathlib version," not
"might be reusable Mathlib-adjacent infrastructure" — a stronger, citable
claim if this work is ever upstreamed.

**Key Mathlib API names verified against pinned version.** The proof of
`integralOperator_nonneg` depends on two non-trivial Mathlib lemmas whose
names were checked against the pinned Mathlib commit
(`3bc2a1801c2416549ba5ba0b3f5728a28b87e7d9`, Lean v4.33) to catch
toolchain-drift breakage proactively:

- `measureReal_prod_prod` — confirmed present in
  `Mathlib/MeasureTheory/Measure/Prod.lean` (as
  `_root_.MeasureTheory.measureReal_prod_prod`).
- `finite_cover_balls_of_compact` — confirmed present in
  `Mathlib/Topology/MetricSpace/Pseudo/Basic.lean` (with alias
  `IsCompact.finite_cover_balls`).

Both names match the current Mathlib; `lake build
YangMills.Proofs.PositiveDefiniteIntegral` succeeds with 0 errors.  This
file is **not** in the toolchain-drift-breakage risk category.

### Lattice action and reflection lemmas
- `reflectSite_involution`, `reflection_involution`
- `total_wilson_action_decomposition_z4` (S_W = S_W⁺ + S_W⁻ + S_W⁰)
- `neg_action_reflection_z4`, `interface_action_reflection_symmetric_z4`,
  `wilsonActionFiniteConfig_reflection_invariant`
- Periodic-site variants: `signedTime_neg`, `plaquette_classification`,
  `total_decomposition_os_periodic`, etc.
- `trace_plaquetteProduct_reflect_ss/_ts/_st/_tt`
- `neg_action_reflection_os_periodic`,
  `interface_action_reflection_symmetric_os_periodic`

### Measure theory
- `productHaarMeasure`, `IsProbabilityMeasure` instance
- `measurable_extendLinkVariable`, `measurable_wilsonActionFiniteConfig`
- `partitionFunctionFinite_pos` — **proved for both empty and nonempty
  sites** (earlier README versions incorrectly listed the nonempty case as
  a sorry — confirmed fixed, this entry corrects that)
- `gibbsExpectation_pos`, `gibbsExpectation_normalization`
- `gibbsExpectation_linear` — **proved, with integrability hypotheses
  added to the interface** (earlier README versions listed this as
  in-progress without hypotheses — confirmed this was resolved by adding
  the hypotheses, not by proving the false unconditional statement)
- `measurable_plaquetteContribution`,
  `measurable_wilsonActionOSPositive/Negative/Interface`
- `measure_factorization'` (μ₀ ≅ μ⁺ × μ⁻ × μ⁰, proved via `MeasurePreserving`)
  — verified by `#print axioms` (only `propext, Classical.choice, Quot.sound`),
  0 sorries, under the current Lean v4.33 toolchain.

### Transfer matrix
- `reflectToPosInterface`, `transferMatrixCorrect`, `G`, `g_posInterface`
  (definitions)
- `G_thetaG_factorization_clean`, `G_thetaG_factorization`
- `osG_thetaG_factorization` (`ReflectionPositivity.lean`) — the clean
  algebraic identity `osG(U)·osG(θU) = f(U)·f(θU)·exp(-β S_W(U))`,
  showing `transferMatrixPositivity_axiom` is equivalent to
  `∫ f(U)·f(θU)·exp(-β S_W) dμ ≥ 0`.  0 sorries, 0 axioms.
- `integral_G_thetaG_eq_inner_g_Tg` — the key identity linking the
  reflected Gibbs expectation to the transfer-matrix inner product;
  verified by `#print axioms` (only `propext, Classical.choice,
  Quot.sound`), 0 sorries, under the current Lean v4.33 toolchain.
- `measurable_G`, `integrand_measurable`, `measurable_reflectLinkVariable`
- `measure_factorization'` in `TransferMatrix.lean` —
  measure-preserving equivalence between the full lattice measure and the
  positive/negative/interface factorization. Verified by `#print axioms`
  (only `propext, Classical.choice, Quot.sound`), 0 sorries, under the
  current Lean v4.33 toolchain.

## Known incomplete / incorrect items

1. **Vacuous proof (`hadd` issue).** `gibbsExpectationZ4_reflection_positive`
   for the nonempty finite-lattice case only goes through because the
   `hadd` hypothesis (closure under forward time translation) forces
   `sites = ∅` on a finite lattice, making the "proof" true by
   contradiction rather than by establishing the actual inequality. **This
   is not a real theorem for any nonempty lattice.** Fix options: switch
   to periodic boundary conditions so `hadd` is satisfiable on a nonempty
   finite lattice, prove the nonempty case directly without `hadd`, or move
   to an infinite lattice. Until fixed, do not cite this lemma as
   establishing reflection positivity for any actual configuration.

2. **Periodic-lattice reflection positivity is unresolved — status now
   confirmed precisely.** `gibbsExpectationPeriodic_reflection_positive`
   closes via `exact transferMatrixPositivity_axiom ...`, a genuine `axiom`
   declared in `ReflectionPositivity.lean` (not a `sorry`, and not in
   `TransferMatrix.lean`). All of the algebraic and measure-theoretic
   bookkeeping around it — including `integral_G_thetaG_eq_inner_g_Tg`,
   `measure_factorization'`, and the clean factorization
   `osG_thetaG_factorization` — is fully proved; the axiom is the only gap.
   The clean factorization shows the axiom is equivalent to
   `∫ f(U)·f(θU)·exp(-β S_W) dμ ≥ 0`, and `boltzmannFactorPD` proves the
   Boltzmann factor `exp(-β S_W)` is PD on the full link group (modulo
   Peter–Weyl).  **However**, this integral is NOT the standard PD quadratic
   form that `integralOperator_nonneg` addresses — it is a single integral
   with the geometric reflection `θ` and `K` evaluated at `g` (not `g⁻¹h`).
   PD-ness of `K` does not imply non-negativity; the Peter–Weyl character
   expansion + orthogonality are needed.  See the suggested next step above.

3. **Systematic audit for vacuous proofs not yet done.** The `hadd` pattern
   (item 1) is a known instance of a broader risk: any proof that goes
   through via deriving a false/unsatisfiable hypothesis rather than
   proving the stated claim. A full pass checking every top-level theorem
   (e.g. via `#print axioms` plus manual inspection for
   contradiction-derivation patterns) has not yet been completed.

4. **Repo hygiene (addressed).** The empty `Coq/` and `Z3/`
   placeholder directories and the stale `TransferMatrix_FIXED.lean.lf` /
   `TransferMatrix.lean.lf` intermediate-version files have been removed
   (they remain recoverable from git history). `TransferMatrix.lean` has
   unusual whitespace suggesting post-processing artifacts.
   `proofs/attempts.jsonl` is raw AI proof-attempt log output and is
   retained as a record of verification attempts; it is not part of the
   build.

5. **`Overview.lean` was stale (fixed).** It previously undersold:
   it claimed `integral_G_thetaG_eq_inner_g_Tg` "is not yet formalized" (false —
   it's proved, verified by `#print axioms`) and referenced a
   `transferMatrixCorrect_positive` lemma "currently sorry" that does not exist
   under that name (the real gap is the differently-named
   `transferMatrixPositivity_axiom` axiom, in `ReflectionPositivity.lean`).
   Both documents are now updated to match the source; the
   same continuous-maintenance discipline applies going forward.

6. **`TransferMatrix.lean` toolchain-drift build break — FIXED.** The
   repo's `lean-toolchain` was `v4.32.0-rc1` but `lake-manifest.json` pins
   a Mathlib commit requiring `v4.33.0-rc1`; `lake build` auto-bumps the
   toolchain and rebuilds.  Several `simp`-based proofs in
   `TransferMatrix.lean` (subtype-coercion goals in `measure_factorization'`
   and the bijectivity/equiv lemmas) no longer closed under the new `simp`
   normal form.  This was **toolchain drift**, not a logical error.  All
   break sites have been fixed this session; `TransferMatrix.lean` now
   builds cleanly under v4.33, and `#print axioms` on
   `measure_factorization'` and `integral_G_thetaG_eq_inner_g_Tg` confirms
   they depend only on `propext, Classical.choice, Quot.sound` (no custom
   axiom, 0 sorries).  The full `lake build` succeeds.

## Project structure

```
YangMills/
├── src/
│   ├── lean/
│   │   ├── YangMills.lean
│   │   └── YangMills/
│   │       ├── Overview.lean
│   │       ├── SpecialUnitary.lean
│   │       ├── OSAxioms.lean
│   │       ├── GaugeTheory.lean
│   │       ├── Lattice.lean
│   │       ├── MassGap.lean
│   │       ├── ContinuumLimit.lean      # invokes continuum_limit_exists
│   │       ├── MassGapProof.lean        # invokes mass_gap_axiom — see status warning above
│   │       └── Proofs/
│   │           ├── BasicLemmas.lean
│   │           ├── GaugeInvariance.lean
│   │           ├── JacobiIdentity.lean
│   │           ├── LatticeMeasure.lean
│   │           ├── PeterWeyl.lean               # Peter–Weyl axiom, plaquetteBoltzmannPD(_inv)
│   │           ├── PositiveDefinite.lean       # PD function algebra (add, mul, prod, finprod, …)
│   │           ├── PositiveDefiniteIntegral.lean  # PD.integral, integralOperator_nonneg, Mercer-PD kernels
│   │           ├── BoltzmannFactor.lean        # boltzmannFactorPD (full Boltzmann factor is PD)
│   │           ├── ReflectionPositivity.lean   # transferMatrixPositivity_axiom, osG_thetaG_factorization
│   │           ├── TransferMatrix.lean         # transferMatrixCorrect, integral_G_thetaG_eq_inner_g_Tg
│   │           └── MassGapProof.lean
├── proofs/                             # attempts.jsonl — raw AI proof-attempt log, not part of build
├── verify/                             # verification scripts (lean.bat, coq.bat, z3.bat, …)
├── docs/
├── literature/
├── lakefile.lean
├── lean-toolchain
└── README.md
```

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

## Key design decisions

- Euclidean formulation via Osterwalder–Schrader axioms rather than
  Minkowski Wightman axioms directly, to use reflection positivity and
  stochastic methods.
- Lattice discretization as a bridge between finite approximations and
  continuum QFT (Wilson's lattice gauge theory).
- Four-corner plaquette classification for the Wilson action decomposition,
  to make the reflection symmetry identities hold.
- `SU(N)` for general N ≥ 2 via Mathlib's `Matrix.specialUnitaryGroup`.

## Keeping this README (and `Overview.lean`) honest

Documentation drift in this project is not a one-time bug, it's a recurring
pattern, and it goes in **both directions**: this README has previously
reported sorries as open that had been closed, and reported lemmas as
complete without noting the axioms they secretly depended on;
`Overview.lean` previously reported a fully-proved
lemma (`integral_G_thetaG_eq_inner_g_Tg`) as unformalized and referenced a
`sorry`'d lemma by a name that doesn't match anything in the actual
codebase (both now fixed). Treat both documents as equally prone to drift
and equally in need of upkeep:

- Every session that changes proof state must update the "What is actually
  proved" / "Known incomplete" sections of this README **and** the
  corresponding status notes in `Overview.lean`, in the same session, not
  later.
- Never describe a theorem as proved without having run
  `#print axioms` on it in that session.
- Never describe the top-level Millennium Prize theorem as proved, nearly
  proved, or as making progress, while `mass_gap_axiom` (or anything
  equivalent to the conjecture) remains in its dependency tree.
- When a module docstring (e.g. `MassGapProof.lean`'s "the proof uses four
  axioms") states a count or fact about the codebase, verify that count
  against the actual source in the same session — the axiom count there is
  currently wrong (says four, lists five).
- If a claim in this README or `Overview.lean` can't be verified against
  current source in under a few minutes, mark it `[UNVERIFIED — recheck]`
  rather than leaving a confident-sounding but possibly stale statement in
  place.

## Mathlib candidate packaging

Three general-purpose results (Mercer-type positive-definite kernels and two
group-theoretic PD lemmas) have been extracted into standalone,
Yang-Mills-free files for independent review by Mathlib maintainers. They
are pure group/measure/kernel theory, verified by `#print axioms` to depend
only on `propext`, `Classical.choice`, `Quot.sound` (0 `sorry`, 0 custom
axiom). See **`MATHLIB_SUBMISSION.md`** at the repo root for the full
summary, absence-verification report, and reproduction steps. The standalone
files are:

- `PositiveDefiniteKernelMathlibCandidate.lean` (repo root) — **priority
  candidate**: Mercer-type PD kernels (no group structure), including
  `PositiveDefiniteKernel.integralOperator_nonneg` and the full building-block
  suite (`.conj_symm`, `.one`, `.mul`, `.smul_nonneg`, `.finprod`, `.comp`,
  `.continuous_comp`, `.sum_nonneg_of_map`, `toPositiveDefiniteKernel`).
- `PositiveDefiniteMathlibCandidate.lean` (repo root) — group-theoretic PD
  functions: `PositiveDefinite.integral` and
  `PositiveDefinite.integralOperator_nonneg`.

These results are unrelated to the (unsolved) Yang-Mills mass-gap difficulty
and are offered as standalone infrastructure.

## References

See `literature/survey.md` and `docs/strategy.md`.

## License

Academic use. No warranty.