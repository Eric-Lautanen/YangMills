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
| `transferMatrixPositivity_axiom` | `ReflectionPositivity.lean` (**confirmed** — not a `sorry`, and not in `TransferMatrix.lean` despite `Overview.lean` implying otherwise) | Positivity of `∫ G(U)·G(θU) dμ₀` for the periodic-lattice transfer matrix | Docstring gives a real justification chain (plaquette PD ⇒ transfer matrix positive ⇒ integral nonnegative). Both abstract sub-steps are now proved: `PositiveDefinite.integral` (integrate out interior links ⟹ PD kernel) and `PositiveDefinite.integralOperator_nonneg` (PD kernel ⟹ positive integral operator), both in `PositiveDefiniteIntegral.lean` with 0 sorries / 0 custom axioms. The **remaining** work is the concrete wiring, but there is a **key obstruction**: the TM kernel `(Tψ)(u) = ∫ ψ(θ⁻⁰(U⁻,u⁰))·exp(-β·(...)) dμ⁻(U⁻)` is NOT of the form `φ(u⁻¹·v)` for a PD function `φ` on a group — the reflection map `θ⁻⁰` is a geometric operation, not group multiplication. While `PosInterfaceConfig` is a product of SU(N)'s (hence a group), the kernel does not factor through the group structure. Closing the axiom requires either (a) a more general PD kernel theory (Mercer-type), (b) showing the TM kernel reduces to the group-theoretic form, or (c) applying the Peter–Weyl character expansion directly to the TM kernel. This is a fundamental mathematical gap, not just formalization work. |
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
integral is nonnegative. Both abstract sub-steps are now proved:

1. `PositiveDefinite.integral` — an integral average of PD functions is PD
   (closes "integrate out interior links ⟹ PD kernel").
2. `PositiveDefinite.integralOperator_nonneg` — a PD kernel on a compact
   group defines a positive integral operator
   (`∫∫ f(x)·conj(f(y))·K(x⁻¹y) dμ dμ ≥ 0`; closes "PD kernel ⟹ positive
   operator").  The proof approximates the integral by Riemann sums and
   controls the error via uniform continuity on `G × G`.

Both are in `PositiveDefiniteIntegral.lean` with 0 sorries and 0 custom axioms.
The **remaining** work is the concrete *wiring*: showing that the
transfer-matrix kernel (a product of plaquette Boltzmann factors, integrated
over negative-time links) is a PD function of the interface link variables —
applying `PositiveDefinite.integral` to the plaquette factors (themselves PD by
`plaquetteBoltzmannPD`, modulo the Peter–Weyl axiom) — and then applying
`integralOperator_nonneg` to the resulting PD kernel.  That wiring is a
substantial measure-theoretic construction not yet undertaken.  Closing it, even
leaving `peterWeyl_clebschGordan_plaquette` as an axiom, would be a genuine
reduction in the codebase's assumption count (five axioms → four).

**Progress.** Two lemmas in `PositiveDefiniteIntegral.lean` are now proved
(0 sorries, 0 custom axioms):

1. `PositiveDefinite.integral` — an integral average of positive-definite
   functions is positive-definite (the continuous analogue of
   `PositiveDefinite.sum`).  This closes the "integrate out interior links ⟹
   the resulting kernel is PD" sub-step.
2. `PositiveDefinite.integralOperator_nonneg` — a positive-definite kernel `K`
   on a compact group `G` defines a *positive integral operator*:
   `∫∫ f(x)·conj(f(y))·K(x⁻¹y) dμ(x) dμ(y) ≥ 0` for a probability measure `μ`.
   The proof approximates the integral by Riemann sums (each non-negative by
   `PositiveDefinite.sum_nonneg_of_map`) and controls the error via uniform
   continuity on the compact space `G × G`.  This closes the "PD kernel ⟹
   positive integral operator" sub-step.

Both abstract sub-steps of the transfer-matrix positivity chain are now
proved.  The **remaining** work to turn `transferMatrixPositivity_axiom` into a
theorem is the *wiring*: showing that the concrete transfer-matrix kernel is a
positive-definite kernel on the interface link variables.  **Key obstruction**:
the transfer matrix kernel `(Tψ)(u) = ∫ ψ(θ⁻⁰(U⁻,u⁰))·exp(-β·(...)) dμ⁻(U⁻)` is
NOT of the form `φ(u⁻¹·v)` for a PD function `φ` on a group — the reflection
map `θ⁻⁰` is a geometric operation, not group multiplication.  While
`PosInterfaceConfig` is a product of SU(N)'s (hence a group), the kernel does
not factor through the group structure.  Closing the axiom requires either (a) a
more general PD kernel theory (Mercer-type), (b) showing the TM kernel reduces
to the group-theoretic form, or (c) applying the Peter–Weyl character expansion
directly to the TM kernel.  This is a fundamental mathematical gap, not just
formalization work.  Closing it, even leaving `peterWeyl_clebschGordan_plaquette`
as an axiom, would be a genuine reduction in the codebase's assumption count
(five axioms → four).

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
   bookkeeping around it — including `integral_G_thetaG_eq_inner_g_Tg` and
   `measure_factorization'` — is fully proved; the axiom is the only gap.
   Its docstring gives a real proof sketch (plaquette positive-definiteness
   ⟹ transfer matrix positive) that looks achievable from existing
   `PositiveDefinite.lean` infrastructure — see the suggested next step in
   the axiom table above.

3. **Systematic audit for vacuous proofs not yet done.** The `hadd` pattern
   (item 1) is a known instance of a broader risk: any proof that goes
   through via deriving a false/unsatisfiable hypothesis rather than
   proving the stated claim. A full pass checking every top-level theorem
   (e.g. via `#print axioms` plus manual inspection for
   contradiction-derivation patterns) has not yet been completed.

4. **Repo hygiene.** `Coq/` and `Z3/` directories are empty placeholders
   despite being listed as backends. `TransferMatrix.lean` has unusual
   whitespace suggesting post-processing artifacts. `Proofs/attempts.jsonl`
   appears to be raw AI proof-attempt logs and should be reviewed for
   whether it belongs in the repo. `TransferMatrix_FIXED.lean.lf` and
   `TransferMatrix.lean.lf` look like stale intermediate versions and
   should be removed or archived if superseded.

5. **`Overview.lean` was stale (fixed this session).** It previously undersold:
   it claimed `integral_G_thetaG_eq_inner_g_Tg` "is not yet formalized" (false —
   it's proved, verified by `#print axioms`) and referenced a
   `transferMatrixCorrect_positive` lemma "currently sorry" that does not exist
   under that name (the real gap is the differently-named
   `transferMatrixPositivity_axiom` axiom, in `ReflectionPositivity.lean`).
   Both documents are now updated to match the source as of this session; the
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
│   │           ├── ReflectionPositivity.lean   # nonempty case vacuous, see known issues
│   │           ├── TransferMatrix.lean         # builds cleanly under v4.33
│   │           ├── PositiveDefinite.lean
│   │           └── PositiveDefiniteIntegral.lean  # PositiveDefinite.integral (new)
│   ├── coq/                             # empty placeholder
│   └── z3/                              # empty placeholder
├── verify/
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
`Overview.lean` currently does the opposite, reporting a fully-proved
lemma (`integral_G_thetaG_eq_inner_g_Tg`) as unformalized and referencing a
`sorry`'d lemma by a name that doesn't match anything in the actual
codebase. Treat both documents as equally prone to drift and equally in
need of upkeep:

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

## References

See `literature/survey.md` and `docs/strategy.md`.

## License

Academic use. No warranty.