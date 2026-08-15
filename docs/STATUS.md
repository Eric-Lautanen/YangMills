# Detailed Proof Status

This document holds the detailed proof-state tracking that previously lived
in `README.md`. It is the working reference for what is proved, what each
axiom stands in for, and what remains. The `README.md` is kept short and
points here.

**Status as of this update: the Millennium Prize theorem is NOT proved.**
The top-level statement depends on axioms that encode the open problems.
See `GOALS.md` for the high-level summary and `docs/honest_frontier_audit.md`
for the full frontier audit.

---

## Axiom table

The formalization rests on **six** axioms:

| Axiom | Declared in | What it stands in for | Status / concern |
|---|---|---|---|
| `peterWeyl_clebschGordan_plaquette` | `PeterWeyl/Axiom.lean` | Peter–Weyl theorem + Clebsch–Gordan decomposition for the plaquette Boltzmann factor **and** for products of characters of the same group element (across-plaquette CG) **and** dual (contragredient) representations **and** L² completeness (Peter–Weyl basis) **and** matrix-element Clebsch–Gordan coefficients (unitary change-of-basis for `ρ_s ⊗ ρ_t → ⊕_ν ρ_ν`) | Not in Mathlib. Defensible as cited external theorems *if* correctly applied. **Strengthened seven times** — see `docs/axiom_growth_audit.md` for the full audit. Four strengthenings (char-level CG, L² completeness, matrix-element CG, Schur for `Λ` + CG for `ι×Λ`) directly followed a session that concluded the target could NOT be closed with current axioms. |
| `transferMatrixPositivity_axiom` | `ReflectionPositivity/GaugeInvariance.lean` | Positivity of `∫ G(U)·G(θU) dμ₀` for the periodic-lattice transfer matrix | The closeable axiom. The Lüscher decomposition `T = V^{1/2}·U·V^{1/2}` is in progress (sub-steps 1–2 done, 3–6 remaining). Even if closed, the "6 → 5" headline is partially misleading per the axiom-growth audit. |
| `os_reconstruction_theorem` | `OSAxioms.lean` | Osterwalder–Schrader reconstruction (OS axioms ⇒ Wightman QFT) | Established published math, not in Mathlib. Only sound to invoke on objects that actually satisfy the OS axioms — depends on the continuum limit existing. |
| `continuum_limit_exists` | `ContinuumLimit.lean` | Existence of the lattice a→0 continuum limit (Balaban RG / stochastic quantization) | **This axiom *is* the open mathematical core of the problem.** Not a placeholder for something routine — it's the thing nobody has proved. |
| `mass_gap_axiom` | `MassGap.lean` | Positivity of the continuum mass gap | **This is the conjecture itself.** `yang_mills_existence_and_mass_gap` pulls the gap directly from this axiom without deriving anything from the lattice work — circular. Must not be used in any theorem claimed as a "proof." |
| `characterOrthogonality` | `PositiveDefinite/CharacterOrthogonality.lean` | Schur orthogonality of **matrix elements** of irreducible unitary representations of a compact group (Great Orthogonality Theorem) | Not in Mathlib. Defensible as a cited external theorem. The (weaker) character-orthogonality statement is derived as `character_orthogonality_from_schur` (0 sorries). |

### Axiom growth audit

`peterWeyl_clebschGordan_plaquette` has been strengthened **seven times**.
Four of those strengthenings directly followed a session that concluded
`transferMatrixPositivity_axiom` could NOT be closed with the current
axioms. The unfolded-axiom count (if the enriched axiom were split into
separately-named axioms) would be **nine** axioms, **six** of them
substantial theorems. See `docs/axiom_growth_audit.md` for the full
chronological reconstruction and `docs/honest_frontier_audit.md` Part 1 for
the per-strengthening verdict on whether "6 → 5" is honest progress.

---

## The Lüscher decomposition plan (current plan to close `transferMatrixPositivity_axiom`)

The current plan to close the axiom (count 6 → 5) is the **Lüscher
decomposition** `T = V^{1/2}·U·V^{1/2}`: spatial plaquettes → V (PD
multiplication operator via Schur product), temporal plaquettes → U (positive
integral operator via Lüscher cascade + `character_kernel_integral_nonneg`).

The full character expansion fails because it expands ALL plaquettes in
characters, giving `Â_w · Â_{w*}` (product at different weights, NOT
`|Â_w|²`). The Lüscher decomposition succeeds because it separates temporal
and spatial plaquettes and handles them by different mechanisms.

### Progress

- **Sub-step 1 (spatial/temporal partition) — DONE.**
- **Sub-step 2 (`spatialBoltzmannPD`) — DONE.** V positive (spatial Boltzmann
  = product of PD plaquette factors → PD multiplication operator).
- **Sub-step 3 (U positive) — pending.** Temporal plaquette character
  expansion + Lüscher cascade → kernel `Σ a_s χ_s(W·V)` with `a_s ≥ 0` →
  `character_kernel_integral_nonneg`.
- **Sub-step 4 (factorization) — pending.** `T = V^{1/2}·U·V^{1/2}`.
- **Sub-step 5 (`∫g·Tg≥0`) — pending.**
- **Sub-step 6 (conclude `I≥0`) — pending.** Use
  `integral_G_thetaG_eq_inner_g_Tg` to conclude.

**`fullBoltzmannPD`** is proved and build GREEN (session 83, 2026-08-11).
`#print axioms` = `[propext, Classical.choice, Quot.sound,
peterWeyl_clebschGordan_plaquette]` (only 4 — does NOT depend on
`characterOrthogonality` or `transferMatrixPositivity_axiom`).

See `docs/transfer_matrix_positivity_design.md` §8.11.67 for the full design.

---

## What is actually proved (no sorry, no axiom beyond Peter–Weyl)

### SU(N) and general algebra
- `CompactSpace (SU N)`, `SecondCountableTopology (SU N)`
- `trace_commutator_zero`, `trace_mul_rotate`, `trace_unitary_conj_invariant`,
  `trace_sq_invariant`, `jacobi_identity`
- `adjointAction_preserves_trace_sq`, `adjointAction_preserves_skewHermitian`,
  `adjointAction_preserves_traceless`
- `lagrangian_gauge_invariant`

### Positive-definite function algebra
- `PositiveDefinite.add`, `.smul_nonneg`, `.conj_inv`, `.zero`, `.one`
- `PositiveDefinite.mul` (Schur product theorem / Hadamard product of PSD matrices)
- `PositiveDefinite.pow`, `.tendsto`, `.prod`, `.sum`, `.sum'`
- `repCharacter_positiveDefinite`, `fundamentalCharacter_positiveDefinite`,
  `reTrace_positiveDefinite`
- `IsUnitaryRepresentation`, `repCharacter`, `repCharacter_inv`,
  `repCharacter_norm_le_dim`
- `character_orthogonality_from_schur` (derives character orthogonality from
  the Schur orthogonality axiom, 0 sorries)
- `luscher_key_identity` — the single-link identity
  `∫_G χ_γ(g·h)·χ_{γ'}(g⁻¹·k) = δ_{γγ'}·(1/d_γ)·χ_γ(h·k)` (Step 1 of the
  Lüscher roadmap, 0 sorries, depends only on `characterOrthogonality`)
- `exp_reTrace_positiveDefinite` (single-link Boltzmann factor, no axiom)
- `plaquetteBoltzmannPD`, `plaquetteBoltzmannPD_inv` (depend on Peter–Weyl axiom)
- Character product / sum decomposition lemmas (`charProduct_PD`,
  `charProduct_finset_decomp`, `charSum_product_decomp`,
  `charSum_finprod_decomp`, `charProduct_link_separable_decomp`,
  `charProduct_mixed_finset_decomp'`, `charProduct_mixed_link_separable_decomp`)
  — all 0 sorries, 0 custom axioms beyond Peter–Weyl
- `boltzmannFactorPD` — the full Boltzmann factor `exp(-β S_W)` is PD on the
  full link group. 0 sorries, 0 axioms beyond Peter–Weyl.
- `fullBoltzmannPD` — proved and build GREEN (session 83). `#print axioms` =
  `[propext, Classical.choice, Quot.sound, peterWeyl_clebschGordan_plaquette]`.
- `osG_thetaG_factorization` — `osG(U)·osG(θU) = f(U)·f(θU)·exp(-β S_W(U))`.
  0 sorries, 0 axioms.
- `PositiveDefinite.integral` — integral average of PD functions is PD.
  0 sorries, no custom axiom.
- `PositiveDefinite.integralOperator_nonneg` — PD kernel ⟹ positive integral
  operator. 0 sorries, no custom axiom.
- `PositiveDefiniteKernel` (Mercer-type) + building blocks (`.conj_symm`,
  `.one`, `.mul`, `.smul_nonneg`, `.finprod`, `.comp`, `.continuous_comp`,
  `.sum_nonneg_of_map`, `toPositiveDefiniteKernel`) — all 0 sorries, 0 axioms.
- `PositiveDefiniteKernel.integralOperator_nonneg` (Mercer-type) — 0 sorries,
  0 custom axioms.
- `character_expansion_positivity` / `character_expansion_nonneg` — abstract
  character-expansion scaffold. 0 sorries, 0 custom axioms.
- `character_kernel_integral_nonneg` — character-kernel → non-negative
  integral. 0 sorries, does NOT depend on `characterOrthogonality`.
- Lüscher cascade integrals: `luscher_2site_cascade_coeff`,
  `luscher_3site_cascade_coeff` — 0 sorries, depend on
  `characterOrthogonality`.

### Lattice action and reflection lemmas
- `reflectSite_involution`, `reflection_involution`
- `total_wilson_action_decomposition_z4` (S_W = S_W⁺ + S_W⁻ + S_W⁰)
- `neg_action_reflection_z4`, `interface_action_reflection_symmetric_z4`
- Periodic-site variants: `signedTime_neg`, `plaquette_classification`,
  `total_decomposition_os_periodic`, etc.
- `trace_plaquetteProduct_reflect_ss/_ts/_st/_tt`
- `neg_action_reflection_os_periodic`,
  `interface_action_reflection_symmetric_os_periodic`

### Measure theory
- `productHaarMeasure`, `IsProbabilityMeasure` instance
- `measurable_extendLinkVariable`, `measurable_wilsonActionFiniteConfig`
- `partitionFunctionFinite_pos`, `gibbsExpectation_pos`,
  `gibbsExpectation_normalization`, `gibbsExpectation_linear`
- `measure_factorization'` (μ₀ ≅ μ⁺ × μ⁻ × μ⁰) — 0 sorries, standard axioms
- `haarMeasure_inv_invariant` — Haar measure invariant under inversion. 0
  sorries, 0 custom axioms.
- `reflectLinkVariable_measurePreserving` — reflection is measure-preserving.
  0 sorries, 0 custom axioms.
- `reflectLinkVariable_measurePreserving_between` — generalized to differing
  source/target site sets. 0 sorries, 0 custom axioms.

### Transfer matrix
- `reflectToPosInterface`, `transferMatrixCorrect`, `G`, `g_posInterface`
- `reflectPosToNeg`, `reflectNegToPos`, `sigmaInterface`
- `reflectToPosInterface_involution` — 0 sorries, 0 custom axioms
- `reflectPosToNeg_reflectNegToPos` — 0 sorries, 0 custom axioms
- `transferMatrix_integrand_change_of_variables` — pointwise identity. 0
  sorries, 0 custom axioms
- `transferMatrix_change_of_variables` — integral-level change of variables.
  0 sorries, 0 custom axioms. **Completes step (b) of the closure plan.**
- `interface_kernel_character_expansion` — separable character expansion of
  the interface Boltzmann factor. 0 sorries, 0 custom axioms.
- Concrete↔abstract bridge (G1+G2+G3): `plaquetteContribution_exp_decomp`,
  `exp_neg_beta_wilsonActionFinite_eq_prod`, interface plaquette enumeration.
  All 0 sorries, 0 custom axioms.
- `interface_boltzmann_character_expansion` — pointwise identity
  `exp(-β·S_int(U)) = (C : ℂ) · ∑_w (F w : ℂ) · Φ_w(U)·Ψ_w(U)·V_w(U)`. 0
  sorries; uses `peterWeyl_clebschGordan_plaquette`.
- Fubini reduction (steps 4a–4e): `inner_product_complex_eq_product_integral`,
  `transferMatrixReflected_split_exp_real/_complex`,
  `transfer_matrix_fubini_character_expansion`,
  `transfer_matrix_fubini_integrability_self`,
  `transfer_matrix_fubini_integrated_prod`,
  `transfer_matrix_fubini_inner_pull`,
  `transfer_matrix_fubini_integrated_pull`. All 0 sorries, 0 custom axioms.
- Lemma 3 σ-inversion: `fourierCoeffNeg_eq_fourierCoeffPos_fullReflect`,
  `fullReflectReindex`, per-link and product identities. 0 sorries, 0 custom
  axioms.
- `integral_G_thetaG_eq_inner_g_Tg` — key identity linking reflected Gibbs
  expectation to transfer-matrix inner product. 0 sorries, standard axioms.
- `measure_factorization'` in `TransferMatrix/` — 0 sorries, standard
  axioms.

---

## Known incomplete / incorrect items

1. **Vacuous proof (`hadd` issue).** `gibbsExpectationZ4_reflection_positive`
   for the nonempty finite-lattice case only goes through because the `hadd`
   hypothesis forces `sites = ∅` on a finite lattice, making the "proof" true
   by contradiction. **Not a real theorem for any nonempty lattice.** Fix:
   switch to periodic boundary conditions (done for the periodic variant),
   prove directly without `hadd`, or move to infinite lattice.

2. **Periodic-lattice reflection positivity is unresolved.**
   `gibbsExpectationPeriodic_reflection_positive` closes via
   `exact transferMatrixPositivity_axiom ...`, a genuine axiom. All algebraic
   and measure-theoretic bookkeeping around it is fully proved; the axiom is
   the only gap. The Lüscher decomposition (sub-steps 3–6) is in progress.

3. **Systematic audit for vacuous proofs not yet done.** The `hadd` pattern
   is a known instance of a broader risk. A full pass checking every top-level
   theorem has not yet been completed.

---

## Mathlib candidate packaging

Three general-purpose results have been extracted into standalone,
Yang-Mills-free files for independent review by Mathlib maintainers. They
are pure group/measure/kernel theory, verified by `#print axioms` to depend
only on `propext`, `Classical.choice`, `Quot.sound` (0 `sorry`, 0 custom
axiom). See **`MATHLIB_SUBMISSION.md`** for the full summary,
absence-verification report, and reproduction steps.

- `mathlib_candidates/PositiveDefiniteKernelMathlibCandidate.lean` —
  **priority candidate**: Mercer-type PD kernels (no group structure),
  including `PositiveDefiniteKernel.integralOperator_nonneg` and the full
  building-block suite. Definition uses `Matrix.PosSemidef` (suggested by
  Yaël Dillies); the quadratic-form equivalence is proved as
  `quadratic_form_nonneg` / `of_quadratic_form`.
- `mathlib_candidates/PositiveDefiniteMathlibCandidate.lean` — group-PD
  functions: `PositiveDefinite.integral` and
  `PositiveDefinite.integralOperator_nonneg`.

See `docs/mathlib_candidates.md` for the extended running list of all
candidates found along the way (Lüscher cascades, character-kernel
non-negativity, Schur orthogonality as a high-impact target, etc.).

---

## Documentation maintenance rules

- Every session that changes proof state must update this document **and**
  `GOALS.md` in the same session, not later.
- Never describe a theorem as proved without having run `#print axioms` on it
  in that session.
- Never describe the top-level Millennium Prize theorem as proved, nearly
  proved, or as making progress, while `mass_gap_axiom` (or anything
  equivalent to the conjecture) remains in its dependency tree.
- If a claim can't be verified against current source in under a few minutes,
  mark it `[UNVERIFIED — recheck]`.
- **Axiom-strengthening logging rule (permanent).** Any future strengthening
  of an existing axiom must be logged in `docs/axiom_growth_audit.md` with:
  (a) what obstruction it was added to resolve, and (b) a same-session
  classification as (a) narrow textbook fact or (b) substantial theorem.
