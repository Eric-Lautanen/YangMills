/-
# Overview

Project structure, references, and current status for the Yang-Mills
formalization effort.

## Current Status

### Completed:
#### Phase 3: SU(N) & Gauge Theory
- SU(N) defined via Mathlib's `Matrix.specialUnitaryGroup` (SpecialUnitary.lean)
- su(N) Lie algebra as skew-Hermitian traceless matrices (SpecialUnitary.lean)
- CompactSpace (SU N) proved (SpecialUnitary.lean)
- Principal G-bundles, connections, curvature (GaugeTheory.lean)
- Yang-Mills action functional (GaugeTheory.lean)
- Lattice gauge theory foundations (Lattice.lean)
- OS Axioms skeleton (OSAxioms.lean)
- Mass Gap definition (MassGap.lean)

#### Phase 4 — Z4Site combinatorial lemmas:
- **reflectSite_involution**: reflectSite ∘ reflectSite = id
- **plaquette_product_reflection_spatial**: plaquette product reflection for spatial μ,ν
- **trace_plaquette_product_reflection**: trace equality for ALL (μ,ν) cases including time-involving
- **neg_action_reflection_z4**: S_W⁻[U] = S_W⁺[θU] (with hadd hypothesis)
- **interface_action_reflection_symmetric_z4**: S_W⁰[θU] = S_W⁰[U] (with hadd hypothesis)
- **reflectTriple_preserves_interface**: reflection maps interface plaquettes to interface plaquettes
- **total_wilson_action_decomposition_z4**: S_W = S_W⁺ + S_W⁻ + S_W⁰
- **wilsonActionFiniteConfig_reflection_invariant**: S_W[θU] = S_W[U]
- **extend_reflectFiniteConfig_eq**: extending reflected config = reflecting extended config

#### Phase 5 — Measure-theoretic formalization:
- **productHaarMeasure**: product Haar measure on finite lattice via Measure.pi
- **MeasurableSpace on LinkVariable**: via MeasurableSpace.comap on value projection
- **IsProbabilityMeasure**: total volume = 1 (proved)
- **partitionFunctionFinite_pos**: > 0 for any sites (including nonempty)
- **gibbsExpectation_pos**: expectation of non-negative observable is ≥ 0
- **gibbsExpectation_normalization**: ⟨1⟩ = 1
- **gibbsExpectation_linear**: linearity of expectation with integrability hypotheses
- **measurable_extendLinkVariable**: extension map is measurable
- **measurable_wilsonActionFiniteConfig**: Wilson action is measurable (continuous on compact)

#### Phase 6 — Periodic BCs, Osterwalder-Seiler decomposition:
- **PeriodicSite**: finite lattice with ZMod time and spatial coordinates
- **addVectorPeriodic, reflectSitePeriodic**: modular arithmetic for periodic BCs
- **signedTime**: signed lift of ZMod T to ℤ, enabling time-ordered decomposition
- **positiveSites, negativeSites, interfaceSites**: time-slice partitioning
- **wilsonActionOSPositive/Negative/Interface**: OS plaquette-based decomposition
- **plaquette_classification**: every plaquette is positive, negative, or interface
- **total_decomposition_os_periodic**: S_W = S_OS⁺ + S_OS⁻ + S_OS_int
- **reflectPlaquetteIndex_sign**: reflection flips positive ↔ negative plaquettes
- **plaquettePositive/Negative**: predicates for OS classification
- **reflectPlaquetteIndex**: involutive bijection on PlaquetteIndex
- **trace_plaquetteProduct_reflect_all**: unconditional trace equality for all (μ,ν)
- **plaquetteContribution_reflect_eq_all**: unconditional contribution equality
- **neg_action_reflection_os_periodic**: S_OS⁻[U] = S_OS⁺[θU] via Fintype.sum_equiv
- **interface_action_reflection_symmetric_os_periodic**: S_OS_int[θU] = S_OS_int[U]
- **measure_factorization'** (TransferMatrix.lean): μ₀ ≅ μ⁺ × μ⁻ × μ⁰ (measure-preserving)
- **measure_factorization'** (TransferMatrix.lean): μ₀ ≅ μ⁺ × μ⁻ × μ⁰ (measure-preserving)
- **finiteLinkIndexUnionSum, finiteLinkIndexEquiv**: link index isomorphisms
- **restrict_merge_id**: restrictPosInterface ∘ mergeConfigurations = id
- **dependsOnlyOnPosInterface**: predicate for correct reflection positivity hypothesis
- **gibbsExpectationPeriodic_reflection_positive**: all algebraic and
  measure-theoretic steps are proved; the final positivity step closes via
  `transferMatrixPositivity_axiom` (a genuine `axiom` in
  `ReflectionPositivity.lean`, **not** a `sorry` and **not** in
  `TransferMatrix.lean`).  See "Remaining" below.

### Remaining:
1. **`transferMatrixPositivity_axiom`** (`ReflectionPositivity.lean`): the only
   real gap in the periodic-lattice reflection-positivity chain.  Everything
   around it is proved — the action decomposition, the reflection lemmas
   (`neg_action_reflection_os_periodic`, `interface_action_reflection_symmetric_os_periodic`),
   the measure factorization (`measure_factorization'`), and the key identity
   `integral_G_thetaG_eq_inner_g_Tg` (all verified by `#print axioms` to depend
   on no custom axiom, under the current Lean v4.33 toolchain).  The axiom's
   own docstring gives the intended chain: plaquette Boltzmann factor PD
   (`plaquetteBoltzmannPD`, proved modulo the Peter–Weyl axiom) ⟹ transfer
   matrix `T` is a positive operator ⟹ `∫ G·G(θU) dμ₀ ≥ 0`.  The middle step
   is the open one.

2. **New infrastructure — `PositiveDefinite.integral` and
   `PositiveDefinite.integralOperator_nonneg`**
   (`PositiveDefiniteIntegral.lean`): two lemmas, both proved with 0 sorries and
   0 custom axioms (verified by `#print axioms`).
   - `PositiveDefinite.integral` is the *continuous* analogue of
     `PositiveDefinite.sum` — an integral average of positive-definite
     functions is positive-definite.  This closes the "integrate out interior
     links ⟹ the resulting kernel is PD" step.
   - `PositiveDefinite.integralOperator_nonneg` is the "PD kernel ⟹ positive
     integral operator" step: for a compact group `G` with probability measure
     `μ`, a continuous PD function `φ`, and a continuous `f`,
     `∫∫ f(x)·conj(f(y))·φ(x⁻¹y) dμ dμ ≥ 0`.  The proof approximates the
     integral by Riemann sums (each non-negative by
     `PositiveDefinite.sum_nonneg_of_map`) and controls the error via uniform
     continuity on `G × G`.
   Together these close both abstract sub-steps of the transfer-matrix
   positivity chain.  The **Mercer-type** generalization (approach (a)) is also
   built in the same file: `PositiveDefiniteKernel` (Mercer sense, no group
   structure), `PositiveDefiniteKernel.sum_nonneg_of_map`, and
   `PositiveDefiniteKernel.integralOperator_nonneg` (a continuous Mercer-PD
   kernel on a compact space defines a positive integral operator).  Building
   blocks for promoting `plaquetteBoltzmannPD` to the full Boltzmann factor are
   proved in `PositiveDefinite.lean`: `PositiveDefinite.comp_mulEquiv` (PD
   preserved by group isomorphisms), `PositiveDefinite.comp_hom` (PD preserved
   by group homomorphisms), `PositiveDefinite.fst`/`.snd` (extension by
   constants), and `PositiveDefinite.finprod` (n-ary Schur product theorem).
   Additionally, `repCharacter_inv` (χ(g⁻¹) = conj(χ(g))) and
   `plaquetteBoltzmannPD_inv` (the plaquette factor with **inverse links**
   exp(c·Re Tr(g₁g₂g₃⁻¹g₄⁻¹)) is PD on SU(N)⁴) are proved in
   `PositiveDefinite.lean` / `PeterWeyl.lean`, handling the actual lattice
   plaquette product with orientation-reversing inverses.  This single-plaquette
   result is then **promoted to the full link-variable group** in
   `BoltzmannFactor.lean`: `plaquetteProjection` (the homomorphism
   `LinkVariable (SU N) Λ →* SU(N)⁴` extracting the four links around a plaquette,
   with `map_one'`/`map_mul'` by `rfl`), `plaquetteFactorPD` (the plaquette
   Boltzmann factor is PD on the full link group, via `comp_hom`), and
   `plaquetteContributionPD` (the full plaquette contribution `exp(-S_p)` is PD,
    via `smul_nonneg`), and `boltzmannFactorPD` (the **full Boltzmann factor**
    `exp(-S_W) = ∏_{n,μ,ν} exp(-S_p)` is PD on the full link group, via
    `finprod` — the n-ary Schur product theorem).  All 0 sorries, 0 custom
     axioms beyond the Peter–Weyl axiom, full `lake build` clean.
     **Mercer-PD kernel building blocks** are also proved in
     `PositiveDefiniteIntegral.lean`: `PositiveDefiniteKernel.conj_symm`
     (Hermitian symmetry), `PositiveDefiniteKernel.mul` (Schur/Hadamard product
     theorem for Mercer-PD kernels), `PositiveDefiniteKernel.smul_nonneg`
     (non-negative scaling), `PositiveDefiniteKernel.finprod` (n-ary Schur
     product), `PositiveDefiniteKernel.comp` (PD preserved by composition with
     `f : X → Y` on both arguments — the key operation for composing the
     Boltzmann-factor kernel with reflection/projection maps), and
     `PositiveDefiniteKernel.continuous_comp` (continuity preserved by
     composition).  These are the algebraic ingredients for constructing the TM
     kernel as a Mercer-PD kernel from the group-PD `boltzmannFactorPD` via
     `toPositiveDefiniteKernel` → `comp` → `integralOperator_nonneg`.  All 0
     sorries, 0 custom axioms, full `lake build` clean.
    The **remaining** work to turn `transferMatrixPositivity_axiom` into a
    theorem is the *wiring*: showing that the concrete transfer-matrix kernel is
    a PD kernel on the interface link variables — integrating out negative-time
    links via `PositiveDefinite.integral` (from the full Boltzmann factor, now
    proved PD by `boltzmannFactorPD`), and applying `integralOperator_nonneg`.
   kernel `(Tψ)(u) = ∫ ψ(θ⁻⁰(U⁻,u⁰))·exp(-β·(...)) dμ⁻(U⁻)` is NOT of the form
   `φ(u⁻¹·v)` for a PD function `φ` on a group — the reflection map `θ⁻⁰` is a
   geometric operation, not group multiplication.  While `PosInterfaceConfig`
   is a product of SU(N)'s (hence a group), the kernel does not factor through
   the group structure.  The Mercer framework removes the *group-structure*
   obstruction, but showing the TM kernel *is* Mercer-PD still requires the
     Peter–Weyl character expansion to decompose the Boltzmann factor into
     separable positive terms (approach (c)).  This is a fundamental mathematical
     gap, not just formalization work.

     **Clean factorization PROVEN** (`osG_thetaG_factorization`): the
     reflection-positivity integrand factorizes as
     `osG(U)·osG(θU) = f(U)·f(θU)·exp(-β S_W(U))`, showing the axiom is
     equivalent to `∫ f(U)·f(θU)·exp(-β S_W) dμ ≥ 0`.  But this integral is NOT
     the standard PD quadratic form `∫∫ f(g)·conj(f(h))·K(g⁻¹h) dμ dμ ≥ 0` — it
     is a single integral with the geometric reflection θ and K evaluated at g
     (not g⁻¹h).  PD-ness of K does not imply this; the Peter–Weyl character
     expansion + orthogonality are needed to decompose the integrand into
     |Fourier coefficients|².  See `docs/gap_analysis.md`.

       Both lemmas carry two independent verification checks: (1) `#print axioms`
       confirms no hidden axiom or `sorry` (only `propext`, `Classical.choice`,
       `Quot.sound`), and (2) independent line-by-line code review of the full
       proof scripts confirmed the logic is sound (Fubini swap, a.e.-non-negativity
       of the PD quadratic-form integrand, Riemann-sum construction,
       uniform-continuity error bound, `Complex.nonneg_iff` split).  These are
       complementary — a clean `#print axioms` alone would not catch a
       wrong-but-compiling argument, and code review alone would not catch a
       silently-introduced axiom.  Both were done.

       Additionally, both lemmas were confirmed **absent from Mathlib** (as of the
       pinned commit `3bc2a1801c2416549ba5ba0b3f5728a28b87e7d9`, Lean v4.33) via
       multiple independent search angles: `PositiveDefinite` does not exist as a
       bare identifier in Mathlib; Loogle `IsCompact _ -> _ -> 0 ≤ _` returns no
       matches across all 126 relevant declarations; Loogle `0 ≤ ∫ _, _ ∂_`
       returns only generic integral-nonnegativity hits, nothing group-theoretic
       or kernel-based.  The key Mathlib API names the proofs depend on
       (`measureReal_prod_prod`, `finite_cover_balls_of_compact`) were verified
       present at the pinned commit to catch toolchain-drift breakage proactively.

3. **`exp_reTrace_positiveDefinite`** (`PositiveDefinite.lean`): proved
   unconditionally (no axiom) — it builds `exp(c·Re Tr g)` as a PD function via
   the power-series / `PositiveDefinite.tendsto` argument.  (The *plaquette*
   version `plaquetteBoltzmannPD` does need the Peter–Weyl / Clebsch–Gordan
   axiom `peterWeyl_clebschGordan_plaquette`; the single-link version does not.)

### Status of the key identity (corrected from earlier versions)
`integral_G_thetaG_eq_inner_g_Tg` in `TransferMatrix.lean` is **fully proved**
under the current Lean v4.33 toolchain (verified by `#print axioms`: only
`propext`, `Classical.choice`, `Quot.sound`).  Earlier versions of this file
claimed it "is not yet formalized" — that was stale and wrong.  The
measure-theoretic bookkeeping (`measure_factorization'`, change of variables,
`integral_prod`) is all proved; `measure_factorization'` is likewise verified
by `#print axioms` (only `propext`, `Classical.choice`, `Quot.sound`).

### Issues found and fixed:
- **2025-06-28**: Discovered that `gibbsExpectationPeriodic_reflection_positive`
  as originally stated (for ALL f) was mathematically false.  Added hypothesis
  `hf_supported : dependsOnlyOnPosInterface N T L f` (f depends only on
  positive-time and interface links).  The `transferMatrix_identity` in
  `TransferMatrix.lean` was also incorrect; file has been rewritten with
  corrected definitions.  See `docs/found_issues.md` for details.
- **This session**: `MassGapProof.lean`'s module docstring said "four axioms"
  while listing five — corrected to "five".  `transferMatrixCorrect_positive`
  (referenced in earlier versions of this file as a "currently sorry" lemma)
  does not exist under that name; the real gap is the differently-named
  `transferMatrixPositivity_axiom` axiom in `ReflectionPositivity.lean`.
  Added `IsIrreducible` (definition) and `characterOrthogonality` (axiom:
  Schur orthogonality for irreducible unitary representations of a compact
  group) to `PositiveDefinite.lean` — the key ingredient for the
  `|Fourier coefficient|²` decomposition of the reflection-positivity integral.
  Also proved `osG_thetaG_factorization` (clean factorization of the
  reflection-positivity integrand) in `ReflectionPositivity.lean`.  Added
  Added `haarMeasure_inv_invariant` (now **proved**, 0 sorries, 0 custom axioms
  — verified by `#print axioms`: only `propext, Classical.choice, Quot.sound`;
  the standard compact-group unimodularity argument) and
  `reflectLinkVariable_measurePreserving`
  (now **proved**, 0 sorries, 0 custom axioms — verified by `#print axioms`:
  only `propext, Classical.choice, Quot.sound`; composes the index-permutation
  `measurePreserving_piCongrLeft` with the componentwise-inversion
  `measurePreserving_pi` + `haarMeasure_inv_invariant` via
  `MeasurePreserving.comp`, under the necessary `hsites` hypothesis that the
  reflection permutes `sites`) to `LatticeMeasure.lean`.  The axiom
  count is now six.

### Future work:
- Wire `PositiveDefinite.integral` and `PositiveDefinite.integralOperator_nonneg`
  (both proved in `PositiveDefiniteIntegral.lean`) into the concrete
  lattice-gauge-theory setup to close `transferMatrixPositivity_axiom`.
  The Mercer-type generalization (`PositiveDefiniteKernel.integralOperator_nonneg`,
  no group structure needed) and the full-Boltzmann-factor building blocks
  (`comp_mulEquiv`, `fst`/`snd`, `finprod` in `PositiveDefinite.lean`) are now
  available.  **Key obstruction**: the TM kernel
  `(Tψ)(u) = ∫ ψ(θ⁻⁰(U⁻,u⁰))·exp(-β·(...)) dμ⁻(U⁻)` is NOT of the form
  `φ(u⁻¹·v)` for a PD function `φ` on a group — the reflection map `θ⁻⁰` is a
  geometric operation, not group multiplication.  While `PosInterfaceConfig` is
  a product of SU(N)'s (hence a group), the kernel does not factor through the
  group structure.  The Mercer framework removes the *group-structure*
  obstruction, but showing the TM kernel *is* Mercer-PD still requires the
  Peter–Weyl character expansion to decompose the Boltzmann factor into
  separable positive terms (approach (c)).
- **Character-orthogonality path** (new): the `characterOrthogonality` axiom
  (Schur orthogonality for irreducible unitary representations of a compact
  group, now in `PositiveDefinite.lean`) provides the key ingredient to turn
  the character expansion of the Boltzmann factor into a `|Fourier
  coefficient|²` decomposition of the reflection-positivity integral
  `∫ f(U)·f(θU)·exp(-β S_W) dμ`.  The path: (1) expand `exp(-β S_W) =
  ∑_λ a_λ χ_λ` (Peter–Weyl), (2) substitute into the integral, (3) use
  reflection-invariance of Haar measure + `characterOrthogonality` to rewrite
  each term as `|∫ f·χ_λ|² ≥ 0`, (4) sum with `a_λ ≥ 0`.  Steps 1–2 are
  formalized (`boltzmannFactorPD`, `osG_thetaG_factorization`); steps 3–4
  are the remaining wiring.
  **Precise analysis (2025-06-29 session):** the naive path at the level of
  the full Boltzmann factor does NOT work directly, because
  `χ_λ(θU) ≠ conj(χ_λ(U))` — the reflection `θ` is not group inversion.
  The correct approach works at the level of the **transfer matrix kernel**
  `K_TM(u, U⁻)`, which must decompose as
  `∑_λ a_λ Φ_λ(u) · conj(Φ_λ(θ⁻⁰(U⁻, u⁰)))` with `a_λ ≥ 0`.  The change of
  variables `U⁻ ↦ θ⁻⁰(U⁻, u⁰)` (measure-preserving by
  `reflectLinkVariable_measurePreserving`) then turns the integral into a sum
  of `|Fourier coefficients|² ≥ 0`.  The key obstruction: the interface
  Boltzmann factor is a **product of multiple plaquette factors**, and
  combining their character expansions requires the **Clebsch–Gordan
  decomposition** for products of characters of the same link variable — not
  currently axiomatized.  An abstract lemma (no new axioms) connecting
  separable kernel decompositions to integral positivity was identified as
  the natural next formalization step.  See `docs/gap_analysis.md`.
- Peter–Weyl theorem for SU(N) (or a bypass via spectral theory) — would remove
  the `peterWeyl_clebschGordan_plaquette` axiom.
- Schur orthogonality for compact groups — would remove the
  `characterOrthogonality` axiom.
- Construct `PeriodicExpectation` structure (requires the corrected reflection
  positivity proof).
- Continuum limit (Balaban renormalization group) — `continuum_limit_exists`.
- OS reconstruction theorem — `os_reconstruction_theorem`.
- Mass gap proof — `mass_gap_axiom` (this **is** the conjecture; not a
  placeholder).

## References

- A. Jaffe, E. Witten, "Quantum Yang-Mills Theory" (Clay Millennium Problem)
- R. Streater, A. Wightman, "PCT, Spin and Statistics, and All That"
- J. Glimm, J. Jaffe, "Quantum Physics: A Functional Integral Point of View"
- K. Osterwalder, R. Schrader, "Axioms for Euclidean Green's Functions"
- K. Osterwalder, E. Seiler, "Gauge Field Theories on a Lattice" (1979)
- T. Balaban, "Renormalization group approach to lattice gauge field theories"
- M. Hairer, "A theory of regularity structures"
- S. Chatterjee, "Yang-Mills for probabilists"
- K. Wilson, "Confinement of quarks"
-/

namespace YangMills

def description : String :=
  "Formalization of Yang-Mills existence and mass gap problem (Clay Millennium Prize)"
