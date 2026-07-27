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
   positivity chain.  The **remaining** work to turn
   `transferMatrixPositivity_axiom` into a theorem is the *wiring*: showing
   that the concrete transfer-matrix kernel is a PD kernel on the interface
   link variables.  **Key obstruction**: the TM kernel
   `(Tψ)(u) = ∫ ψ(θ⁻⁰(U⁻,u⁰))·exp(-β·(...)) dμ⁻(U⁻)` is NOT of the form
   `φ(u⁻¹·v)` for a PD function `φ` on a group — the reflection map `θ⁻⁰` is a
   geometric operation, not group multiplication.  While `PosInterfaceConfig`
   is a product of SU(N)'s (hence a group), the kernel does not factor through
   the group structure.  Closing the axiom requires either (a) a more general
   PD kernel theory (Mercer-type), (b) showing the TM kernel reduces to the
   group-theoretic form, or (c) applying the Peter–Weyl character expansion
   directly to the TM kernel.  This is a fundamental mathematical gap, not
   just formalization work.

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

### Future work:
- Wire `PositiveDefinite.integral` and `PositiveDefinite.integralOperator_nonneg`
  (both proved in `PositiveDefiniteIntegral.lean`) into the concrete
  lattice-gauge-theory setup to close `transferMatrixPositivity_axiom`.
  **Key obstruction**: the TM kernel `(Tψ)(u) = ∫ ψ(θ⁻⁰(U⁻,u⁰))·exp(-β·(...)) dμ⁻(U⁻)`
  is NOT of the form `φ(u⁻¹·v)` for a PD function `φ` on a group — the reflection
  map `θ⁻⁰` is a geometric operation, not group multiplication.  While
  `PosInterfaceConfig` is a product of SU(N)'s (hence a group), the kernel does
  not factor through the group structure.  Closing the axiom requires either
  (a) a more general PD kernel theory (Mercer-type), (b) showing the TM kernel
  reduces to the group-theoretic form, or (c) applying the Peter–Weyl character
  expansion directly to the TM kernel.
- Peter–Weyl theorem for SU(N) (or a bypass via spectral theory) — would remove
  the `peterWeyl_clebschGordan_plaquette` axiom.
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


