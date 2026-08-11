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
   is the open one.  **Current plan: the Lüscher mechanism** (design doc
   §8.11.41–42) — integrate out temporal links first via Schur orthogonality to
   get non-negative coefficients, avoiding the `σ` twist.  Step 1 (the single-link
   `luscher_key_identity`, `PositiveDefinite.lean:1037`) is **proved** (0 sorries,
   0 new axioms); Steps 2–5 (single-site CG decomposition, 3D global cascade,
   connection to `character_expansion_nonneg_shared`, closing the axiom) remain.

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
- **2026-06-28**: Discovered that `gibbsExpectationPeriodic_reflection_positive`
  as originally stated (for ALL f) was mathematically false.  Added hypothesis
  `hf_supported : dependsOnlyOnPosInterface N T L f` (f depends only on
  positive-time and interface links).  The `transferMatrix_identity` in
  `TransferMatrix.lean` was also incorrect; file has been rewritten with
  corrected definitions.  See `docs/found_issues.md` for details.
- **This session**: `MassGapProof.lean`'s module docstring said "four axioms"
  while listing five — corrected to "six" (2026-08-03 session; the docstring
  now reads "the proof uses six axioms" and lists all six).
  `transferMatrixCorrect_positive`
  (referenced in earlier versions of this file as a "currently sorry" lemma)
  does not exist under that name; the real gap is the differently-named
  `transferMatrixPositivity_axiom` axiom in `ReflectionPositivity.lean`.
  Added `IsIrreducible` (definition) and `characterOrthogonality` (axiom:
  Schur orthogonality for irreducible unitary representations of a compact
  group) to `PositiveDefinite.lean` — the key ingredient for the
  `|Fourier coefficient|²` decomposition of the reflection-positivity integral.
  **Strengthened (2026-08-01):** the axiom now provides the full Schur
  orthogonality of **matrix elements** (`∫ (ρ_λ g)_{ij}·conj((ρ_μ g)_{kl}) dμ =
  δ_{λμ}δ_{ik}δ_{jl}/dim(λ)`, with `hDims`/`hIrr` hypotheses); the (weaker)
  character-orthogonality statement is now **derived** as the lemma
  `character_orthogonality_from_schur` (0 sorries; `#print axioms`:
  `propext, Classical.choice, Quot.sound, characterOrthogonality`).
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

### Transfer-matrix positivity closure plan (2026-07-30):
The plan to close `transferMatrixPositivity_axiom` (reducing the axiom count
from 6 to 5) via the operator-theoretic `T = B*·B` argument has four steps:
- **Step (a) — DONE** (session 5): `plaquette_product_separable_decomp`
  (`PeterWeyl.lean`) — the product of interface plaquette Boltzmann factors
  has a separable character decomposition with non-negative coefficients.
  0 sorries, 0 custom axioms.
- **Step (b) — DONE** (sessions 6–7): change of variables in the
  transfer-matrix integral.  The key measure-theoretic ingredient
  `reflectLinkVariable_measurePreserving_between` (`LatticeMeasure.lean`,
  session 6) is proved — the reflection is measure-preserving from μ⁻ to μ⁺.
  Sub-step (1) `reflectToPosInterface_involution` (`TransferMatrix.lean`,
  session 7) is proved — `reflectToPosInterface(reflectPosToNeg(V⁺), u⁰) =
  mergePosInterface(V⁺, σ(u⁰))`.  The pointwise identity
  `transferMatrix_integrand_change_of_variables` (the integrand at `U⁻` equals
  the transformed integrand at `V⁺ = reflect(U⁻)`) is proved.  The integral-level
  change of variables `transferMatrix_change_of_variables` (showing
  `transferMatrixCorrect = transferMatrixReflected` via `integral_map` +
  `reflectLinkVariable_measurePreserving_between`) is proved.  New definitions
  `reflectPosToNeg`, `reflectNegToPos`, `sigmaInterface`, `transferMatrixReflected`
  and supporting lemmas added.  All 0 sorries, 0 custom axioms.
- **Steps (c)–(d) — pending**: CG + character orthogonality, conclude
  `T = B*·B` and `⟨g, Tg⟩ = ‖Bg‖² ≥ 0`.
  **Step (c) analysis (2026-07-31 session): L² expansion obstruction.**  A
  detailed analysis revealed that closing `transferMatrixPositivity_axiom`
  from the current axioms alone is NOT possible.  After steps (a)–(b), the
  integral becomes `∑_w F(w) · ∫_{u⁰} Ψ_w(u⁰) · A_w(u⁰) · A_w(σ(u⁰)) dμ⁰(u⁰)`
  where `A_w(u⁰) = ∫_{u⁺} f(u⁺, u⁰) · Φ_w(u⁺) dμ⁺(u⁺)` depends on the
  arbitrary test function `f`.  This is obstruction 3 (the `σ` reflection
  gives `A_w(u⁰) · A_w(σ(u⁰))` instead of `|A_w(u⁰)|²`), and evaluating the
  `u⁰` integral requires expanding `A_w(u⁰)` in the **L² basis**
  (Peter–Weyl completeness: matrix elements of irreducible representations
  span `L²(G)`), which is NOT provided by the current axioms.
  `peterWeyl_clebschGordan_plaquette` provides the character expansion of the
  **Boltzmann factor** (a specific function), not the L² expansion of
  **arbitrary** functions.  **Update (2026-08-01 session):** the
  `characterOrthogonality` axiom has been **strengthened** from character
  orthogonality to the full **Schur orthogonality of matrix elements**
  (`∫ (ρ_λ g)_{ij}·conj((ρ_μ g)_{kl}) dμ = δ_{λμ}δ_{ik}δ_{jl}/dim(λ)`, with
  `hDims`/`hIrr` hypotheses), and the (weaker) character-orthogonality statement
  is now **derived** as the lemma `character_orthogonality_from_schur` (0 sorries;
  `#print axioms`: `propext, Classical.choice, Quot.sound, characterOrthogonality`).
   The remaining gap is the L² **completeness** statement (matrix elements span
   `L²(G)`), which is now **provided** (2026-08-02 session) by the strengthened
   `peterWeyl_clebschGordan_plaquette` axiom: a countable `Λ` of all irreps +
   the "trivial orthogonal complement" form (if all Fourier coefficients vanish,
   then `f = 0` a.e.).  Axiom count STILL SIX (enriched existing axiom).  The
   axiom was **further strengthened** (2026-08-02 session 3) to also provide the
   **matrix-element Clebsch–Gordan coefficients** `cgME` — the unitary
   change-of-basis matrices implementing `ρ_s ⊗ ρ_t → ⊕_ν ρ_ν` at the
   matrix-element level, needed to evaluate the triple-product integrals
   `∫ χ_w · (ρ_λ)_{ij} · conj((ρ_μ)_{kl}) dμ` in the reflection-positivity
   reorganization.  Axiom count STILL SIX.  The remaining work is to **use**
   the L² completeness + Schur orthogonality + matrix-element CG to evaluate
   the `u⁰` integral as `∑ |Fourier coefficient|² ≥ 0`, closing
   `transferMatrixPositivity_axiom` (count → 5).  See
   `docs/transfer_matrix_positivity_design.md` §5a and `docs/gap_analysis.md`
   §"Step (c) analysis complete" for the full analysis.
   **Update (2026-08-02 session 4):** the V⁺ conjugation building block
   `prod_conj_partition_dual` (`PeterWeyl.lean`) is proved (0 sorries, 0 custom
   axioms) — it separates the V⁺ links of a character product with conjugated
   dual characters via the dual map.  Building on it, **lemma 1 of the §8.8
   formalization plan** — `interface_kernel_character_expansion` (`PeterWeyl.lean`)
   — is proved (0 sorries, 0 custom axioms; `#print axioms`:
   `propext, Classical.choice, Quot.sound`): a product of interface plaquette
   Boltzmann factors admits the separable character expansion
   `∑_w F(w)·Φ_w(U⁺)·Ψ_w(u⁰)·conj(Φ_w(V⁺))` with `F(w) ≥ 0`, given a disjoint
   link partition `L = L_U ⊔ L_0 ⊔ L_V`.  This is the abstract-level kernel
   character expansion; the remaining gap to the *concrete* transfer-matrix
    kernel is a separate lemma connecting `exp(-β·S_OS)` to the abstract
    plaquette-product form.
   **Update (2026-08-02 session 5):** the concrete↔abstract bridge is partially
   closed (§8.11 of `docs/transfer_matrix_positivity_design.md`).  Two of three
   pieces are proved (0 sorries, 0 custom axioms — `#print axioms`:
   `propext, Classical.choice, Quot.sound`): **G1** `exp_neg_beta_wilsonActionFinite_eq_prod`
   (`exp(-β·S_W) = ∏ exp(-β·S_p)`, exp-of-sum = product-of-exps) and **G2**
   `plaquetteContribution_exp_decomp` / `plaquetteContribution_exp_decomp_tm`
   (`exp(-S_p) = exp(-β)·exp((β/N)·Re Tr)` / `exp(-β·S_p) = exp(-β²)·exp((β²/N)·Re Tr)`,
   with coupling `c ≥ 0` and positive constant).  G1+G2 rewrite
   `exp(-β·S_W) = C·∏_p exp(c·Re Tr(P_p))` with `C > 0`, `c ≥ 0` — the abstract
   **G3** (interface plaquette enumeration +
   link partition `L = L_U ⊔ L_0 ⊔ L_V`) remains — pure combinatorial
   bookkeeping, no new axioms.  All G1/G2 lemmas are pure algebra; they do NOT
   strengthen any axiom (per the axiom-growth audit,
   `docs/axiom_growth_audit.md`).
   **Update (2026-08-02 session 6):** **G3 is now DONE** —
   `isInterfacePlaquette` + `wilsonActionOSInterface_eq` +
   `exp_neg_beta_wilsonActionOSInterface_eq_prod` +
   `exp_neg_beta_wilsonActionOSInterface_eq_prod_abstract`
   (`ReflectionPositivity.lean`), all 0 sorries, 0 custom axioms (`#print axioms`:
   `propext, Classical.choice, Quot.sound`).  G1+G2+G3 together rewrite the
   concrete interface Boltzmann factor `exp(-β·S_int)` as a product of abstract
   plaquette Boltzmann factors `exp(c·Re Tr(P_p))` (with `c = β²/N ≥ 0`) over
   interface plaquettes, times a positive constant — exactly the form
    `interface_kernel_character_expansion` operates on.  **Remaining for lemma 2:**
    identify the link partition `L = L_U ⊔ L_0 ⊔ L_V` (U⁺/u⁰/V⁺ links) for the
    concrete lattice, then Fubini.  All G1/G2/G3 lemmas are pure algebra; they do
    NOT strengthen any axiom (per the axiom-growth audit,
    `docs/axiom_growth_audit.md`).
    **Update (2026-08-03 session 3):** **sub-steps (i) and (ii) of Lemma 2 are
    now DONE.**  Sub-step (i): concrete link/plaquette structures
    (`InterfacePlaquette`, `InterfaceLink`, `interfaceLinkAssign`+surjectivity,
    `interfaceLinkVar`, `plaquetteProduct_interface_eq`, the link partition
    `interfaceLinkPos`/`Int`/`Neg`+disjoint cover, `prod_if_interface_eq_prod_subtype`)
    — all 0 sorries, 0 custom axioms.  Sub-step (ii): two new lemmas in
    `ReflectionPositivity.lean` — `interface_boltzmann_eq_abstract_product`
    (G3 + `prod_if_interface_eq_prod_subtype` + `plaquetteProduct_interface_eq` →
    `exp(-β·S_int) = C·∏ exp((β²/N)·Re Tr(g₀g₁g₂⁻¹g₃⁻¹))` with `C > 0`; 0 sorries,
    0 custom axioms) and `interface_product_character_expansion` (applies the
    abstract `interface_kernel_character_expansion` to the concrete lattice data,
    yielding the concrete separable character expansion; 0 sorries, uses
    `peterWeyl_clebschGordan_plaquette`, axiom count 6 unchanged).  Full `lake
    build` GREEN (2972 jobs).  **Remaining for lemma 2:** sub-step (iii) — Fubini
    to exchange the u⁺/V⁺ integrals with the character-expansion sum.
    **Update (2026-08-03 session 4):** sub-step (iii) steps 1–2 DONE.  Bridge
    lemmas `interfaceLinkVar_extendToFullConfig_pos`/`_int`/`_neg`
    (`TransferMatrix.lean`) identify `interfaceLinkVar` with site-based configs
    (`U_plus`/`U_zero`/`U_minus`).  0 sorries, 0 custom axioms.  Full `lake build`
     GREEN.  V⁺ conjugation analysis (design doc §8.11.4): `V_w(V⁺) ≠
     conj(Φ_w(V⁺))` due to reindexing; Fubini reduction doesn't require V⁺
     conjugation.  **Remaining:** steps 3–6 (substitute char expansion, Fubini,
     measure factorization, identify A_w/B_w).
     **Update (2026-08-03 session 5):** step 3 (pointwise substitution) DONE.
     `interface_boltzmann_character_expansion` (`ReflectionPositivity.lean`)
     composes `interface_boltzmann_eq_abstract_product` +
     `interface_product_character_expansion` to give the pointwise identity
     `exp(-β·S_int(U)) = (C : ℂ) · ∑_w (F w : ℂ) · Φ_w(U)·Ψ_w(U)·V_w(U)` with
     `C > 0`, `F(w) ≥ 0`. 0 sorries; uses `peterWeyl_clebschGordan_plaquette`
     (axiom count 6, unchanged). Full `lake build` GREEN. **Key technique:**
     `norm_cast at h` pulls the coercion OUT of the product in `hF_decomp`
     (converting `∏_p ↑(Real.exp(...))` to `↑(∏_p Real.exp(...))` WITHOUT
     touching `Real.exp`), then `rw [Complex.ofReal_mul, h]` — avoiding the
     `Real.exp → Complex.exp` conversion that `push_cast` triggers. **Remaining:**
     steps 4–6 (Fubini finite sum ↔ integral, measure factorization split,
     identify Fourier coefficients A_w/B_w).
     **Update (2026-08-03 session 6):** UNIFORM CHARACTER EXPANSION REFACTOR.
     The Fubini exchange (step 4) requires pulling `∑_w` outside the integral,
     which needs the SAME `(C, ι, ρ, dual, F)` for every `U`. Analysis confirmed
     all five are `U`-independent (C = ∏_p exp(-β²); ι,ρ,dual from
     `peterWeyl_clebschGordan_plaquette` (no U arg); F from
     `charProduct_mixed_link_separable_decomp` which has `∀ g` inside). Refactored
     5 lemmas IN PLACE to move `∀ U`/`∀ g` INSIDE the existentials:
     `plaquette_product_separable_decomp`, `interface_kernel_character_expansion`,
     `interface_boltzmann_eq_abstract_product`,
     `interface_product_character_expansion`,
     `interface_boltzmann_character_expansion`. Full `lake build` GREEN (2890
     jobs); `#print axioms` = NO `sorryAx`, axiom count 6 unchanged. The uniform
     `interface_boltzmann_character_expansion` now provides a single
     `(C, ι, ρ, dual, F)` with `∀ U, (exp(-β·S_int(U)) : ℂ) = (C : ℂ)·∑_w …`,
      which is exactly what step 4 needs.
      **Update (2026-08-02 sessions 7–9 + 2026-08-03):** **Steps 4a–4e of the
      Fubini reduction are DONE** (all 0 sorries, 0 custom axioms): 4a —
      `inner_product_complex_eq_product_integral` (inner product → `ℂ`-valued
      product-measure integral via `haarMeasurePosInterface_eq` +
      `MeasurableEmbedding.integral_map`); 4b —
      `transferMatrixReflected_split_exp_real`/`_complex` (split the exp, pull the
      V⁺-independent factor out); 4c — `integrand_character_expansion_pointwise`,
      `integral_finsetSum_pull_constants`,
      `transfer_matrix_fubini_character_expansion` (substitute the character
      expansion and exchange `∑_w` with the V⁺ integral), with `h_int` discharged
      via the domination argument `transfer_matrix_fubini_integrability` (pointwise
      bound `‖integrand_w(V⁺)‖ ≤ K_w·|full(V⁺)|` using `charTripleProduct_norm_le`
      + `exp_neg_beta_wilsonActionOSInterface_lower_bound`) and `h_integrand_ae`
      discharged via `transfer_matrix_integrand_ae` from `hψ_int` + `hMeas` (the
      axiom strengthening #6 of 2026-08-03); self-contained versions
      `transfer_matrix_fubini_integrability_self` and
      `transfer_matrix_fubini_character_expansion_self` take only `hψ_int` +
      `h_meas`; 4d — `restrictToPositive`/`mergePosInterface_restrictToPositive_restrictToInterface`
      (restrict-after-merge foundation), the bridge lemmas
      `interfaceLinkVar_extendToFullConfig_pos'/_int'/_neg'`,
      `transfer_matrix_fubini_character_expansion_separated(_pull)`,
      `transfer_matrix_fubini_integrated` (integrate over `u`, CoV
      `u = merge(U⁺,u⁰)`, restrict-after-merge simplification),
      `transfer_matrix_fubini_integrated_prod` (product-measure Fubini split via
      `integral_prod_symm`, integrability of `g_RHS` via the from-LHS push-through
      `MeasurePreserving.integrable_comp_emb`), and Lemma 4b
      `transfer_matrix_fubini_inner_pull` (+ `fourierCoeffPos`/`fourierCoeffNeg`
      defs — pull U⁺-independent constants out of the inner U⁺ integral, rewrite
      each `∫ U⁺ prefactor·charFactorPos` as `fourierCoeffPos`); 4e —
      `transfer_matrix_fubini_integrated_pull` (integrate the pointwise identity
      over `u⁰` via product-measure Fubini, recognizing `fourierCoeffPos` and
      `fourierCoeffNeg` by defeq), producing
      `C · ∑_w (F w) · ∫_{u⁰} charFactorInt · fourierCoeffNeg · fourierCoeffPos ∂μ⁰`.
      Per-`w` integrability remains a hypothesis (`h_int`).
      **Update (2026-08-04 session 17):** **Lemma 3 (σ-inversion) is DONE.**  The
      plain-form identity `B_w(u⁰) = A_{w*}(σ(u⁰))` is proved as
      `fourierCoeffNeg_eq_fourierCoeffPos_fullReflect` (TransferMatrix.lean, ~line
      5597): the full reflection reindexing `fullReflectReindex` (pos ↔ neg swap via
      `reflectInterfaceLink`, `dual` on time-like links) + per-link/product identities
      `charFactorNeg_eq_star_charFactorPos_link_fullReflect` /
      `charFactorNeg_eq_star_charFactorPos_fullReflect` /
      `star_charFactorNeg_eq_charFactorPos_fullReflect` (via `Finset.prod_bij`
      reindexing neg → pos).  This avoids the invalid `w ↦ θw` sum reindexing (θ is a
      projection); no `dual` involutivity needed (`conj = star` is defeq).  0 sorries,
      0 custom axioms.  The residual "σ twist" (`A_w·A_{w*}(σ)` ≠ `|A_w|²`) means the
      L² (matrix-element) expansion is required regardless of reindexing.  **Remaining:**
      lemma 5 (L² expansion reorganization: expand `A_w`/`A_{w*}(σ)` in the
      matrix-element basis, σ-inversion + `repMatrixElement_inv` + CG triple-product
      evaluation + Schur orthogonality → `∑ |Fourier coefficient|² ≥ 0`) and final
      assembly (lemma 6) to close `transferMatrixPositivity_axiom`.
      **Update (2026-08-06 sessions 38–39): Lüscher roadmap — Step 1 DONE.**  The
      plan to close `transferMatrixPositivity_axiom` (count 6 → 5) is now the
      **Lüscher mechanism** (design doc §8.11.41–42): integrate out temporal links
      *first* via Schur orthogonality (forcing matching representations and giving
      strictly positive coefficients `1/d_γ > 0`), which avoids the `σ` twist that
      obstructs the direct character-expansion approach (the `∑ A²` vs `∑ |A|²`
      obstruction of §8.11.38).  **Step 1 is proved:** `luscher_key_identity`
      (`PositiveDefinite.lean:1037`) — the single-link identity
      `∫_G χ_γ(g·h)·χ_{γ'}(g⁻¹·k) ∂μ = δ_{γγ'}·(1/d_γ)·χ_γ(h·k)` for irreducible
      unitary representations of a compact group with normalized Haar measure.
      0 sorries, 0 NEW custom axioms — `#print axioms` confirms only
      `propext, Classical.choice, Quot.sound, characterOrthogonality` (the existing
      Schur-orthogonality axiom; axiom count remains **six**).  The proof expands
      both characters into matrix elements (`Tr(AB)=∑_{ij}A_{ij}B_{ji}` +
      `ρ(g⁻¹)=ρ(g)†`), distributes via `Fintype.sum_mul_sum`, exchanges four sums
      with the integral via `integral_finsetSum`, factors constants via
      `integral_smul`, and applies Schur orthogonality (diagonal: `Finset.sum_eq_single`
      collapses the Kronecker deltas and `Matrix.trace_mul_comm` recognizes the
      surviving trace as `χ_γ(h·k)`; off-diagonal: sum of zeros).  This is the
      one-site integral the 1D/3D cascade iterates.  **Remaining:** the full 1D
      cascade (`U_1D = ∑_γ (c_γ)^L/d_γ^{L-1}·χ_γ(∏_x W)`, a Fubini iteration of
      the key identity), then Step 2 (single-site CG decomposition for 3D via
      `hcgME_decomp`/`hcgME_unitary`), Step 3 (3D global cascade), Step 4 (connect
      to `character_expansion_nonneg_shared`, `PositiveDefiniteIntegral.lean:1196`),
      Step 5 (close `transferMatrixPositivity_axiom` via
      `integral_G_thetaG_eq_inner_g_Tg`).  Build GREEN (full `lake build` 2972
      jobs; targeted `YangMills.Proofs.PositiveDefinite` 2856 jobs).
      **Update (2026-08-06 → 2026-08-08 sessions 41–52): Steps 2–4 DONE.**
      Step 2: `cgME_decomp_3fold`/`_conj` + `single_site_3D_luscher_integral`
      (`PeterWeyl.lean`).  Step 3(a–c): `cg_unitarity_nonneg`, `chainIntegral_eq`,
      `luscher_2site_2D_cascade_charlevel` (`PositiveDefinite.lean`) — the
      character-level 2-site 2D cascade reducing the integral to
      `∑_ν cg(s₁,s₂,ν)·cg(t₁,t₂,ν)·(1/dims ν)·χ_ν(W·V)`.  Step 4:
      `cascade_integral_nonneg` (`PositiveDefiniteIntegral.lean:1275`) — the
      kernel `∑_ν cg·cg·(1/dims ν)·χ_ν(W·V)` integrated against `f(W)·f(V⁻¹)`
      is `≥ 0`, via `character_expansion_nonneg` with Sigma index type
      `ι' = Σ ν, Fin(dims ν)×Fin(dims ν)`.  0 sorries, build GREEN (2892 jobs),
      `#print axioms` = `[propext, Classical.choice, Quot.sound]` (only 3 — no
      `characterOrthogonality` needed).  **Remaining:** Step 5 — close
      `transferMatrixPositivity_axiom` (axiom count 6 → 5).
      **Update (2026-08-08 session 53): TM closure step 4 PROVED.**
      `fourierCoeffPos_sigma_invisible` (`TransferMatrix.lean:4650`) — the
      positive Fourier coefficient `A_w(u⁰) = fourierCoeffPos(w, u⁰)` is
      σ-invisible: `A_w(σ(u⁰)) = A_w(u⁰)` when `f` satisfies
      `dependsOnlyOnPosSpatialInterface`.  0 sorries, 3 axioms, build GREEN
      (2972 jobs).  This is step 4 of the 6-step TM closure plan (§8.11.40):
      steps 1–4 now PROVED; steps 5–6 remain (u⁰_t integral via character
      orthogonality; non-negativity of remaining kernel via Lüscher mechanism).
      **Update (2026-08-08 session 54): Step 5 sub-lemmas 1–2 PROVED.**
      `charFactorInt_eq_temporal_spatial` (`TransferMatrix.lean:~2406`) —
      `charFactorInt` decomposes into temporal (μ=0) and spatial (μ≠0) parts
      via `prod_interfaceLinkInt_eq_temporal_spatial`. 0 sorries, 0 new axioms.
      `fourierCoeffPos_independent_of_temporal` (`TransferMatrix.lean:~4822`) —
      `fourierCoeffPos` depends only on `u⁰_s` (spatial interface links), not
      `u⁰_t` (temporal interface links), because `g` and `S⁺` are both
      invisible to changes in temporal interface links. 0 sorries, 0 new axioms.
      Supporting lemmas: `extendLinkVariable_merge_spatial_agree`,
      `f_temporal_invisible`, `osPositiveOfPosInterface_temporal_invariant`,
      `g_posInterface_temporal_invisible` (all generalizations of their σ
      counterparts). Build GREEN (2891 jobs). **Remaining:** step 5 sub-lemma 3
      (temporal integral `∫χ_γ = δ_{γ,trivial}` — requires identifying the
      trivial representation in `ι`, see §8.11.43) and step 6 (Lüscher mechanism
      for non-negativity of the remaining kernel).
      **Update (2026-08-08 session 55): Step 5 sub-lemma 3 PROVED (with hypothesis).**
      `integral_repCharacter_eq_iff_trivial` (`PositiveDefinite.lean:~1066`) —
      `∫_G χ_γ(g) ∂μ = if γ = triv then 1 else 0`, a direct corollary of
      `character_orthogonality_from_schur` with `s = triv` (since `χ_{triv} = 1`
      ⟹ `conj(χ_{triv}) = 1` ⟹ `∫ χ_γ · conj(χ_{triv}) = ∫ χ_γ`). 0 sorries,
      0 new axioms, `#print axioms` = `[propext, Classical.choice, Quot.sound,
      characterOrthogonality]`. The trivial rep is taken as a hypothesis
      (`htriv : ∀ g, χ_{triv}(g) = 1`); deriving it from the axiom is analyzed in
      §8.11.44 but not formalized. **Key analysis (§8.11.44):** the naive expansion
      (steps 3–6) CANNOT close the axiom — the kernel coefficients are complex, not
      non-negative reals. The Lüscher mechanism (step 6) bypasses steps 3–5 entirely
      by using a PLAQUETTE-LEVEL character expansion (5-index from the axiom) where
      each temporal link appears in multiple characters from adjacent plaquettes.
      The Lüscher cascade then integrates out temporal links via Schur orthogonality,
      giving non-negative coefficients matching `cascade_integral_nonneg`.
      **Update (2026-08-10 sessions 73–79): §8.11.61 plan — Steps 1–4 DONE.**
      A new plan (design doc §8.11.61) supersedes the Lüscher roadmap. The key
      insight (§8.11.60): the correct mechanism is `dependsOnlyOnPositive` (f
      depends only on positive links, NOT interface links) + the **full**
      character expansion (over ALL links). This makes the interface link
      integral **unweighted** character orthogonality (giving `δ_{w|_int, trivial}`).
      Step 2 (full character expansion, §8.11.62), Step 3
      (`interface_char_integral_trivial`, §8.11.64 — axiom extended to provide
      `σ_0`), and Step 4 (full-lattice character factor lemmas, §8.11.65 —
      `fullReflectReindexLink`, `charFactorPosAll`/`charFactorNegAll`, per-link
      & product identities, all full-lattice analogues of the interface-only
      versions) are all proved. All 0 sorries, 0 custom axioms (only standard 3:
      propext, Classical.choice, Quot.sound). Build GREEN, axiom count 6 unchanged.
      **Remaining:** Step 5 (REVISED, §8.11.66 — the `|Â_w|²` claim is INCORRECT;
      actual result is `Â_w · Â_{w*}` with reflected weight `w*`, NOT trivially
      non-negative; non-negativity requires PD of the u⁰-integrated kernel K)
      and Step 6 (replace `transferMatrixPositivity_axiom` with proved lemma,
      count 6 → 5).
  **Update (2026-08-10 session 80): §8.11.66 CRITICAL ANALYSIS.** The §8.11.61
  claim that Step 5 gives `|Â_w|²` is **INCORRECT**. The actual result is
  `I = C · Σ_{w: trivial on int} F(w) · Â_w · Â_{w*}` where
  `w* = fullReflectReindexLink dual w` is the **reflected** weight. This is a
  product of two complex Fourier coefficients (NOT an absolute square), and is
  **NOT trivially non-negative**. The non-negativity requires the **PD of the
  u⁰-integrated kernel** `K = ∫_{u⁰} exp(-β·S_W) dμ⁰` (which IS PD, bypassing
  the §8.11.60 per-u⁰ objection, because the u⁰ integral is done FIRST giving δ
  by character orthogonality). No code changes — pure analysis. Build GREEN,
  0 sorries, 6 axioms.
  See `docs/transfer_matrix_positivity_design.md` for the full design.

  **Update (2026-08-10 session 81): §8.11.67 CRITICAL ANALYSIS.** The §8.11.66
  strategy ("K is PD by PD of full Boltzmann") is **ALSO INCORRECT** — the
  group-PD of B does NOT transfer to Mercer-PD of K (B(U) ≠ B(g⁻¹·h), θ is not
  a group homomorphism). The **CORRECT mechanism** is the **Lüscher decomposition**
  T = V^{1/2}·U·V^{1/2}: spatial plaquettes → V (PD multiplication operator via
  Schur product), temporal plaquettes → U (positive integral operator via Lüscher
  cascade + `character_kernel_integral_nonneg`). The full character expansion fails
  because it expands ALL plaquettes in characters, giving `Â_w · Â_{w*}` (product at
  different weights, NOT |Â_w|²). The Lüscher decomposition succeeds because it
  separates temporal and spatial plaquettes and handles them by different mechanisms.
  **Code**: `fullBoltzmannPD` theorem PROVED and build GREEN (session 83,
  2026-08-11). The whnf timeout was caused by `addVectorPeriodic`'s `match μ
  with | 0 => ... | 1 => ...` getting stuck during `whnf`/`isDefEq` when `μ`
  is a variable (e.g. `p.2.1`). Fix: use `PositiveDefinite.congr` for ALL
  steps — build PD proofs WITHOUT declared types (so no conclusion defeq
  check against the `∏` notation), then transfer PD with `congr` + `funext`
  + `rfl` (the `funext` goal is alpha-equivalent, so `rfl` is fast — `isDefEq`
  confirms structural equality without unfolding `plaquetteProduct`). Step 6
  uses `exact_mod_cast h_eq U`. `#print axioms` = `[propext,
  Classical.choice, Quot.sound, peterWeyl_clebschGordan_plaquette]` (only 4 —
  does NOT depend on `characterOrthogonality` or
  `transferMatrixPositivity_axiom`). Full `lake build` GREEN (2972 jobs).

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
  **Update (2026-08-01):** the `characterOrthogonality` axiom has been
  **strengthened** to provide the full Schur orthogonality of **matrix
  elements** (not just characters), with `hDims`/`hIrr` hypotheses; the
  character-orthogonality statement is now the derived lemma
  `character_orthogonality_from_schur`.  The stronger matrix-element version
  is needed because the test function `f` produces arbitrary (non-class)
  functions of the interface links, which must be expanded in the
  matrix-element basis (see the L²-expansion obstruction analysis in the
  transfer-matrix positivity closure plan above).
  **Precise analysis (2026-06-29 session):** the naive path at the level of
  the full Boltzmann factor does NOT work directly, because
  `χ_λ(θU) ≠ conj(χ_λ(U))` — the reflection `θ` is not group inversion.
  The correct approach works at the level of the **transfer matrix kernel**
  `K_TM(u, U⁻)`, which must decompose as
  `∑_λ a_λ Φ_λ(u) · conj(Φ_λ(θ⁻⁰(U⁻, u⁰)))` with `a_λ ≥ 0`.  The change of
  variables `U⁻ ↦ θ⁻⁰(U⁻, u⁰)` (measure-preserving by
  `reflectLinkVariable_measurePreserving`) then turns the integral into a sum
  of `|Fourier coefficients|² ≥ 0`.  The key obstruction: the interface
  Boltzmann factor is a **product of multiple interface plaquette factors**, and
  combining their character expansions requires the **Clebsch–Gordan
  decomposition** for products of characters of the same link variable — not
  currently axiomatized.  The abstract lemma (no new axioms) connecting
  separable kernel decompositions to integral positivity is now **proved** as
  `character_expansion_positivity` / `character_expansion_nonneg`
  (`PositiveDefiniteIntegral.lean`): if `K(x, y) = ∑_i a_i · Φ_i(x) ·
  conj(Φ_i(θ y))` with `θ` measure-preserving and `a_i ≥ 0`, then
  `∫∫ f(x)·f(θ y)·K(x, y) dν dμ = ∑_i a_i · ‖∫ f·Φ_i dμ‖² ≥ 0` (0 sorries, 0
  custom axioms — verified by `#print axioms`).  This is the scaffold the
  concrete Peter–Weyl character expansion of the TM kernel would plug into; it
  does **not** close `transferMatrixPositivity_axiom` (which requires showing
  the TM kernel has the required separable decomposition — the Clebsch–Gordan
  gap).  See `docs/gap_analysis.md`.
  **Further analysis (2026-07-02 session):** a detailed investigation revealed
  that `character_expansion_positivity` does NOT directly apply to the lattice
  case, for three reasons: (1) `θ⁻⁰(U⁻, u⁰)` depends on both `x` (through
  `u⁰`) and `y` (`U⁻`), while the lemma requires `θ : Y → X` (function of
  `y` only); (2) the pushforward of `μ⁻` by `θ⁻⁰(·, u⁰)` is
  `μ⁺ × δ_{σ(u⁰)}` (singular), not the full `μ⁺⁰`; (3) the `σ` reflection
  on interface time-like links (inverting them) causes `χ(g)²` instead of
  `|χ(g)|²`, giving `∑ a_i ∫ A_i(u⁰) conj(A_i(σ(u⁰))) dμ⁰(u⁰)`, which is NOT
  necessarily non-negative.  The correct approach is the operator-theoretic
  argument: show `T = B* · B` for some operator `B` defined via the character
  expansion (Peter–Weyl + CG), then `⟨g, Tg⟩ = ‖Bg‖² ≥ 0`.  This requires a
  Clebsch–Gordan axiom and the full combinatorial wiring of the interface
  plaquette expansion.  See `docs/gap_analysis.md` for the full analysis.
  **Progress (2026-07-03 session):** Step (a) — the Clebsch–Gordan axiom — is
  now complete.  The `peterWeyl_clebschGordan_plaquette` axiom has been
  **strengthened** to also provide the CG decomposition for character products
  `χ_s(g)·χ_t(g) = ∑_w cg s t w · χ_w(g)` with `cg s t w ≥ 0` (Littlewood–
  Richardson).  Two new lemmas proved from it (0 sorries, 0 custom axioms):
  `charProduct_PD` and `charProduct_finset_decomp` (in `PeterWeyl.lean`).
  Two further lemmas proved from the strengthened axiom (0 sorries, 0 custom
  axioms): `charSum_product_decomp` (product of two non-negative-weighted char
  sums decomposes as a non-negative-weighted char sum via CG) and
  `charSum_finprod_decomp` (finite product of non-negative-weighted char sums
  decomposes as a non-negative-weighted char sum via iterated CG), and
   `charSum_product_link_decomp` (product of per-link character sums decomposes
   as a non-negative-weighted sum of products of characters — the separable
   decomposition of the full Boltzmann factor).  Two further lemmas proved
   (2026-07-05 session, 0 sorries, 0 custom axioms — verified by `#print
   axioms`): `charProduct_finset_decomp'` (generalized CG decomposition for a
   product of characters indexed by a finset of *appearances* `A` via
   `appChar : A → ι`, handling duplicate character indices) and
    `charProduct_link_separable_decomp` (per-term separable decomposition: a
    product of characters grouped by link decomposes as a non-negative-weighted
    sum of products of single characters — the key algebraic ingredient for the
    interface Boltzmann factor decomposition).  The axiom was **further
    strengthened** (2026-07-30 session) to also provide a dual (contragredient)
    map `dual : ι → ι` with `χ_{dual(i)}(g) = conj(χ_i(g))`, needed to handle
    inverted links in the plaquette product (`χ(g⁻¹) = conj(χ(g)) =
    χ_{dual}(g)` by `repCharacter_inv`).  Two further lemmas proved from the
    strengthened axiom (2026-07-30 session, 0 sorries, 0 custom axioms —
    verified by `#print axioms`): `charProduct_mixed_finset_decomp'`
    (mixed-conjugation CG decomposition: a product of characters with mixed
    conjugation — some `χ(g)`, some `conj(χ(g))` — of the same group element
    decomposes as a non-negative-weighted sum of single characters, using the
    dual map to convert `conj(χ)` to `χ_{dual}`) and
     `charProduct_mixed_link_separable_decomp` (per-term separable decomposition
     with mixed conjugation: a product of characters with mixed conjugation
     grouped by link decomposes as a non-negative-weighted sum of products of
     single unconjugated characters — the key algebraic ingredient for the
     interface Boltzmann factor decomposition with inverted links).  Step (b) —
     formalizing the operator `B` and showing `T = B* · B` — remains; the per-term
     separable decomposition (with mixed conjugation) is now proved, and the
     remaining steps are: (a) expand the product of plaquette factors and apply
     the per-term decomposition to get the full separable decomposition of the
     interface Boltzmann factor, (b) change variables in the transfer-matrix
     integral (reflecting negative links to positive), (c) use CG with dual
   representations to combine reflected and unreflected characters, (d) use the
   strengthened `characterOrthogonality` (Schur orthogonality of matrix elements)
   + the L² completeness (now provided by the strengthened
   `peterWeyl_clebschGordan_plaquette` axiom, 2026-08-02) + the **matrix-element
   CG coefficients** `cgME` (also provided by the strengthened axiom, 2026-08-02
   session 3) to expand `A_w` in the matrix-element basis, evaluate the
   triple-product integrals, and reorganize as
   `∑_w a_w · |Fourier coefficient|² ≥ 0`.
- Peter–Weyl theorem for SU(N) (or a bypass via spectral theory) — would remove
  the `peterWeyl_clebschGordan_plaquette` axiom.
- Schur orthogonality for compact groups (now stated for matrix elements of
  irreducible representations, not just characters) — would remove the
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
