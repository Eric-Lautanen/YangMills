/-
# Reflection Positivity: Full Boltzmann PD and Luscher Decomposition
-/

import YangMills.Proofs.ReflectionPositivity.CharacterExpansion

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open scoped BigOperators
open MeasureTheory
open Complex
open scoped ComplexConjugate

namespace YangMills
namespace Lattice
/-! ## Full Boltzmann positive-definiteness (building block for Lüscher decomposition)

The full Boltzmann factor `exp(-β·S_W)` is a product of plaquette Boltzmann factors,
each positive-definite on `SU(N)⁴` (proven: `plaquetteBoltzmannPD_inv`).  By the Schur
product theorem (`PositiveDefinite.finprod`), the full Boltzmann is positive-definite
on the link group `G = SU(N)^{allLinks}`.  This is the key building block for the
spatial hopping operator V in the Lüscher decomposition T = V^{1/2}·U·V^{1/2}.
See `docs/transfer_matrix_positivity_design.md` §8.11.67. -/


theorem fullBoltzmannPD (N T L : ℕ) [NeZero T] [NeZero L] (β : ℝ) (hβ : 0 ≤ β) :
    PositiveDefinite (fun (U : LinkVariable (SU N) (PeriodicSite T L)) =>
      (Real.exp (-β * wilsonActionFinite N β (Finset.univ : Finset (PeriodicSite T L)) U) : ℂ)) := by
  -- Step 1: Obtain the product form from full_boltzmann_eq_abstract_product
  obtain ⟨C, hC_pos, h_eq⟩ := full_boltzmann_eq_abstract_product N T L β
  -- Step 2: The coupling constant c = β²/N ≥ 0
  set c := β * β / N
  have hc : 0 ≤ c := div_nonneg (mul_self_nonneg β) (Nat.cast_nonneg _)
  -- Step 3: For each plaquette p, the plaquette factor is PD.
  -- We use PositiveDefinite.congr (not convert/exact) to avoid the whnf timeout
  -- caused by addVectorPeriodic's match on Fin 4 (which gets stuck when the
  -- direction μ is a variable).  The function equality is proved by funext + simp
  -- (which handles the stuck match via equational rewriting), then PD is transferred.
  let φ (q : ((SU N × SU N) × SU N) × SU N) : ℂ :=
    (Real.exp (c * (Matrix.trace ((q.1.1.1 * q.1.1.2 * q.1.2⁻¹ * q.2⁻¹ : SU N) :
      Matrix (Fin N) (Fin N) ℂ)).re) : ℂ)
  have hφ : PositiveDefinite φ := plaquetteBoltzmannPD_inv N c hc
  have hφ_PD : ∀ (p : PlaquetteIndex T L), PositiveDefinite
      (fun (U : LinkVariable (SU N) (PeriodicSite T L)) =>
        (Real.exp (c * Complex.re (Matrix.trace
          ((plaquetteProduct N U p.1 p.2.1 p.2.2 : SU N) :
            Matrix (Fin N) (Fin N) ℂ))) : ℂ)) := by
    intro p
    have hcomp : PositiveDefinite (fun g => φ (plaquetteProjection N p.1 p.2.1 p.2.2 g)) :=
      PositiveDefinite.comp_hom (plaquetteProjection N p.1 p.2.1 p.2.2) hφ
    have hfun : (fun (U : LinkVariable (SU N) (PeriodicSite T L)) =>
        (Real.exp (c * Complex.re (Matrix.trace
          ((plaquetteProduct N U p.1 p.2.1 p.2.2 : SU N) :
            Matrix (Fin N) (Fin N) ℂ))) : ℂ)) =
        (fun g => φ (plaquetteProjection N p.1 p.2.1 p.2.2 g)) := by
      funext U
      show (Real.exp (c * Complex.re (Matrix.trace
        ((plaquetteProduct N U p.1 p.2.1 p.2.2 : SU N) :
          Matrix (Fin N) (Fin N) ℂ))) : ℂ) =
        (Real.exp (c * (Matrix.trace
          (((plaquetteProjection N p.1 p.2.1 p.2.2 U).1.1.1 *
            (plaquetteProjection N p.1 p.2.1 p.2.2 U).1.1.2 *
            (plaquetteProjection N p.1 p.2.1 p.2.2 U).1.2⁻¹ *
            (plaquetteProjection N p.1 p.2.1 p.2.2 U).2⁻¹ : SU N) :
            Matrix (Fin N) (Fin N) ℂ)).re) : ℂ)
      simp only [plaquetteProjection, plaquetteProduct, MonoidHom.coe_mk, Complex.re]
      rfl
    exact PositiveDefinite.congr hfun hcomp
  -- Step 4: The product of PD functions is PD (Schur product theorem).
  -- Use congr to avoid the whnf timeout caused by addVectorPeriodic's stuck
  -- match on Fin 4.  Build hprod_PD' WITHOUT a declared type (so no conclusion
  -- defeq check against the ∏ notation), then transfer PD with congr + funext.
  -- The funext goal is alpha-equivalent (renaming bound variables), so rfl is
  -- fast — isDefEq confirms structural equality without unfolding plaquetteProduct.
  have hprod_PD' := PositiveDefinite.finprod Finset.univ
    (fun (p : PlaquetteIndex T L) (U : LinkVariable (SU N) (PeriodicSite T L)) =>
      (Real.exp (c * Complex.re (Matrix.trace
        ((plaquetteProduct N U p.1 p.2.1 p.2.2 : SU N) :
          Matrix (Fin N) (Fin N) ℂ))) : ℂ))
    (fun p _ => hφ_PD p)
  have hprod_PD : PositiveDefinite (fun (U : LinkVariable (SU N) (PeriodicSite T L)) =>
    (∏ p : PlaquetteIndex T L,
      (Real.exp (c * Complex.re (Matrix.trace
        ((plaquetteProduct N U p.1 p.2.1 p.2.2 : SU N) :
          Matrix (Fin N) (Fin N) ℂ))) : ℂ))) := by
    apply PositiveDefinite.congr _ hprod_PD'
    funext U
    rfl
  -- Step 5: C times the product is PD (C ≥ 0).  Same congr pattern.
  have hCprod_PD' := PositiveDefinite.smul_nonneg (le_of_lt hC_pos) hprod_PD
  have hCprod_PD : PositiveDefinite (fun (U : LinkVariable (SU N) (PeriodicSite T L)) =>
    ((C : ℂ) * ∏ p : PlaquetteIndex T L,
      (Real.exp (c * Complex.re (Matrix.trace
        ((plaquetteProduct N U p.1 p.2.1 p.2.2 : SU N) :
          Matrix (Fin N) (Fin N) ℂ))) : ℂ))) := by
    apply PositiveDefinite.congr _ hCprod_PD'
    funext U
    rfl
  -- Step 6: The full Boltzmann equals C times the product (pointwise).
  have hfun_final : (fun (U : LinkVariable (SU N) (PeriodicSite T L)) =>
      (Real.exp (-β * wilsonActionFinite N β (Finset.univ : Finset (PeriodicSite T L)) U) : ℂ)) =
    (fun (U : LinkVariable (SU N) (PeriodicSite T L)) =>
      ((C : ℂ) * ∏ p : PlaquetteIndex T L,
        (Real.exp (c * Complex.re (Matrix.trace
          ((plaquetteProduct N U p.1 p.2.1 p.2.2 : SU N) :
            Matrix (Fin N) (Fin N) ℂ))) : ℂ))) := by
    funext U
    exact_mod_cast h_eq U
  exact PositiveDefinite.congr hfun_final hCprod_PD

#print axioms fullBoltzmannPD

/-! ## Spatial/temporal plaquette decomposition (Lüscher decomposition §8.11.67)

The Lüscher decomposition T = V^{1/2}·U·V^{1/2} requires splitting the Wilson action
into spatial plaquettes (both directions nonzero — plaquettes within a single time
slice) and temporal plaquettes (at least one direction is the time direction 0 —
plaquettes spanning two adjacent time slices).  The spatial plaquettes give the
positive multiplication operator V (PD by the Schur product theorem), and the
temporal plaquettes give the integral operator U (positive by the Lüscher cascade
+ `character_kernel_integral_nonneg`).
See `docs/transfer_matrix_positivity_design.md` §8.11.67. -/

/-- A plaquette is **spatial** if both directions are nonzero (μ ≠ 0 and ν ≠ 0).
Such a plaquette lies entirely within a single time slice. -/
def isSpatialPlaquette {T L : ℕ} (p : PlaquetteIndex T L) : Prop :=
  p.2.1 ≠ 0 ∧ p.2.2 ≠ 0

/-- A plaquette is **temporal** if at least one direction is the time direction 0
(μ = 0 or ν = 0).  Such a plaquette spans two adjacent time slices. -/
def isTemporalPlaquette {T L : ℕ} (p : PlaquetteIndex T L) : Prop :=
  p.2.1 = 0 ∨ p.2.2 = 0

/-- The set of spatial plaquettes (both directions nonzero). -/
def spatialPlaquettes (T L : ℕ) [NeZero T] [NeZero L] : Finset (PlaquetteIndex T L) :=
  Finset.univ.filter (fun p => p.2.1 ≠ 0 ∧ p.2.2 ≠ 0)

/-- The set of temporal plaquettes (at least one direction is 0). -/
def temporalPlaquettes (T L : ℕ) [NeZero T] [NeZero L] : Finset (PlaquetteIndex T L) :=
  Finset.univ.filter (fun p => p.2.1 = 0 ∨ p.2.2 = 0)

/-- Membership in `spatialPlaquettes`: both directions nonzero. -/
lemma spatialPlaquettes_mem_iff (T L : ℕ) [NeZero T] [NeZero L]
    (p : PlaquetteIndex T L) :
    p ∈ spatialPlaquettes T L ↔ p.2.1 ≠ 0 ∧ p.2.2 ≠ 0 := by
  unfold spatialPlaquettes
  simp [Finset.mem_filter, Finset.mem_univ]

/-- Membership in `temporalPlaquettes`: at least one direction is 0. -/
lemma temporalPlaquettes_mem_iff (T L : ℕ) [NeZero T] [NeZero L]
    (p : PlaquetteIndex T L) :
    p ∈ temporalPlaquettes T L ↔ p.2.1 = 0 ∨ p.2.2 = 0 := by
  unfold temporalPlaquettes
  simp [Finset.mem_filter, Finset.mem_univ]

/-- Spatial and temporal plaquettes partition all plaquettes (disjoint + cover). -/
lemma spatial_temporal_plaquette_partition (T L : ℕ) [NeZero T] [NeZero L] :
    Disjoint (spatialPlaquettes T L) (temporalPlaquettes T L) ∧
    spatialPlaquettes T L ∪ temporalPlaquettes T L = Finset.univ := by
  refine ⟨?_, ?_⟩
  · refine Finset.disjoint_left.mpr (fun p hp hp' => ?_)
    rw [spatialPlaquettes_mem_iff] at hp
    rw [temporalPlaquettes_mem_iff] at hp'
    cases hp' with
    | inl h => exact hp.1 h
    | inr h => exact hp.2 h
  · ext p
    simp only [Finset.mem_union, spatialPlaquettes_mem_iff, temporalPlaquettes_mem_iff,
      Finset.mem_univ]
    tauto

/-- The spatial part of the Wilson action: sum over spatial plaquettes only. -/
noncomputable def wilsonActionSpatial (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) : ℝ :=
  ∑ p ∈ spatialPlaquettes T L, plaquetteContribution N β U p.1 p.2.1 p.2.2

/-- The temporal part of the Wilson action: sum over temporal plaquettes only. -/
noncomputable def wilsonActionTemporal (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) : ℝ :=
  ∑ p ∈ temporalPlaquettes T L, plaquetteContribution N β U p.1 p.2.1 p.2.2

/-- **Spatial/temporal plaquette decomposition of the Wilson action.**
`S_W = S_spatial + S_temporal` where `S_spatial` is the sum over spatial plaquettes
(both directions nonzero) and `S_temporal` is the sum over temporal plaquettes
(at least one direction is the time direction 0).  This is sub-step 1 of the
Lüscher decomposition T = V^{1/2}·U·V^{1/2} (§8.11.67). -/
lemma wilsonActionFinite_eq_spatial_plus_temporal (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) :
    wilsonActionFinite N β (Finset.univ : Finset (PeriodicSite T L)) U =
      wilsonActionSpatial N T L β U + wilsonActionTemporal N T L β U := by
  -- Step 1: Convert wilsonActionFinite to a sum over PlaquetteIndex.
  -- wilsonActionFinite N β Finset.univ U = ∑ n, ∑ μ, ∑ ν, plaquetteContribution N β U n μ ν
  -- Merge the three nested sums into one over PlaquetteIndex T L (right-associated).
  have h_eq : wilsonActionFinite N β (Finset.univ : Finset (PeriodicSite T L)) U =
      ∑ p : PlaquetteIndex T L, plaquetteContribution N β U p.1 p.2.1 p.2.2 := by
    simp only [Lattice.wilsonActionFinite]
    -- ∑ n ∈ Finset.univ, ∑ μ, ∑ ν, plaquetteContribution N β U n μ ν
    -- = ∑ p : PlaquetteIndex T L, plaquetteContribution N β U p.1 p.2.1 p.2.2
    -- Use the same pattern as prod_if_interface_eq_prod_subtype:
    -- ← Fintype.sum_prod_type' merges nested Fintype sums into a product-type sum.
    simp only [← Fintype.sum_prod_type']
  -- Step 2: Split by the spatial/temporal partition.
  rw [h_eq]
  have ⟨hdisj, hcover⟩ := spatial_temporal_plaquette_partition T L
  rw [← hcover, Finset.sum_union hdisj]
  rfl

#print axioms wilsonActionFinite_eq_spatial_plus_temporal

/-! ## Spatial Boltzmann factor positive-definiteness (V operator, Lüscher §8.11.67)

The spatial Boltzmann factor `exp(-β·S_spatial)` is a product of spatial plaquette
Boltzmann factors, each PD on `SU(N)⁴` (proven: `plaquetteBoltzmannPD_inv`).  By the
Schur product theorem (`PositiveDefinite.finprod`), the spatial Boltzmann is PD on
the link group `G = SU(N)^{allLinks}`.  This is the key building block for the
spatial hopping operator V in the Lüscher decomposition T = V^{1/2}·U·V^{1/2}.
See `docs/transfer_matrix_positivity_design.md` §8.11.67. -/

/-- **Spatial Boltzmann factor as a positive constant times the abstract spatial
plaquette product.** The spatial Boltzmann factor `exp(-β·S_spatial)` equals a
positive constant `C = ∏_{p ∈ spatialPlaquettes} exp(-β²)` times the abstract
plaquette product `∏_{p ∈ spatialPlaquettes} exp((β²/N)·Re Tr(P_p))`.
This is the spatial analogue of `full_boltzmann_eq_abstract_product`.
Pure algebra — 0 sorries, 0 custom axioms. -/
lemma spatial_boltzmann_eq_abstract_product (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L] :
    ∃ (C : ℝ) (hC : 0 < C),
      ∀ (U : LinkVariable (SU N) (PeriodicSite T L)),
      Real.exp (-β * wilsonActionSpatial N T L β U) =
        C * ∏ p ∈ spatialPlaquettes T L,
          Real.exp ((β * β / N) * Complex.re (Matrix.trace
            ((plaquetteProduct N U p.1 p.2.1 p.2.2 : SU N) :
              Matrix (Fin N) (Fin N) ℂ))) := by
  set C := ∏ p ∈ spatialPlaquettes T L, Real.exp (-(β * β))
  refine ⟨C, ?_, fun U => ?_⟩
  · exact Finset.prod_pos (fun p _ => plaquetteBoltzmann_tm_const_pos β)
  · -- exp(-β·S_spatial) = ∏_{p ∈ spatial} exp(-β·plaquetteContribution)
    have h_exp_sum : Real.exp (-β * wilsonActionSpatial N T L β U) =
        ∏ p ∈ spatialPlaquettes T L,
          Real.exp (-β * plaquetteContribution N β U p.1 p.2.1 p.2.2) := by
      show Real.exp (-β * ∑ p ∈ spatialPlaquettes T L, plaquetteContribution N β U p.1 p.2.1 p.2.2) =
        ∏ p ∈ spatialPlaquettes T L, Real.exp (-β * plaquetteContribution N β U p.1 p.2.1 p.2.2)
      rw [Finset.mul_sum, Real.exp_sum]
    rw [h_exp_sum]
    -- Per-plaquette: exp(-β·plaquetteContribution) = exp(-β²)·exp((β²/N)·Re Tr)
    simp only [plaquetteContribution_exp_decomp_tm]
    rw [Finset.prod_mul_distrib]

#print axioms spatial_boltzmann_eq_abstract_product

/-- **The spatial Boltzmann factor is positive-definite.** The spatial Boltzmann
factor `exp(-β·S_spatial)` is a product of spatial plaquette Boltzmann factors,
each PD on `SU(N)⁴` (proven: `plaquetteBoltzmannPD_inv`).  By the Schur product
theorem (`PositiveDefinite.finprod`), the spatial Boltzmann is PD on the link
group `G = SU(N)^{allLinks}`.  This is sub-step 2 of the Lüscher decomposition
(§8.11.67): V (the spatial hopping operator) is a positive multiplication
operator because the spatial Boltzmann factor is PD. -/
theorem spatialBoltzmannPD (N T L : ℕ) [NeZero T] [NeZero L] (β : ℝ) (hβ : 0 ≤ β) :
    PositiveDefinite (fun (U : LinkVariable (SU N) (PeriodicSite T L)) =>
      (Real.exp (-β * wilsonActionSpatial N T L β U) : ℂ)) := by
  -- Step 1: Obtain the product form from spatial_boltzmann_eq_abstract_product
  obtain ⟨C, hC_pos, h_eq⟩ := spatial_boltzmann_eq_abstract_product N T L β
  -- Step 2: The coupling constant c = β²/N ≥ 0
  set c := β * β / N
  have hc : 0 ≤ c := div_nonneg (mul_self_nonneg β) (Nat.cast_nonneg _)
  -- Step 3: For each spatial plaquette p, the plaquette factor is PD.
  -- Use PositiveDefinite.congr to avoid the whnf timeout caused by
  -- addVectorPeriodic's match on Fin 4 (same technique as fullBoltzmannPD).
  let φ (q : ((SU N × SU N) × SU N) × SU N) : ℂ :=
    (Real.exp (c * (Matrix.trace ((q.1.1.1 * q.1.1.2 * q.1.2⁻¹ * q.2⁻¹ : SU N) :
      Matrix (Fin N) (Fin N) ℂ)).re) : ℂ)
  have hφ : PositiveDefinite φ := plaquetteBoltzmannPD_inv N c hc
  have hφ_PD : ∀ (p : PlaquetteIndex T L), PositiveDefinite
      (fun (U : LinkVariable (SU N) (PeriodicSite T L)) =>
        (Real.exp (c * Complex.re (Matrix.trace
          ((plaquetteProduct N U p.1 p.2.1 p.2.2 : SU N) :
            Matrix (Fin N) (Fin N) ℂ))) : ℂ)) := by
    intro p
    have hcomp : PositiveDefinite (fun g => φ (plaquetteProjection N p.1 p.2.1 p.2.2 g)) :=
      PositiveDefinite.comp_hom (plaquetteProjection N p.1 p.2.1 p.2.2) hφ
    have hfun : (fun (U : LinkVariable (SU N) (PeriodicSite T L)) =>
        (Real.exp (c * Complex.re (Matrix.trace
          ((plaquetteProduct N U p.1 p.2.1 p.2.2 : SU N) :
            Matrix (Fin N) (Fin N) ℂ))) : ℂ)) =
        (fun g => φ (plaquetteProjection N p.1 p.2.1 p.2.2 g)) := by
      funext U
      show (Real.exp (c * Complex.re (Matrix.trace
        ((plaquetteProduct N U p.1 p.2.1 p.2.2 : SU N) :
          Matrix (Fin N) (Fin N) ℂ))) : ℂ) =
        (Real.exp (c * (Matrix.trace
          (((plaquetteProjection N p.1 p.2.1 p.2.2 U).1.1.1 *
            (plaquetteProjection N p.1 p.2.1 p.2.2 U).1.1.2 *
            (plaquetteProjection N p.1 p.2.1 p.2.2 U).1.2⁻¹ *
            (plaquetteProjection N p.1 p.2.1 p.2.2 U).2⁻¹ : SU N) :
            Matrix (Fin N) (Fin N) ℂ)).re) : ℂ)
      simp only [plaquetteProjection, plaquetteProduct, MonoidHom.coe_mk, Complex.re]
      rfl
    exact PositiveDefinite.congr hfun hcomp
  -- Step 4: The product of PD functions over spatial plaquettes is PD (Schur product).
  -- Use congr to avoid the whnf timeout caused by addVectorPeriodic's stuck match.
  have hprod_PD' := PositiveDefinite.finprod (spatialPlaquettes T L)
    (fun (p : PlaquetteIndex T L) (U : LinkVariable (SU N) (PeriodicSite T L)) =>
      (Real.exp (c * Complex.re (Matrix.trace
        ((plaquetteProduct N U p.1 p.2.1 p.2.2 : SU N) :
          Matrix (Fin N) (Fin N) ℂ))) : ℂ))
    (fun p _ => hφ_PD p)
  have hprod_PD : PositiveDefinite (fun (U : LinkVariable (SU N) (PeriodicSite T L)) =>
    (∏ p ∈ spatialPlaquettes T L,
      (Real.exp (c * Complex.re (Matrix.trace
        ((plaquetteProduct N U p.1 p.2.1 p.2.2 : SU N) :
          Matrix (Fin N) (Fin N) ℂ))) : ℂ))) := by
    apply PositiveDefinite.congr _ hprod_PD'
    funext U
    rfl
  -- Step 5: C times the product is PD (C ≥ 0).
  have hCprod_PD' := PositiveDefinite.smul_nonneg (le_of_lt hC_pos) hprod_PD
  have hCprod_PD : PositiveDefinite (fun (U : LinkVariable (SU N) (PeriodicSite T L)) =>
    ((C : ℂ) * ∏ p ∈ spatialPlaquettes T L,
      (Real.exp (c * Complex.re (Matrix.trace
        ((plaquetteProduct N U p.1 p.2.1 p.2.2 : SU N) :
          Matrix (Fin N) (Fin N) ℂ))) : ℂ))) := by
    apply PositiveDefinite.congr _ hCprod_PD'
    funext U
    rfl
  -- Step 6: The spatial Boltzmann equals C times the product (pointwise).
  have hfun_final : (fun (U : LinkVariable (SU N) (PeriodicSite T L)) =>
      (Real.exp (-β * wilsonActionSpatial N T L β U) : ℂ)) =
    (fun (U : LinkVariable (SU N) (PeriodicSite T L)) =>
      ((C : ℂ) * ∏ p ∈ spatialPlaquettes T L,
        (Real.exp (c * Complex.re (Matrix.trace
          ((plaquetteProduct N U p.1 p.2.1 p.2.2 : SU N) :
            Matrix (Fin N) (Fin N) ℂ))) : ℂ))) := by
    funext U
    exact_mod_cast h_eq U
  exact PositiveDefinite.congr hfun_final hCprod_PD

#print axioms spatialBoltzmannPD

/-! ## Temporal Boltzmann factor: abstract product form (U operator, Lüscher §8.11.67)

The temporal Boltzmann factor `exp(-β·S_temporal)` is a product of temporal plaquette
Boltzmann factors.  Unlike the spatial case (where the product is kept as a PD function
defining the multiplication operator V), the temporal plaquette product is expanded
in characters (sub-step 3 of the Lüscher decomposition) and the temporal links are
integrated out via the Lüscher cascade, producing a kernel `Σ_s a_s · χ_s(W·V)` with
`a_s ≥ 0`.  This lemma gives the abstract product form (pure algebra); the character
expansion is a separate lemma.
See `docs/transfer_matrix_positivity_design.md` §8.11.67. -/

/-- **Temporal Boltzmann factor as a positive constant times the abstract temporal
plaquette product.** The temporal Boltzmann factor `exp(-β·S_temporal)` equals a
positive constant `C = ∏_{p ∈ temporalPlaquettes} exp(-β²)` times the abstract
plaquette product `∏_{p ∈ temporalPlaquettes} exp((β²/N)·Re Tr(P_p))`.
This is the temporal analogue of `spatial_boltzmann_eq_abstract_product`.
Pure algebra — 0 sorries, 0 custom axioms. -/
lemma temporal_boltzmann_eq_abstract_product (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L] :
    ∃ (C : ℝ) (hC : 0 < C),
      ∀ (U : LinkVariable (SU N) (PeriodicSite T L)),
      Real.exp (-β * wilsonActionTemporal N T L β U) =
        C * ∏ p ∈ temporalPlaquettes T L,
          Real.exp ((β * β / N) * Complex.re (Matrix.trace
            ((plaquetteProduct N U p.1 p.2.1 p.2.2 : SU N) :
              Matrix (Fin N) (Fin N) ℂ))) := by
  set C := ∏ p ∈ temporalPlaquettes T L, Real.exp (-(β * β))
  refine ⟨C, ?_, fun U => ?_⟩
  · exact Finset.prod_pos (fun p _ => plaquetteBoltzmann_tm_const_pos β)
  · have h_exp_sum : Real.exp (-β * wilsonActionTemporal N T L β U) =
        ∏ p ∈ temporalPlaquettes T L,
          Real.exp (-β * plaquetteContribution N β U p.1 p.2.1 p.2.2) := by
      show Real.exp (-β * ∑ p ∈ temporalPlaquettes T L, plaquetteContribution N β U p.1 p.2.1 p.2.2) =
        ∏ p ∈ temporalPlaquettes T L, Real.exp (-β * plaquetteContribution N β U p.1 p.2.1 p.2.2)
      rw [Finset.mul_sum, Real.exp_sum]
    rw [h_exp_sum]
    simp only [plaquetteContribution_exp_decomp_tm]
    rw [Finset.prod_mul_distrib]

#print axioms temporal_boltzmann_eq_abstract_product

/-! ## Temporal plaquette link infrastructure (Lüscher §8.11.67 sub-step 3b)

The temporal plaquette product needs to be expanded in characters.  This requires
defining the temporal plaquette subtype, the temporal link subtype (links appearing
in temporal plaquettes), the link assignment, and a partition of the temporal links
into positive-time spatial (L_U, "W"), temporal + interface (L_0, internal), and
negative-time spatial (L_V, "V").  This is the temporal analogue of the interface
link infrastructure (`InterfacePlaquette`, `InterfaceLink`, `interfaceLinkAssign`).
The temporal links (μ = 0) are internal — to be integrated out by the Lüscher cascade
in sub-step 3c.  The spatial links (μ ≠ 0) at positive/negative time are external —
the kernel variables W and V. -/

/-- Temporal plaquettes as a subtype of `PlaquetteIndex`. -/
abbrev TemporalPlaquette (T L : ℕ) [NeZero T] [NeZero L] : Type :=
  {p : PlaquetteIndex T L // isTemporalPlaquette p}

noncomputable instance (T L : ℕ) [NeZero T] [NeZero L] : Fintype (TemporalPlaquette T L) := by
  classical
  exact inferInstanceAs (Fintype {p : PlaquetteIndex T L // isTemporalPlaquette p})

instance (T L : ℕ) [NeZero T] [NeZero L] : DecidableEq (TemporalPlaquette T L) :=
  inferInstanceAs (DecidableEq {p : PlaquetteIndex T L // isTemporalPlaquette p})

/-- The Finset of all links appearing in at least one temporal plaquette. -/
noncomputable def temporalPlaqLinkFinset (T L : ℕ) [NeZero T] [NeZero L] :
    Finset (PeriodicSite T L × Fin 4) :=
  (Finset.univ : Finset (TemporalPlaquette T L × Fin 4)).image
    (fun x => plaquetteLinkIdx T L x.1.val x.2)

/-- The type of links appearing in temporal plaquettes (subtype).  This is the
concrete `L` for `interface_kernel_character_expansion`: by construction, every
link in this type appears in at least one temporal plaquette, so the
surjectivity hypothesis `hlinks_surj` holds. -/
abbrev TemporalLink (T L : ℕ) [NeZero T] [NeZero L] : Type :=
  {l : PeriodicSite T L × Fin 4 // l ∈ temporalPlaqLinkFinset T L}

noncomputable instance (T L : ℕ) [NeZero T] [NeZero L] : Fintype (TemporalLink T L) := by
  classical
  exact inferInstanceAs (Fintype {l : PeriodicSite T L × Fin 4 //
    l ∈ temporalPlaqLinkFinset T L})

instance (T L : ℕ) [NeZero T] [NeZero L] : DecidableEq (TemporalLink T L) :=
  inferInstanceAs (DecidableEq {l : PeriodicSite T L × Fin 4 //
    l ∈ temporalPlaqLinkFinset T L})

/-- The link assignment `TemporalPlaquette → Fin 4 → TemporalLink`.  Maps each
plaquette `p` and index `j` to the j-th link of `p`, packaged as a
`TemporalLink` (with the proof that it appears in a temporal plaquette). -/
def temporalLinkAssign (T L : ℕ) [NeZero T] [NeZero L]
    (p : TemporalPlaquette T L) (j : Fin 4) : TemporalLink T L :=
  ⟨plaquetteLinkIdx T L p.val j, by
    simp only [temporalPlaqLinkFinset, Finset.mem_image, Finset.mem_univ, true_and,
      Prod.exists, exists_prop]
    exact ⟨p, j, rfl⟩⟩

/-- The link assignment is surjective: every `TemporalLink` arises as some
plaquette's j-th link.  This is the `hlinks_surj` hypothesis for
`interface_kernel_character_expansion`. -/
lemma temporalLinkAssign_surj (T L : ℕ) [NeZero T] [NeZero L] :
    ∀ l : TemporalLink T L, ∃ p j, temporalLinkAssign T L p j = l := by
  intro l
  have hl : l.val ∈ temporalPlaqLinkFinset T L := l.prop
  simp only [temporalPlaqLinkFinset, Finset.mem_image, Finset.mem_univ, true_and,
    Prod.exists, exists_prop] at hl
  obtain ⟨p, j, hj⟩ := hl
  refine ⟨p, j, ?_⟩
  simp only [temporalLinkAssign, Subtype.mk_eq_mk, hj]

/-- Extract the link variable `U(n, μ)` from a full configuration at a
`TemporalLink` `l = (n, μ)`. -/
def temporalLinkVar (N T L : ℕ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) (l : TemporalLink T L) : SU N :=
  U.value l.val.1 l.val.2

/-- The plaquette product of a temporal plaquette equals the abstract form
`g(links p 0)·g(links p 1)·g(links p 2)⁻¹·g(links p 3)⁻¹` where `g` extracts
link variables via `temporalLinkVar`. -/
lemma plaquetteProduct_temporal_eq (N T L : ℕ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) (p : TemporalPlaquette T L) :
    plaquetteProduct N U p.val.1 p.val.2.1 p.val.2.2 =
    temporalLinkVar N T L U (temporalLinkAssign T L p 0) *
    temporalLinkVar N T L U (temporalLinkAssign T L p 1) *
    (temporalLinkVar N T L U (temporalLinkAssign T L p 2))⁻¹ *
    (temporalLinkVar N T L U (temporalLinkAssign T L p 3))⁻¹ := by
  unfold temporalLinkVar temporalLinkAssign
  exact plaquetteProduct_eq_linkIdx N T L U p.val

/-- The positive-time spatial links among temporal links (L_U, "W").
These are spatial links (μ ≠ 0) at positive signed time — the external "W"
variables of the Lüscher kernel. -/
noncomputable def temporalLinkPos (T L : ℕ) [NeZero T] [NeZero L] :
    Finset (TemporalLink T L) :=
  (Finset.univ : Finset (TemporalLink T L)).filter
    (fun l => signedTime T l.val.1.time > 0 ∧ l.val.2 ≠ 0)

/-- The temporal + interface links among temporal links (L_0, internal).
These are temporal links (μ = 0, at any time) OR spatial links at the interface
(signedTime = 0) — the internal links to be integrated out by the Lüscher cascade. -/
noncomputable def temporalLinkInt (T L : ℕ) [NeZero T] [NeZero L] :
    Finset (TemporalLink T L) :=
  (Finset.univ : Finset (TemporalLink T L)).filter
    (fun l => l.val.2 = 0 ∨ signedTime T l.val.1.time = 0)

/-- The negative-time spatial links among temporal links (L_V, "V").
These are spatial links (μ ≠ 0) at negative signed time — the external "V"
variables of the Lüscher kernel. -/
noncomputable def temporalLinkNeg (T L : ℕ) [NeZero T] [NeZero L] :
    Finset (TemporalLink T L) :=
  (Finset.univ : Finset (TemporalLink T L)).filter
    (fun l => signedTime T l.val.1.time < 0 ∧ l.val.2 ≠ 0)

/-- The three temporal link sets are pairwise disjoint and cover all temporal links.
The partition separates:
- L_U: spatial links (μ ≠ 0) at positive time (external "W")
- L_0: temporal links (μ = 0) at any time, or spatial links at the interface (internal)
- L_V: spatial links (μ ≠ 0) at negative time (external "V")
Disjointness: L_U and L_0 are disjoint (L_U requires μ ≠ 0 and signedTime > 0,
which contradicts both μ = 0 and signedTime = 0).  (L_U ∪ L_0) and L_V are disjoint
(L_V requires signedTime < 0, contradicting L_U's signedTime > 0 and L_0's
signedTime = 0 or μ = 0).  Cover: by signedTime trichotomy and μ = 0 / μ ≠ 0 cases. -/
lemma temporalLinkPartition_disjoint_cover (T L : ℕ) [NeZero T] [NeZero L] :
    Disjoint (temporalLinkPos T L) (temporalLinkInt T L) ∧
    Disjoint (temporalLinkPos T L ∪ temporalLinkInt T L) (temporalLinkNeg T L) ∧
    temporalLinkPos T L ∪ temporalLinkInt T L ∪ temporalLinkNeg T L = Finset.univ := by
  refine ⟨?_, ?_, ?_⟩
  · -- Disjoint L_U L_0
    refine Finset.disjoint_left.mpr (fun l hl hl' => ?_)
    rw [temporalLinkPos, Finset.mem_filter] at hl
    rw [temporalLinkInt, Finset.mem_filter] at hl'
    obtain ⟨_, hpos, hne⟩ := hl
    obtain ⟨_, hint⟩ := hl'
    rcases hint with hμ | htime
    · exact hne hμ
    · omega
  · -- Disjoint (L_U ∪ L_0) L_V
    refine Finset.disjoint_left.mpr (fun l hl hl' => ?_)
    rw [temporalLinkNeg, Finset.mem_filter] at hl'
    obtain ⟨_, hneg, hne⟩ := hl'
    rcases Finset.mem_union.mp hl with h | h
    · rw [temporalLinkPos, Finset.mem_filter] at h
      obtain ⟨_, hpos, _⟩ := h
      omega
    · rw [temporalLinkInt, Finset.mem_filter] at h
      obtain ⟨_, hint⟩ := h
      rcases hint with hμ | htime
      · exact hne hμ
      · omega
  · -- Cover
    ext l
    simp only [temporalLinkPos, temporalLinkInt, temporalLinkNeg, Finset.mem_union,
      Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    by_cases hμ : l.val.2 = 0
    · left; right; left; exact hμ
    · rcases signedTime_trichotomy T l.val.1.time with hpos | hzero | hneg
      · left; left; exact ⟨hpos, hμ⟩
      · left; right; right; exact hzero
      · right; exact ⟨hneg, hμ⟩

/-- The partition in the form required by `interface_kernel_character_expansion`:
`hdisj : Disjoint L_U L_0 ∧ Disjoint (L_U ∪ L_0) L_V`. -/
lemma temporalLinkPartition_hdisj (T L : ℕ) [NeZero T] [NeZero L] :
    Disjoint (temporalLinkPos T L) (temporalLinkInt T L) ∧
    Disjoint (temporalLinkPos T L ∪ temporalLinkInt T L) (temporalLinkNeg T L) :=
  ⟨temporalLinkPartition_disjoint_cover T L |>.1,
   temporalLinkPartition_disjoint_cover T L |>.2.1⟩

/-- The partition in the form required by `interface_kernel_character_expansion`:
`hcover : L_U ∪ L_0 ∪ L_V = Finset.univ`. -/
lemma temporalLinkPartition_hcover (T L : ℕ) [NeZero T] [NeZero L] :
    temporalLinkPos T L ∪ temporalLinkInt T L ∪ temporalLinkNeg T L = Finset.univ :=
  temporalLinkPartition_disjoint_cover T L |>.2.2

/-- **Character expansion of the temporal plaquette product.** Applying
`interface_kernel_character_expansion` (Peter-Weyl / Clebsch-Gordan) to the temporal
plaquettes, the temporal plaquette product
`∏_{p ∈ TemporalPlaquette} exp((β²/N)·Re Tr(P_p))` (viewed in `ℂ`) admits the
separable character expansion

    ∏_p exp(c·Re Tr(...)) = ∑_w F(w) · Φ_w(W) · Ψ_w(internal) · conj(Φ_w(V))

with `F(w) ≥ 0`, where `Φ_w(W) = ∏_{l ∈ L_U} χ_{w(l)}(U_l)` (positive-time spatial
links, the external "W" variables), `Ψ_w(internal) = ∏_{l ∈ L_0} χ_{w(l)}(U_l)`
(temporal + interface links, internal — to be integrated out by the Lüscher cascade
in sub-step 3c), and the V factor uses the dual map (negative-time spatial links,
the external "V" variables).
This is sub-step 3b of the Lüscher decomposition (§8.11.67): the temporal plaquette
product is expanded in characters, separating temporal links (internal) from spatial
links (external, the kernel variables W and V).
Uses the `peterWeyl_clebschGordan_plaquette` axiom (count 6); 0 sorries. -/
lemma temporal_product_character_expansion (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (hN : 1 ≤ N) :
    ∃ (ι : Type) (hι : Fintype ι) (dims : ι → ℕ)
      (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
      (hU : ∀ i, IsUnitaryRepresentation (ρ i))
      (hMeas : ∀ i, Measurable (repCharacter (ρ i)))
      (dual : ι → ι)
      (F : (TemporalLink T L → ι) → ℝ) (hF : ∀ w, 0 ≤ F w),
      ∀ (U : LinkVariable (SU N) (PeriodicSite T L)),
      ∏ p : TemporalPlaquette T L,
        (Real.exp ((β * β / N) * Complex.re (Matrix.trace
          ((plaquetteProduct N U p.val.1 p.val.2.1 p.val.2.2 : SU N) :
            Matrix (Fin N) (Fin N) ℂ))) : ℂ) =
        ∑ w : TemporalLink T L → ι, (F w : ℂ) *
          (∏ l ∈ temporalLinkPos T L, repCharacter (ρ (w l)) (temporalLinkVar N T L U l)) *
          (∏ l ∈ temporalLinkInt T L, repCharacter (ρ (w l)) (temporalLinkVar N T L U l)) *
          star (∏ l ∈ temporalLinkNeg T L, repCharacter (ρ (dual (w l))) (temporalLinkVar N T L U l)) := by
  obtain ⟨ι, hι, dims, ρ, hU, hMeas, hIrr, hDims, σ_0, hσ_0_dims, hσ_0_trivial, coeff, hcoeff, cg, hcg, hcg_decomp, dual, hdual,
      cgME, hcgME_decomp, hcgME_unitary, hcgME_cross_rep,
      Λ, hΛ, dimsΛ, ρΛ, hUΛ, hIrrΛ, hDimsΛ, emb, hemb, μ, hμ,
      cgMEΛ, hcgMEΛ_support, hexp4, hL2, hSchurΛ, hcgMEΛ_parts⟩ :=
    peterWeyl_clebschGordan_plaquette N (β * β / N) (plaquetteBoltzmann_tm_coupling_nonneg N β hN)
  letI : Fintype ι := hι
  classical
  obtain ⟨F, hF, hF_decomp⟩ := interface_kernel_character_expansion
    ρ hU coeff hcoeff cg hcg hcg_decomp dual hdual
    (β * β / N) (plaquetteBoltzmann_tm_coupling_nonneg N β hN) hexp4
    (TemporalPlaquette T L) (TemporalLink T L) (temporalLinkAssign T L)
    (temporalLinkAssign_surj T L)
    (temporalLinkPos T L) (temporalLinkInt T L) (temporalLinkNeg T L)
    (temporalLinkPartition_hdisj T L) (temporalLinkPartition_hcover T L)
  refine ⟨ι, hι, dims, ρ, hU, hMeas, dual, F, hF, fun U => ?_⟩
  have h := hF_decomp (temporalLinkVar N T L U)
  have h_eq : (∏ p : TemporalPlaquette T L,
      (Real.exp ((β * β / N) * Complex.re (Matrix.trace
        ((plaquetteProduct N U p.val.1 p.val.2.1 p.val.2.2 : SU N) :
          Matrix (Fin N) (Fin N) ℂ))) : ℂ)) =
      (∏ p : TemporalPlaquette T L,
      (Real.exp ((β * β / N) * Complex.re (Matrix.trace
        ((temporalLinkVar N T L U (temporalLinkAssign T L p 0) *
          temporalLinkVar N T L U (temporalLinkAssign T L p 1) *
          (temporalLinkVar N T L U (temporalLinkAssign T L p 2))⁻¹ *
          (temporalLinkVar N T L U (temporalLinkAssign T L p 3))⁻¹ : SU N) :
          Matrix (Fin N) (Fin N) ℂ))) : ℂ)) := by
    apply Finset.prod_congr rfl
    intro p _
    rw [plaquetteProduct_temporal_eq N T L U p]
  rw [h_eq]
  exact h

#print axioms temporal_product_character_expansion

/-! ## Character expansion of the full plaquette product.

Applying `interface_kernel_character_expansion` (Peter-Weyl / Clebsch-Gordan) to ALL
plaquettes (not just interface ones), the full plaquette product
`∏_{p ∈ PlaquetteIndex} exp((β²/N)·Re Tr(P_p))` (viewed in `ℂ`) admits the
separable character expansion

    ∏_p exp(c·Re Tr(...)) = ∑_w F(w) · Φ_w(U) · Ψ_w(U) · conj(Φ_w(U))

with `F(w) ≥ 0`, where `Φ_w(U) = ∏_{l ∈ allLinkPos} χ_{w(l)}(U.value l.1 l.2)`,
`Ψ_w(U) = ∏_{l ∈ allLinkInt} χ_{w(l)}(U.value l.1 l.2)`, and the negative-link
factor uses the dual (contragredient) map.
This is the full-lattice analogue of `interface_product_character_expansion`.
Uses the `peterWeyl_clebschGordan_plaquette` axiom (count 6); 0 sorries. -/
lemma full_product_character_expansion (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (hN : 1 ≤ N) :
    ∃ (ι : Type) (hι : Fintype ι) (dims : ι → ℕ)
      (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
      (hU : ∀ i, IsUnitaryRepresentation (ρ i))
      (hMeas : ∀ i, Measurable (repCharacter (ρ i)))
      (dual : ι → ι)
      (F : ((PeriodicSite T L × Fin 4) → ι) → ℝ) (hF : ∀ w, 0 ≤ F w),
      ∀ (U : LinkVariable (SU N) (PeriodicSite T L)),
      ∏ p : PlaquetteIndex T L,
        (Real.exp ((β * β / N) * Complex.re (Matrix.trace
          ((plaquetteProduct N U p.1 p.2.1 p.2.2 : SU N) :
            Matrix (Fin N) (Fin N) ℂ))) : ℂ) =
        ∑ w : (PeriodicSite T L × Fin 4) → ι, (F w : ℂ) *
          (∏ l ∈ allLinkPos T L, repCharacter (ρ (w l)) (U.value l.1 l.2)) *
          (∏ l ∈ allLinkInt T L, repCharacter (ρ (w l)) (U.value l.1 l.2)) *
          star (∏ l ∈ allLinkNeg T L, repCharacter (ρ (dual (w l))) (U.value l.1 l.2)) := by
  obtain ⟨ι, hι, dims, ρ, hU, hMeas, hIrr, hDims, σ_0, hσ_0_dims, hσ_0_trivial, coeff, hcoeff, cg, hcg, hcg_decomp, dual, hdual,
      cgME, hcgME_decomp, hcgME_unitary, hcgME_cross_rep,
      Λ, hΛ, dimsΛ, ρΛ, hUΛ, hIrrΛ, hDimsΛ, emb, hemb, μ, hμ,
      cgMEΛ, hcgMEΛ_support, hexp4, hL2, hSchurΛ, hcgMEΛ_parts⟩ :=
    peterWeyl_clebschGordan_plaquette N (β * β / N) (plaquetteBoltzmann_tm_coupling_nonneg N β hN)
  letI : Fintype ι := hι
  classical
  obtain ⟨F, hF, hF_decomp⟩ := interface_kernel_character_expansion
    ρ hU coeff hcoeff cg hcg hcg_decomp dual hdual
    (β * β / N) (plaquetteBoltzmann_tm_coupling_nonneg N β hN) hexp4
    (PlaquetteIndex T L) (PeriodicSite T L × Fin 4) (plaquetteLinkIdx T L)
    (plaquetteLinkIdx_surj T L)
    (allLinkPos T L) (allLinkInt T L) (allLinkNeg T L)
    (allLinkPartition_hdisj T L) (allLinkPartition_hcover T L)
  refine ⟨ι, hι, dims, ρ, hU, hMeas, dual, F, hF, fun U => ?_⟩
  have h := hF_decomp (fun l => U.value l.1 l.2)
  -- h : (∏ p, exp(...U.value(plaquetteLinkIdx p 0)·...·⁻¹)) = ∑ w, ...
  -- Goal: (∏ p, exp(...plaquetteProduct...)) = ∑ w, ...
  -- Rewrite plaquetteProduct in the goal to the linkIdx form via plaquetteProduct_eq_linkIdx.
  have h_eq : (∏ p : PlaquetteIndex T L,
      (Real.exp ((β * β / N) * Complex.re (Matrix.trace
        ((plaquetteProduct N U p.1 p.2.1 p.2.2 : SU N) :
          Matrix (Fin N) (Fin N) ℂ))) : ℂ)) =
      (∏ p : PlaquetteIndex T L,
      (Real.exp ((β * β / N) * Complex.re (Matrix.trace
        ((U.value (plaquetteLinkIdx T L p 0).1 (plaquetteLinkIdx T L p 0).2 *
          U.value (plaquetteLinkIdx T L p 1).1 (plaquetteLinkIdx T L p 1).2 *
          (U.value (plaquetteLinkIdx T L p 2).1 (plaquetteLinkIdx T L p 2).2)⁻¹ *
          (U.value (plaquetteLinkIdx T L p 3).1 (plaquetteLinkIdx T L p 3).2)⁻¹ : SU N) :
          Matrix (Fin N) (Fin N) ℂ))) : ℂ)) := by
    apply Finset.prod_congr rfl
    intro p _
    rw [plaquetteProduct_eq_linkIdx]
  rw [h_eq]
  exact h

#print axioms full_product_character_expansion

/-- **Combined character expansion of the full Boltzmann factor.** Composing
`full_boltzmann_eq_abstract_product` (exp(-β·S_W) = C · ∏_p exp(c·Re Tr(...)))
with `full_product_character_expansion` (∏_p exp(c·Re Tr(...)) = ∑_w F(w)·Φ_w·Ψ_w·V_w),
the full Boltzmann factor admits the character expansion (viewed in ℂ)

    (exp(-β·S_W(U)) : ℂ) = (C : ℂ) · ∑_w F(w) · Φ_w(U) · Ψ_w(U) · V_w(U)

with C > 0 and F(w) ≥ 0, where Φ_w(U) = ∏_{l ∈ allLinkPos} χ_{w(l)}(U.value l.1 l.2),
Ψ_w(U) = ∏_{l ∈ allLinkInt} χ_{w(l)}(U.value l.1 l.2),
V_w(U) = star(∏_{l ∈ allLinkNeg} χ_{dual(w(l))}(U.value l.1 l.2)).
This is the full-lattice analogue of `interface_boltzmann_character_expansion`.
Uses `peterWeyl_clebschGordan_plaquette` (axiom count 6, unchanged); 0 sorries. -/
lemma full_boltzmann_character_expansion (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (hN : 1 ≤ N) :
    ∃ (C : ℝ) (hC : 0 < C)
      (ι : Type) (hι : Fintype ι) (dims : ι → ℕ)
      (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
      (hU : ∀ i, IsUnitaryRepresentation (ρ i))
      (hMeas : ∀ i, Measurable (repCharacter (ρ i)))
      (dual : ι → ι)
      (F : ((PeriodicSite T L × Fin 4) → ι) → ℝ) (hF : ∀ w, 0 ≤ F w),
      ∀ (U : LinkVariable (SU N) (PeriodicSite T L)),
      (Real.exp (-β * wilsonActionFinite N β (Finset.univ : Finset (PeriodicSite T L)) U) : ℂ) =
        (C : ℂ) * ∑ w : (PeriodicSite T L × Fin 4) → ι, (F w : ℂ) *
          (∏ l ∈ allLinkPos T L, repCharacter (ρ (w l)) (U.value l.1 l.2)) *
          (∏ l ∈ allLinkInt T L, repCharacter (ρ (w l)) (U.value l.1 l.2)) *
          star (∏ l ∈ allLinkNeg T L, repCharacter (ρ (dual (w l))) (U.value l.1 l.2)) := by
  obtain ⟨C, hC, hC_eq_all⟩ := full_boltzmann_eq_abstract_product N T L β
  obtain ⟨ι, hι, dims, ρ, hU, hMeas, dual, F, hF, hF_decomp⟩ :=
    full_product_character_expansion N T L β hN
  letI : Fintype ι := hι
  classical
  refine ⟨C, hC, ι, hι, dims, ρ, hU, hMeas, dual, F, hF, fun U => ?_⟩
  rw [hC_eq_all U]
  have h := hF_decomp U
  norm_cast at h
  rw [Complex.ofReal_mul, h]

#print axioms full_boltzmann_character_expansion

/-! ### Bridge lemmas: link partition ↔ site partition

These lemmas connect the LINK-based partition (`interfaceLinkPos/Int/Neg`, used by
the character expansion) with the SITE-based partition
(`positiveSites/interfaceSites/negativeSites`, used by the measure factorization
in `TransferMatrix.lean`).  A link `(n, μ)` is in `interfaceLinkPos` iff its base
site `n` is in `positiveSites`, etc.  This compatibility is needed for sub-step
(iii) of Lemma 2 (Fubini reduction).  All 0 sorries, 0 custom axioms. -/

lemma interfaceLinkPos_mem_iff (T L : ℕ) [NeZero T] [NeZero L]
    (l : InterfaceLink T L) :
    l ∈ interfaceLinkPos T L ↔ l.val.1 ∈ positiveSites T L := by
  simp only [interfaceLinkPos, Finset.mem_filter, Finset.mem_univ, true_and,
    positiveSites]

lemma interfaceLinkInt_mem_iff (T L : ℕ) [NeZero T] [NeZero L]
    (l : InterfaceLink T L) :
    l ∈ interfaceLinkInt T L ↔ l.val.1 ∈ interfaceSites T L := by
  simp only [interfaceLinkInt, Finset.mem_filter, Finset.mem_univ, true_and,
    interfaceSites]

lemma interfaceLinkNeg_mem_iff (T L : ℕ) [NeZero T] [NeZero L]
    (l : InterfaceLink T L) :
    l ∈ interfaceLinkNeg T L ↔ l.val.1 ∈ negativeSites T L := by
  simp only [interfaceLinkNeg, Finset.mem_filter, Finset.mem_univ, true_and,
    negativeSites]

#print axioms interfaceLinkPos_mem_iff
#print axioms interfaceLinkInt_mem_iff
#print axioms interfaceLinkNeg_mem_iff


lemma reflectSite_addVector_comm (T L : ℕ) (n : PeriodicSite T L) (μ : Fin 4) (hμ0 : μ ≠ 0) :
    ReflectSite.reflectSite (AddVector.addVector n μ) =
    AddVector.addVector (ReflectSite.reflectSite n) μ := by
  -- For spatial directions (μ ≠ 0), reflection commutes with adding a basis vector
  fin_cases μ
  · -- μ = 0 is excluded by hμ0
    exfalso; exact hμ0 rfl
  · -- μ = 1 (x direction): adding e_x doesn't change time, so reflection commutes
    ext <;> simp [ReflectSite.reflectSite, AddVector.addVector, reflectSitePeriodic, addVectorPeriodic]
  · -- μ = 2 (y direction)
    ext <;> simp [ReflectSite.reflectSite, AddVector.addVector, reflectSitePeriodic, addVectorPeriodic]
  · -- μ = 3 (z direction)
    ext <;> simp [ReflectSite.reflectSite, AddVector.addVector, reflectSitePeriodic, addVectorPeriodic]

/-- For spatial directions (μ ≠ 0), addition and reflection commute at the level of
    the reflected site applied twice. -/
lemma reflectSite_addVector_comm_two (T L : ℕ) (n : PeriodicSite T L) (μ ν : Fin 4) (hμ0 : μ ≠ 0) (hν0 : ν ≠ 0) :
    ReflectSite.reflectSite (AddVector.addVector (AddVector.addVector n μ) ν) =
    AddVector.addVector (AddVector.addVector (ReflectSite.reflectSite n) μ) ν := by
  calc
    ReflectSite.reflectSite (AddVector.addVector (AddVector.addVector n μ) ν)
        = AddVector.addVector (ReflectSite.reflectSite (AddVector.addVector n μ)) ν :=
      reflectSite_addVector_comm T L (AddVector.addVector n μ) ν hν0
    _ = AddVector.addVector (AddVector.addVector (ReflectSite.reflectSite n) μ) ν := by
      rw [reflectSite_addVector_comm T L n μ hμ0]

lemma trace_plaquetteProduct_reflect_ss (N T L : ℕ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) (n : PeriodicSite T L) (μ ν : Fin 4)
    (hμ0 : μ ≠ 0) (hν0 : ν ≠ 0) :
    ((Matrix.trace ((plaquetteProduct N (reflectLinkVariable N U) (ReflectSite.reflectSite n) μ ν : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) =
    ((Matrix.trace ((plaquetteProduct N U n μ ν : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) := by
  have h_eq : plaquetteProduct N (reflectLinkVariable N U) (ReflectSite.reflectSite n) μ ν =
      plaquetteProduct N U n μ ν := by
    dsimp [plaquetteProduct, reflectLinkVariable]
    simp [hμ0, hν0]
    rw [ReflectSite.involution n]
    rw [reflectSite_addVector_comm T L (ReflectSite.reflectSite n) μ hμ0, ReflectSite.involution n]
    rw [reflectSite_addVector_comm_two T L (ReflectSite.reflectSite n) μ ν hμ0 hν0, ReflectSite.involution n]
    rw [reflectSite_addVector_comm T L (ReflectSite.reflectSite n) ν hν0, ReflectSite.involution n]
  simpa [h_eq]

lemma trace_plaquetteProduct_reflect_ts (N T L : ℕ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) (n : PeriodicSite T L) (ν : Fin 4)
    (hν0 : ν ≠ 0) :
    ((Matrix.trace ((plaquetteProduct N U n 0 ν : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) =
    ((Matrix.trace ((plaquetteProduct N (reflectLinkVariable N U)
      (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) ν 0 : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) := by
  set a := U.value n 0
  set b := U.value (addVectorPeriodic T L n 0) ν
  set c := (U.value (addVectorPeriodic T L (addVectorPeriodic T L n 0) ν) 0)⁻¹
  set d := (U.value (addVectorPeriodic T L n ν) ν)⁻¹
  have h_original : ((plaquetteProduct N U n 0 ν : Matrix (Fin N) (Fin N) ℂ)) = a * b * c * d := by
    dsimp [plaquetteProduct, a, b, c, d]; rfl
  set m := ReflectSite.reflectSite (addVectorPeriodic T L n 0)
  have h_reflected : ((plaquetteProduct N (reflectLinkVariable N U) m ν 0 : Matrix (Fin N) (Fin N) ℂ)) = b * c * d * a := by
    dsimp only [plaquetteProduct]
    -- Factor 1: (θU)(m, ν) = U(θm, ν) = U(n+e₀, ν) = b
    have h_f1 : (reflectLinkVariable N U).value m ν = b := by
      dsimp [reflectLinkVariable, m, b]
      simp [hν0, ReflectSite.involution]
    -- Factor 2: (θU)(m+e_ν, 0) = (U(θ(m+e_ν), 0))⁻¹ = (U(n+e₀+e_ν, 0))⁻¹ = c
    have h_f2 : (reflectLinkVariable N U).value (AddVector.addVector m ν) 0 = c := by
      dsimp [reflectLinkVariable, c]
      have h_θ : ReflectSite.reflectSite (AddVector.addVector m ν) = addVectorPeriodic T L (addVectorPeriodic T L n 0) ν := by
        calc
          ReflectSite.reflectSite (AddVector.addVector m ν)
              = AddVector.addVector (ReflectSite.reflectSite m) ν :=
            reflectSite_addVector_comm T L m ν hν0
          _ = AddVector.addVector (addVectorPeriodic T L n 0) ν := by simp [m, ReflectSite.involution]
      simp [hν0, h_θ]
    have h_f3 : ((reflectLinkVariable N U).value (AddVector.addVector (AddVector.addVector m ν) 0) ν)⁻¹ = d := by
      dsimp [reflectLinkVariable, d]
      have h_θ : ReflectSite.reflectSite (AddVector.addVector (AddVector.addVector m ν) 0) = addVectorPeriodic T L n ν := by
        fin_cases ν
        · exfalso; exact hν0 rfl
        · simp [ReflectSite.reflectSite, AddVector.addVector, reflectSitePeriodic, addVectorPeriodic, m]
        · simp [ReflectSite.reflectSite, AddVector.addVector, reflectSitePeriodic, addVectorPeriodic, m]
        · simp [ReflectSite.reflectSite, AddVector.addVector, reflectSitePeriodic, addVectorPeriodic, m]
      simp [hν0, h_θ]
    -- Factor 4: ((θU)(m+e_0, 0))⁻¹ = ((U(θ(m+e_0), 0))⁻¹)⁻¹ = U(n, 0) = a
    have h_f4 : ((reflectLinkVariable N U).value (AddVector.addVector m 0) 0)⁻¹ = a := by
      dsimp [reflectLinkVariable, a]
      have h_θ : ReflectSite.reflectSite (AddVector.addVector m 0) = n := by
        simp [ReflectSite.reflectSite, AddVector.addVector, reflectSitePeriodic, addVectorPeriodic, m]
      simp [h_θ]
    rw [h_f1, h_f2, h_f3, h_f4]
    simp [map_mul]
  rw [h_original, h_reflected]
  exact congrArg (fun x => x.re) (trace_cyclic_four N (a : Matrix (Fin N) (Fin N) ℂ) b c d)

lemma trace_plaquetteProduct_reflect_st (N T L : ℕ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) (n : PeriodicSite T L) (μ : Fin 4)
    (hμ0 : μ ≠ 0) :
    ((Matrix.trace ((plaquetteProduct N U n μ 0 : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) =
    ((Matrix.trace ((plaquetteProduct N (reflectLinkVariable N U)
      (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) 0 μ : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) := by
  set a := U.value n μ
  set b := U.value (addVectorPeriodic T L n μ) 0
  set c := (U.value (addVectorPeriodic T L (addVectorPeriodic T L n μ) 0) μ)⁻¹
  set d := (U.value (addVectorPeriodic T L n 0) 0)⁻¹
  have h_original : ((plaquetteProduct N U n μ 0 : Matrix (Fin N) (Fin N) ℂ)) = a * b * c * d := by
    dsimp [plaquetteProduct, a, b, c, d]; rfl
  set m := ReflectSite.reflectSite (addVectorPeriodic T L n 0)
  have h_reflected : ((plaquetteProduct N (reflectLinkVariable N U) m 0 μ : Matrix (Fin N) (Fin N) ℂ)) = d * a * b * c := by
    dsimp only [plaquetteProduct]
    -- Factor 1: (θU)(m, 0) = (U(θm, 0))⁻¹ = (U(n+e₀, 0))⁻¹ = d
    have h_f1 : (reflectLinkVariable N U).value m 0 = d := by
      have h_θm : ReflectSite.reflectSite m = addVectorPeriodic T L n 0 := by
        simp [m, ReflectSite.involution]
      simp [reflectLinkVariable, h_θm, d]
    -- Factor 2: (θU)(m+e_0, μ) = U(θ(m+e_0), μ) = U(n, μ) = a
    have h_f2 : (reflectLinkVariable N U).value (AddVector.addVector m 0) μ = a := by
      have h_θ : ReflectSite.reflectSite (AddVector.addVector m 0) = n := by
        simp [ReflectSite.reflectSite, AddVector.addVector, reflectSitePeriodic, addVectorPeriodic, m]
      simp [reflectLinkVariable, hμ0, h_θ, a]
    -- Factor 3: ((θU)(m+e_0+e_μ, 0))⁻¹ = ((U(θ(m+e_0+e_μ), 0))⁻¹)⁻¹ = U(θ(m+e_0+e_μ), 0) = U(n+e_μ, 0) = b
    have h_f3 : ((reflectLinkVariable N U).value (AddVector.addVector (AddVector.addVector m 0) μ) 0)⁻¹ = b := by
      have h_θ : ReflectSite.reflectSite (AddVector.addVector (AddVector.addVector m 0) μ) = addVectorPeriodic T L n μ := by
        fin_cases μ
        · exfalso; exact hμ0 rfl
        · simp [ReflectSite.reflectSite, AddVector.addVector, reflectSitePeriodic, addVectorPeriodic, m]
        · simp [ReflectSite.reflectSite, AddVector.addVector, reflectSitePeriodic, addVectorPeriodic, m]
        · simp [ReflectSite.reflectSite, AddVector.addVector, reflectSitePeriodic, addVectorPeriodic, m]
      simp [reflectLinkVariable, h_θ, b]
    -- Factor 4: ((θU)(m+e_μ, μ))⁻¹ = (U(θ(m+e_μ), μ))⁻¹ = (U(n+e₀+e_μ, μ))⁻¹ = c
    have h_f4 : ((reflectLinkVariable N U).value (AddVector.addVector m μ) μ)⁻¹ = c := by
      dsimp [reflectLinkVariable, c]
      have h_θ : ReflectSite.reflectSite (AddVector.addVector m μ) = addVectorPeriodic T L (addVectorPeriodic T L n 0) μ := by
        calc
          ReflectSite.reflectSite (AddVector.addVector m μ)
              = AddVector.addVector (ReflectSite.reflectSite m) μ :=
            reflectSite_addVector_comm T L m μ hμ0
          _ = AddVector.addVector (addVectorPeriodic T L n 0) μ := by simp [m, ReflectSite.involution]
      have h_comm : addVectorPeriodic T L (addVectorPeriodic T L n 0) μ = addVectorPeriodic T L (addVectorPeriodic T L n μ) 0 := by
        fin_cases μ
        · exfalso; exact hμ0 rfl
        · ext <;> simp [addVectorPeriodic]
        · ext <;> simp [addVectorPeriodic]
        · ext <;> simp [addVectorPeriodic]
      simp [hμ0, h_θ, h_comm]
    rw [h_f1, h_f2, h_f3, h_f4]
    rfl
  rw [h_original, h_reflected]
  exact congrArg (fun x => x.re) (trace_cyclic_four N (d : Matrix (Fin N) (Fin N) ℂ) a b c).symm

lemma trace_plaquetteProduct_reflect_tt (N T L : ℕ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) (n : PeriodicSite T L) :
    ((Matrix.trace ((plaquetteProduct N U n 0 0 : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) =
    ((Matrix.trace ((plaquetteProduct N (reflectLinkVariable N U)
      (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0)) 0 0 : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) := by
  set a := U.value n 0
  set b := U.value (addVectorPeriodic T L n 0) 0
  set c := (U.value (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0) 0)⁻¹
  set d := (U.value (addVectorPeriodic T L n 0) 0)⁻¹
  have h_original : ((plaquetteProduct N U n 0 0 : Matrix (Fin N) (Fin N) ℂ)) = a * b * c * d := by
    dsimp [plaquetteProduct, a, b, c, d]; rfl
  set m := ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0)
  have h_reflected : ((plaquetteProduct N (reflectLinkVariable N U) m 0 0 : Matrix (Fin N) (Fin N) ℂ)) = c * d * a * b := by
    dsimp only [plaquetteProduct]
    -- Factor 1: (θU)(m, 0) = (U(θm, 0))⁻¹ = (U(n+2e₀, 0))⁻¹ = c
    have h_f1 : (reflectLinkVariable N U).value m 0 = c := by
      have h_θm : ReflectSite.reflectSite m = addVectorPeriodic T L (addVectorPeriodic T L n 0) 0 := by
        simp [m, ReflectSite.involution]
      simp [reflectLinkVariable, h_θm, c]
    -- Factor 2: (θU)(m+e_0, 0) = (U(θ(m+e_0), 0))⁻¹ = (U(n+e₀, 0))⁻¹ = d
    have h_f2 : (reflectLinkVariable N U).value (AddVector.addVector m 0) 0 = d := by
      have h_θ : ReflectSite.reflectSite (AddVector.addVector m 0) = addVectorPeriodic T L n 0 := by
        simp [ReflectSite.reflectSite, AddVector.addVector, reflectSitePeriodic, addVectorPeriodic, m]
      simp [reflectLinkVariable, h_θ, d]
    -- Factor 3: ((θU)(m+2e_0, 0))⁻¹ = ((U(θ(m+2e_0), 0))⁻¹)⁻¹ = U(θ(m+2e_0), 0) = U(n, 0) = a
    have h_f3 : ((reflectLinkVariable N U).value (AddVector.addVector (AddVector.addVector m 0) 0) 0)⁻¹ = a := by
      have h_θ : ReflectSite.reflectSite (AddVector.addVector (AddVector.addVector m 0) 0) = n := by
        simp [ReflectSite.reflectSite, AddVector.addVector, reflectSitePeriodic, addVectorPeriodic, m]
      simp [reflectLinkVariable, h_θ, a]
    -- Factor 4: ((θU)(m+e_0, 0))⁻¹ = ((U(θ(m+e_0), 0))⁻¹)⁻¹ = U(θ(m+e_0), 0) = U(n+e₀, 0) = b
    have h_f4 : ((reflectLinkVariable N U).value (AddVector.addVector m 0) 0)⁻¹ = b := by
      have h_θ : ReflectSite.reflectSite (AddVector.addVector m 0) = addVectorPeriodic T L n 0 := by
        simp [ReflectSite.reflectSite, AddVector.addVector, reflectSitePeriodic, addVectorPeriodic, m]
      simp [reflectLinkVariable, h_θ, b]
    rw [h_f1, h_f4, h_f2, h_f3]
    rfl
  rw [h_original, h_reflected]
  exact congrArg (fun x => x.re)
    (Eq.trans (trace_cyclic_four N (a : Matrix (Fin N) (Fin N) ℂ) b c d)
      (trace_cyclic_four N (b : Matrix (Fin N) (Fin N) ℂ) c d a))
