/-
# Positive-definite functions on groups — Mathlib candidate

This is a standalone, self-contained file extracting the group-theoretic
positive-definite-function theory developed in the YangMills project
(`src/lean/YangMills/Proofs/PositiveDefinite.lean` and
`src/lean/YangMills/Proofs/PositiveDefiniteIntegral.lean`).  It is pure
group/measure theory: no gauge theory, no lattice, no Yang-Mills.

## Main results

1. `PositiveDefinite.integral` — an integral average of positive-definite
   functions on a group is positive-definite (the continuous analogue of
   `PositiveDefinite.sum`).

2. `PositiveDefinite.integralOperator_nonneg` — for a compact (pseudo)metric
   group `G` with probability measure `μ`, a continuous positive-definite
   function `φ`, and a continuous `f`,
   `∫∫ f(x) * conj(f(y)) * φ(x⁻¹ * y) dμ dμ ≥ 0`.
   The proof approximates the integral by Riemann sums (each non-negative by
   `PositiveDefinite.sum_nonneg_of_map`) and controls the error via uniform
   continuity on `G × G`.

## Supporting lemma

* `PositiveDefinite.sum_nonneg_of_map` — the quadratic form with a mapped
  (possibly non-injective) index set is non-negative.  This is the key
  grouping argument used by `integralOperator_nonneg`.

## Verification

All lemmas depend only on `propext`, `Classical.choice`, `Quot.sound`
(verified by `#print axioms`), with 0 `sorry`s and 0 custom axioms.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Disjointed
import Mathlib.Topology.Constructions.SumProd

open Finset MeasureTheory Complex Metric

open scoped ComplexConjugate ComplexOrder Function

attribute [local instance] Classical.propDecidable

/-- A function `φ : G → ℂ` on a group `G` is *positive-definite* if for every
finite set `{g_i}` and coefficients `{c_i}`, the quadratic form
`∑ c_i * conj(c_j) * φ(g_i⁻¹ * g_j) ≥ 0`. -/
def PositiveDefinite {G : Type*} [Group G] (φ : G → ℂ) : Prop :=
  ∀ (s : Finset G) (c : G → ℂ),
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * φ (i⁻¹ * j)

variable {G : Type*} [Group G]

/-- Helper: sum over fibers of a function.  For any `f : α → G`, the sum
`∑ i ∈ s, w i * Φ (f i)` can be regrouped by the value of `f i`. -/
private lemma sum_fiber {α : Type*} {G : Type*}
    (s : Finset α) (f : α → G) (w : α → ℂ) (Φ : G → ℂ) :
    ∑ i ∈ s, w i * Φ (f i) =
    ∑ g ∈ s.image f, (∑ i ∈ s.filter (fun i => f i = g), w i) * Φ g := by
  classical
  let t := s.image f
  have hmaps : ∀ i ∈ s, f i ∈ t := fun i hi => Finset.mem_image_of_mem f hi
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl (fun g hg => ?_)
  have hfg : ∀ i ∈ s.filter (fun i => f i = g), f i = g := fun i hi =>
    (Finset.mem_filter.mp hi).2
  have hsum : ∑ i ∈ s.filter (fun i => f i = g), w i * Φ (f i) =
      ∑ i ∈ s.filter (fun i => f i = g), w i * Φ g := by
    apply Finset.sum_congr rfl
    intro i hi; rw [hfg i hi]
  rw [hsum, ← Finset.sum_mul]

/-- For a positive-definite function `φ`, the quadratic form with a mapped index set
is non-negative.  This is the key grouping argument: even if `f : α → G` is not
injective, the sum `∑ c_i conj(c_j) φ(f(i)⁻¹ * f(j))` is non-negative. -/
lemma PositiveDefinite.sum_nonneg_of_map
    {G : Type*} [Group G] {φ : G → ℂ} (hφ : PositiveDefinite φ)
    {α : Type*} (s : Finset α) (f : α → G) (c : α → ℂ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * φ ((f i)⁻¹ * f j) := by
  classical
  let t := s.image f
  let d : G → ℂ := fun g => ∑ i ∈ s.filter (fun i => f i = g), c i
  have h_conj_d : ∀ h, ∑ j ∈ s.filter (fun j => f j = h), conj (c j) = conj (d h) := by
    intro h
    simp only [d, ← map_sum (starRingEnd ℂ)]
  have h_fiber_i : ∀ j ∈ s, ∑ i ∈ s, c i * φ ((f i)⁻¹ * f j) =
      ∑ g ∈ t, d g * φ (g⁻¹ * f j) := by
    intro j hj
    exact sum_fiber s f c (fun g => φ (g⁻¹ * f j))
  have h_fiber_j : ∀ g ∈ t, ∑ j ∈ s, conj (c j) * φ (g⁻¹ * f j) =
      ∑ h ∈ t, conj (d h) * φ (g⁻¹ * h) := by
    intro g hg
    rw [sum_fiber s f (fun j => conj (c j)) (fun h => φ (g⁻¹ * h))]
    apply Finset.sum_congr rfl
    intro h hh
    rw [h_conj_d h]
  calc
    ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * φ ((f i)⁻¹ * f j)
        = ∑ j ∈ s, ∑ i ∈ s, c i * conj (c j) * φ ((f i)⁻¹ * f j) := by
      rw [Finset.sum_comm]
    _ = ∑ j ∈ s, conj (c j) * ∑ i ∈ s, c i * φ ((f i)⁻¹ * f j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have h_rearr : ∑ i ∈ s, c i * conj (c j) * φ ((f i)⁻¹ * f j) =
          ∑ i ∈ s, conj (c j) * (c i * φ ((f i)⁻¹ * f j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [mul_comm (c i) (conj (c j)), mul_assoc]
      rw [h_rearr, ← Finset.mul_sum]
    _ = ∑ j ∈ s, conj (c j) * ∑ g ∈ t, d g * φ (g⁻¹ * f j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [h_fiber_i j hj]
    _ = ∑ g ∈ t, d g * ∑ j ∈ s, conj (c j) * φ (g⁻¹ * f j) := by
      have h1 : ∑ j ∈ s, conj (c j) * ∑ g ∈ t, d g * φ (g⁻¹ * f j) =
          ∑ j ∈ s, ∑ g ∈ t, conj (c j) * d g * φ (g⁻¹ * f j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro g hg
        rw [← mul_assoc]
      have h2 : ∑ j ∈ s, ∑ g ∈ t, conj (c j) * d g * φ (g⁻¹ * f j) =
          ∑ g ∈ t, ∑ j ∈ s, conj (c j) * d g * φ (g⁻¹ * f j) := by
        exact Finset.sum_comm ..
      have h3 : ∑ g ∈ t, ∑ j ∈ s, conj (c j) * d g * φ (g⁻¹ * f j) =
          ∑ g ∈ t, d g * ∑ j ∈ s, conj (c j) * φ (g⁻¹ * f j) := by
        apply Finset.sum_congr rfl
        intro g hg
        have h_rearr : ∑ j ∈ s, conj (c j) * d g * φ (g⁻¹ * f j) =
            ∑ j ∈ s, d g * (conj (c j) * φ (g⁻¹ * f j)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [mul_comm (conj (c j)) (d g), mul_assoc]
        rw [h_rearr, ← Finset.mul_sum]
      rw [h1, h2, h3]
    _ = ∑ g ∈ t, d g * ∑ h ∈ t, conj (d h) * φ (g⁻¹ * h) := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [h_fiber_j g hg]
    _ = ∑ g ∈ t, ∑ h ∈ t, d g * conj (d h) * φ (g⁻¹ * h) := by
      apply Finset.sum_congr rfl
      intro g hg
      have h_rearr : ∑ h ∈ t, d g * conj (d h) * φ (g⁻¹ * h) =
          ∑ h ∈ t, d g * (conj (d h) * φ (g⁻¹ * h)) := by
        apply Finset.sum_congr rfl
        intro h hh
        rw [← mul_assoc]
      rw [h_rearr, ← Finset.mul_sum]
    _ ≥ 0 := hφ t d

/-- **An integral average of positive-definite functions is positive-definite.**

Let `ν` be a measure on `T` and `Φ : T → G → ℂ` a family of functions such that
`Φ t` is positive-definite for `ν`-almost every `t`, and such that for every
`g : G` the map `t ↦ Φ t g` is `ν`-integrable.  Then the pointwise integral
`g ↦ ∫ t, Φ t g ∂ν` is positive-definite.

This is the continuous analogue of `PositiveDefinite.sum` (a finite sum of PD
functions with non-negative weights is PD).  The proof swaps the finite PD
quadratic-form sum with the integral (justified by the integrability
hypothesis) and uses that the integrand is non-negative `ν`-a.e. by the
positive-definiteness of each `Φ t`. -/
lemma PositiveDefinite.integral {T : Type*} [MeasurableSpace T] (ν : Measure T)
    (Φ : T → G → ℂ) (hPD : ∀ᵐ t ∂ν, PositiveDefinite (Φ t))
    (hint : ∀ g : G, Integrable (fun t => Φ t g) ν) :
    PositiveDefinite (fun g => ∫ t, Φ t g ∂ν) := by
  intro s c
  have h_nonneg : ∀ᵐ t ∂ν,
      0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * Φ t (i⁻¹ * j) := by
    filter_upwards [hPD] with t hPDt
    exact hPDt s c
  have h_int_ij : ∀ i ∈ s, ∀ j ∈ s, Integrable
      (fun t => c i * conj (c j) * Φ t (i⁻¹ * j)) ν := by
    intro i _ j _
    have h := (hint (i⁻¹ * j)).smul (c i * conj (c j))
    rwa [show (c i * conj (c j)) • (fun t => Φ t (i⁻¹ * j)) =
        (fun t => c i * conj (c j) * Φ t (i⁻¹ * j)) from by
        funext t; rw [Pi.smul_apply, smul_eq_mul]] at h
  have h_int_i : ∀ i ∈ s, Integrable
      (fun t => ∑ j ∈ s, c i * conj (c j) * Φ t (i⁻¹ * j)) ν :=
    fun i hi => integrable_finsetSum s (h_int_ij i hi)
  have h_swap :
      (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * ∫ t, Φ t (i⁻¹ * j) ∂ν) =
      ∫ t, ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * Φ t (i⁻¹ * j) ∂ν := by
    symm
    rw [integral_finsetSum s h_int_i]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum s (h_int_ij i hi)]
    apply Finset.sum_congr rfl
    intro j _
    rw [show (fun t => c i * conj (c j) * Φ t (i⁻¹ * j)) =
        (fun t => (c i * conj (c j)) • Φ t (i⁻¹ * j)) from by
        funext t; rw [smul_eq_mul, mul_assoc]]
    rw [integral_smul, smul_eq_mul]
  have h_beta :
      (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * (fun g => ∫ t, Φ t g ∂ν) (i⁻¹ * j)) =
      (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * ∫ t, Φ t (i⁻¹ * j) ∂ν) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rfl
  rw [h_beta, h_swap]
  have h_re_nonneg : ∀ᵐ t ∂ν,
      0 ≤ (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * Φ t (i⁻¹ * j)).re := by
    filter_upwards [h_nonneg] with t ht
    exact (Complex.nonneg_iff.mp ht).1
  have h_im_zero : ∀ᵐ t ∂ν,
      (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * Φ t (i⁻¹ * j)).im = 0 := by
    filter_upwards [h_nonneg] with t ht
    exact (Complex.nonneg_iff.mp ht).2.symm
  have h_int' : Integrable
      (fun t => ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * Φ t (i⁻¹ * j)) ν := by
    have heq : (fun t => ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * Φ t (i⁻¹ * j)) =
        fun t => ∑ i ∈ s, ∑ j ∈ s, (c i * conj (c j)) • Φ t (i⁻¹ * j) := by
      funext t; simp only [smul_eq_mul, mul_assoc]
    rw [heq]
    exact integrable_finsetSum s (fun i hi => integrable_finsetSum s (h_int_ij i hi))
  have h_im_zero' : (fun t => (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * Φ t (i⁻¹ * j)).im) =ᵐ[ν] 0 :=
    h_im_zero
  have h_int_re : (∫ t, ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * Φ t (i⁻¹ * j) ∂ν).re =
      ∫ t, (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * Φ t (i⁻¹ * j)).re ∂ν :=
    (integral_re h_int').symm
  have h_int_im : (∫ t, ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * Φ t (i⁻¹ * j) ∂ν).im =
      ∫ t, (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * Φ t (i⁻¹ * j)).im ∂ν :=
    (integral_im h_int').symm
  rw [Complex.nonneg_iff]
  refine ⟨?_, ?_⟩
  · rw [h_int_re]
    exact integral_nonneg_of_ae h_re_nonneg
  · rw [h_int_im]
    rw [integral_eq_zero_of_ae h_im_zero']

/-- **A continuous positive-definite function on a compact group defines a
positive integral operator.**

For a compact (pseudo)metric group `G` with probability measure `μ`, a
continuous positive-definite function `φ`, and a continuous function `f`,
the integral `∫∫ f(x) * conj(f(y)) * φ(x⁻¹ * y) dμ dμ ≥ 0`.

The proof approximates the integral by Riemann sums (each non-negative by
`PositiveDefinite.sum_nonneg_of_map`) and controls the error via uniform
continuity on the compact space `G × G`.  No Haar-measure invariance is
needed: the non-negativity of each Riemann sum is a direct consequence of
the positive-definiteness of `φ`. -/
lemma PositiveDefinite.integralOperator_nonneg
    {G : Type*} [Group G] [PseudoMetricSpace G] [CompactSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {φ : G → ℂ} (hφ : PositiveDefinite φ) (hφ_cont : Continuous φ)
    {f : G → ℂ} (hf_cont : Continuous f) :
    0 ≤ ∫ x, ∫ y, f x * conj (f y) * φ (x⁻¹ * y) ∂μ ∂μ := by
  let F : G × G → ℂ := fun p => f p.1 * conj (f p.2) * φ (p.1⁻¹ * p.2)
  have hF_cont : Continuous F := by
    have h_fst : Continuous (fun p : G × G => f p.1) := hf_cont.comp continuous_fst
    have h_snd : Continuous (fun p : G × G => f p.2) := hf_cont.comp continuous_snd
    have h_conj_snd : Continuous (fun p : G × G => conj (f p.2)) :=
      Complex.continuous_conj.comp h_snd
    have h_group : Continuous (fun p : G × G => p.1⁻¹ * p.2) := by
      have h_inv : Continuous (fun p : G × G => (p.1)⁻¹) :=
        continuous_inv.comp continuous_fst
      exact Continuous.mul h_inv continuous_snd
    have h_phi : Continuous (fun p : G × G => φ (p.1⁻¹ * p.2)) := hφ_cont.comp h_group
    convert Continuous.mul (Continuous.mul h_fst h_conj_snd) h_phi using 1
    ext p; rfl
  haveI : CompactSpace (G × G) := inferInstance
  have hF_unif : UniformContinuous F :=
    CompactSpace.uniformContinuous_of_continuous hF_cont
  have hF_aes : AEStronglyMeasurable F (μ.prod μ) :=
    Continuous.aestronglyMeasurable_of_compactSpace hF_cont
  have hF_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : G × G, ‖F z‖ ≤ C := by
    have h_range_compact : IsCompact (Set.range F) := by
      rw [← Set.image_univ]
      exact isCompact_univ.image hF_cont
    obtain ⟨C, hCpos, hC⟩ := h_range_compact.isBounded.exists_pos_norm_le
    exact ⟨C, hCpos.le, fun z => hC (F z) (Set.mem_range_self _)⟩
  obtain ⟨C, hCnn, hC⟩ := hF_bdd
  have hF_int : Integrable F (μ.prod μ) := by
    apply Integrable.of_bound hF_aes C
    filter_upwards with z using hC z
  have hFub : ∫ z, F z ∂(μ.prod μ) = ∫ x, ∫ y, f x * conj (f y) * φ (x⁻¹ * y) ∂μ ∂μ := by
    rw [integral_prod F hF_int]
  rw [← hFub]
  set I : ℂ := ∫ z, F z ∂(μ.prod μ)
  have hkey : ∀ ε : ℝ, 0 < ε → ∃ S : ℂ, 0 ≤ S ∧ ‖I - S‖ ≤ ε := by
    intro ε εpos
    obtain ⟨δ, δpos, hδ⟩ := Metric.uniformContinuous_iff.mp hF_unif ε εpos
    obtain ⟨t, _, ht_fin, ht_cover⟩ :=
      finite_cover_balls_of_compact (isCompact_univ : IsCompact (Set.univ : Set G)) (half_pos δpos)
    let ts : Finset G := ht_fin.toFinset
    have hts_eq : ↑ts = t := ht_fin.coe_toFinset
    let n := ts.card
    let e : Fin n ≃ ↥ts := ts.equivFin.symm
    let x : Fin n → G := fun i => (e i : G)
    let B : Fin n → Set G := fun i => ball (x i) (δ / 2)
    have hA_disjoint : Pairwise (Disjoint on disjointed B) := disjoint_disjointed B
    have hA_cover : (Set.univ : Set G) ⊆ ⋃ (i : Fin n), disjointed B i := by
      rw [iUnion_disjointed]
      intro g hg
      simp only [Set.mem_iUnion]
      have hg' := ht_cover hg
      simp only [Set.mem_iUnion₂] at hg'
      obtain ⟨xg, hxg, hg_ball⟩ := hg'
      have hxg_ts : xg ∈ ts := by
        have : xg ∈ (↑ts : Set G) := hts_eq.symm ▸ hxg
        exact Finset.mem_coe.mp this
      obtain ⟨i, hi⟩ := (Equiv.surjective e) ⟨xg, hxg_ts⟩
      refine ⟨i, ?_⟩
      have hxi : x i = xg := by simp only [x, hi]
      simp only [B, hxi]
      exact hg_ball
    have hA_meas : ∀ (i : Fin n), MeasurableSet (disjointed B i) := by
      intro i
      rw [disjointed_apply, Finset.sup_set_eq_biUnion]
      exact MeasurableSet.diff isOpen_ball.measurableSet
        (Finset.measurableSet_biUnion _ (fun j _ => isOpen_ball.measurableSet))
    let c : Fin n → ℂ := fun i => f (x i) * ((μ.real (disjointed B i)) : ℂ)
    refine ⟨∑ i, ∑ j, c i * conj (c j) * φ ((x i)⁻¹ * x j), ?_, ?_⟩
    · exact hφ.sum_nonneg_of_map Finset.univ x c
    · have hCover : (Set.univ : Set (G × G)) =
        ⋃ (ij : Fin n × Fin n), disjointed B ij.1 ×ˢ disjointed B ij.2 := by
        rw [Set.iUnion_prod]
        have hU : (⋃ i, disjointed B i) = (Set.univ : Set G) :=
          (Set.subset_univ _).antisymm hA_cover
        simp only [hU, Set.univ_prod_univ]
      have hDisj : Pairwise (Disjoint on
          fun ij : Fin n × Fin n => disjointed B ij.1 ×ˢ disjointed B ij.2) := by
        intro ij ij' hij
        simp only [Function.onFun]
        rw [Set.disjoint_prod]
        by_cases h1 : ij.1 = ij'.1
        · right; exact hA_disjoint (fun heq => hij (Prod.ext h1 heq))
        · left; exact hA_disjoint h1
      have hMeas' : ∀ (ij : Fin n × Fin n),
          MeasurableSet (disjointed B ij.1 ×ˢ disjointed B ij.2) :=
        fun ij => MeasurableSet.prod (hA_meas ij.1) (hA_meas ij.2)
      have hInt' : ∀ (ij : Fin n × Fin n),
          IntegrableOn F (disjointed B ij.1 ×ˢ disjointed B ij.2) (μ.prod μ) :=
        fun ij => hF_int.integrableOn
      have hI_part : I = ∑ (ij : Fin n × Fin n),
          ∫ z in disjointed B ij.1 ×ˢ disjointed B ij.2, F z ∂(μ.prod μ) := by
        rw [show I = ∫ z in Set.univ, F z ∂(μ.prod μ) from setIntegral_univ.symm, hCover]
        exact integral_iUnion_fintype hMeas' hDisj hInt'
      have h_term : ∀ (ij : Fin n × Fin n),
          c ij.1 * conj (c ij.2) * φ ((x ij.1)⁻¹ * x ij.2) =
          ∫ z in disjointed B ij.1 ×ˢ disjointed B ij.2, F (x ij.1, x ij.2) ∂(μ.prod μ) := by
        intro ij
        rw [setIntegral_const, measureReal_prod_prod]
        simp only [c, F, map_mul, Complex.conj_ofReal,
          Algebra.smul_def, Complex.coe_algebraMap]
        ring
      have hS_part : (∑ i, ∑ j, c i * conj (c j) * φ ((x i)⁻¹ * x j)) =
          ∑ (ij : Fin n × Fin n),
          ∫ z in disjointed B ij.1 ×ˢ disjointed B ij.2, F (x ij.1, x ij.2) ∂(μ.prod μ) := by
        rw [← Finset.sum_product', Finset.univ_product_univ]
        exact Finset.sum_congr rfl (fun ij _ => h_term ij)
      have hIS : I - ∑ i, ∑ j, c i * conj (c j) * φ ((x i)⁻¹ * x j) =
          ∑ (ij : Fin n × Fin n),
          ∫ z in disjointed B ij.1 ×ˢ disjointed B ij.2,
            (F z - F (x ij.1, x ij.2)) ∂(μ.prod μ) := by
        rw [hI_part, hS_part, sub_eq_add_neg, ← Finset.sum_neg_distrib,
          ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro ij _
        rw [← sub_eq_add_neg, ← integral_sub (hInt' ij) ((integrable_const _).integrableOn)]
      have hUC : ∀ (ij : Fin n × Fin n),
          ∀ z ∈ disjointed B ij.1 ×ˢ disjointed B ij.2,
          ‖F z - F (x ij.1, x ij.2)‖ ≤ ε := by
        intro ij z hz
        have ha : z.1 ∈ disjointed B ij.1 := hz.1
        have hb : z.2 ∈ disjointed B ij.2 := hz.2
        have ha_sub : disjointed B ij.1 ⊆ B ij.1 := disjointed_subset B ij.1
        have hb_sub : disjointed B ij.2 ⊆ B ij.2 := disjointed_subset B ij.2
        have ha_dist : dist z.1 (x ij.1) < δ / 2 := ha_sub ha
        have hb_dist : dist z.2 (x ij.2) < δ / 2 := hb_sub hb
        have hdist : dist z (x ij.1, x ij.2) < δ := by
          rw [Prod.dist_eq]
          exact (max_lt ha_dist hb_dist).trans (by linarith [δpos])
        have hnorm : ‖F z - F (x ij.1, x ij.2)‖ < ε := by
          have := hδ hdist
          rwa [dist_eq_norm] at this
        exact le_of_lt hnorm
      have hSumMeas : ∑ (ij : Fin n × Fin n),
          (μ.prod μ).real (disjointed B ij.1 ×ˢ disjointed B ij.2) = 1 := by
        rw [← measureReal_iUnion_fintype hDisj hMeas', ← hCover]
        simp [measureReal_def]
      rw [hIS]
      calc ‖∑ (ij : Fin n × Fin n),
          ∫ z in disjointed B ij.1 ×ˢ disjointed B ij.2,
            (F z - F (x ij.1, x ij.2)) ∂(μ.prod μ)‖
          ≤ ∑ (ij : Fin n × Fin n),
              ‖∫ z in disjointed B ij.1 ×ˢ disjointed B ij.2,
                  (F z - F (x ij.1, x ij.2)) ∂(μ.prod μ)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ (ij : Fin n × Fin n),
              ε * (μ.prod μ).real (disjointed B ij.1 ×ˢ disjointed B ij.2) := by
            apply Finset.sum_le_sum
            intro ij _
            exact norm_setIntegral_le_of_norm_le_const (by finiteness) (hUC ij)
        _ = ε * ∑ (ij : Fin n × Fin n),
              (μ.prod μ).real (disjointed B ij.1 ×ˢ disjointed B ij.2) := by
            rw [← Finset.mul_sum]
        _ = ε * 1 := by rw [hSumMeas]
        _ = ε := mul_one ε
  rw [Complex.nonneg_iff]
  refine ⟨?_, ?_⟩
  · by_contra h
    have hneg : I.re < 0 := lt_of_not_ge h
    obtain ⟨S, hS_nonneg, hS_bound⟩ := hkey (-I.re / 2) (half_pos (neg_pos.mpr hneg))
    have hReS : 0 ≤ S.re := (Complex.nonneg_iff.mp hS_nonneg).1
    have h_abs : |I.re - S.re| ≤ ‖I - S‖ := by
      rw [show I.re - S.re = (I - S).re from rfl]
      exact abs_re_le_norm (I - S)
    have h_bound : |I.re - S.re| ≤ -I.re / 2 := h_abs.trans hS_bound
    have h_lower : I.re ≥ S.re - (-I.re / 2) := by linarith [abs_le.mp h_bound]
    linarith
  · by_contra h
    have hne : I.im ≠ 0 := fun heq => h heq.symm
    have habs : 0 < |I.im| := abs_pos.mpr hne
    obtain ⟨S, hS_nonneg, hS_bound⟩ := hkey (|I.im| / 2) (half_pos habs)
    have hImS : S.im = 0 := (Complex.nonneg_iff.mp hS_nonneg).2.symm
    have h_abs : |I.im - S.im| ≤ ‖I - S‖ := by
      rw [show I.im - S.im = (I - S).im from rfl]
      exact abs_im_le_norm (I - S)
    have h_bound : |I.im| ≤ |I.im| / 2 := by
      rw [hImS] at h_abs
      simp only [sub_zero] at h_abs
      exact h_abs.trans hS_bound
    linarith

#print axioms PositiveDefinite.sum_nonneg_of_map
#print axioms PositiveDefinite.integral
#print axioms PositiveDefinite.integralOperator_nonneg

