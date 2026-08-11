/-
# Integration of Positive-Definite Functions

This file provides the *continuous* analogue of `PositiveDefinite.sum`: an
integral (average) of positive-definite functions is again positive-definite.

This is a key piece of infrastructure for the Osterwalder–Seiler transfer-matrix
positivity argument.  In that argument the transfer-matrix kernel is obtained
by integrating out the interior (negative-time) link variables; each plaquette
Boltzmann factor entering that integral is positive-definite (proved in
`PeterWeyl.lean` as `plaquetteBoltzmannPD`, modulo the Peter–Weyl /
Clebsch–Gordan axiom), and a *product* of positive-definite functions is
positive-definite (`PositiveDefinite.mul` / `.prod`).  The present lemma
`PositiveDefinite.integral` then promotes the resulting *integral* of those
positive-definite products to a positive-definite kernel on the interface link
variables.

## What this closes and what it does not

- **Closes:** the step "integrate out interior links ⟹ the resulting kernel is
  positive-definite" (the continuous-sum step, `PositiveDefinite.integral`),
  which previously had no formalization in `PositiveDefinite.lean`.
- **Closes:** the step "a positive-definite kernel `K` on a compact group `G`
  defines a *positive integral operator*", i.e.
  `∫∫ f(x) * conj(f(y)) * K(x⁻¹ * y) dμ(x) dμ(y) ≥ 0` for a probability
  measure `μ` (`PositiveDefinite.integralOperator_nonneg`).  This is the
  continuous analogue of the definition of positive-definiteness itself; the
  proof approximates the integral by Riemann sums (each non-negative by
  `PositiveDefinite.sum_nonneg_of_map`) and uses uniform continuity on the
  compact space `G × G` to control the approximation error.
- **Does not close (the remaining, separately-scoped gap):** the *wiring* of
  these two abstract lemmas into the concrete lattice-gauge-theory setup of
  `ReflectionPositivity.lean`.  Closing `transferMatrixPositivity_axiom`
  requires showing that the transfer-matrix kernel is a positive-definite
  kernel on the interface link variables.  **Key obstruction**: the transfer
  matrix kernel `(Tψ)(u) = ∫ ψ(θ⁻⁰(U⁻,u⁰))·exp(-β·(...)) dμ⁻(U⁻)` is NOT of
  the form `φ(u⁻¹·v)` for a PD function `φ` on a group — the reflection map
  `θ⁻⁰` is a geometric operation, not group multiplication, and the kernel
  depends on `u` through both the OS-positive action and the interface
  restriction.  While `PosInterfaceConfig` is a product of SU(N)'s (hence a
  group), the kernel does not factor through the group structure.

  To address the group-structure obstruction, the **Mercer-type PD kernel
  theory** (approach (a)) is also built in this file (second half):
  `PositiveDefiniteKernel` (Mercer sense, no group structure),
  `PositiveDefiniteKernel.sum_nonneg_of_map`, and
  `PositiveDefiniteKernel.integralOperator_nonneg` (a continuous Mercer-PD
  kernel on a compact space defines a positive integral operator).  This
  removes the *group-structure* requirement, but showing the TM kernel *is*
  Mercer-PD still requires the Peter–Weyl character expansion to decompose
  the Boltzmann factor into separable positive terms (approach (c)).  See the
  status notes in `Overview.lean` and `README.md`, and `docs/gap_analysis.md`.

## References

* K. Osterwalder, E. Seiler, "Gauge Field Theories on a Lattice"
  (Ann. Phys. 110, 1978, pp 440–471), §3.
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
import Mathlib.MeasureTheory.Group.Measure
import YangMills.Proofs.PositiveDefinite

namespace YangMills

open Finset MeasureTheory Complex Metric Matrix

open scoped ComplexConjugate ComplexOrder Function

variable {G : Type*} [Group G]

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
  -- The PD quadratic-form integrand is non-negative ν-a.e.
  have h_nonneg : ∀ᵐ t ∂ν,
      0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * Φ t (i⁻¹ * j) := by
    filter_upwards [hPD] with t hPDt
    exact hPDt s c
  -- Integrability of each (i,j) summand, in `*` form.
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
  -- Swap the finite sum and the integral.
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
  -- Beta-reduce the goal to match h_swap, then conclude.
  have h_beta :
      (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * (fun g => ∫ t, Φ t g ∂ν) (i⁻¹ * j)) =
      (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * ∫ t, Φ t (i⁻¹ * j) ∂ν) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rfl
  rw [h_beta, h_swap]
  -- The integral is non-negative: split into real and imaginary parts.
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
  rw [ge_iff_le, Complex.nonneg_iff]
  refine ⟨?_, ?_⟩
  · rw [h_int_re]
    exact integral_nonneg_of_ae h_re_nonneg
  · rw [h_int_im]
    rw [integral_eq_zero_of_ae h_im_zero']

/-! ## Positive integral operators from positive-definite kernels

The main result here is `PositiveDefinite.integralOperator_nonneg`: for a
compact (pseudo)metric group `G` with probability measure `μ`, a continuous
positive-definite function `φ`, and a continuous function `f`, the integral
`∫∫ f(x) * conj(f(y)) * φ(x⁻¹ * y) dμ dμ ≥ 0`.

This is the continuous analogue of the definition of positive-definiteness
itself: the quadratic form `∑ c_i * conj(c_j) * φ(g_i⁻¹ * g_j) ≥ 0` becomes
an integral in the limit.  The proof approximates the integral by Riemann
sums; each Riemann sum is non-negative by `PositiveDefinite.sum_nonneg_of_map`,
and the sums converge to the integral by uniform continuity of the integrand
on the compact space `G × G`.

No Haar-measure invariance is needed: the non-negativity of each Riemann sum
is a direct consequence of the positive-definiteness of `φ`. -/

lemma PositiveDefinite.integralOperator_nonneg
    {G : Type*} [Group G] [PseudoMetricSpace G] [CompactSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    {φ : G → ℂ} (hφ : PositiveDefinite φ) (hφ_cont : Continuous φ)
    {f : G → ℂ} (hf_cont : Continuous f) :
    0 ≤ ∫ x, ∫ y, f x * conj (f y) * φ (x⁻¹ * y) ∂μ ∂μ := by
  -- The integrand as a function on G × G
  let F : G × G → ℂ := fun p => f p.1 * conj (f p.2) * φ (p.1⁻¹ * p.2)
  -- F is continuous (product of continuous functions on a topological group)
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
  -- G × G is compact
  haveI : CompactSpace (G × G) := inferInstance
  -- F is uniformly continuous (Heine–Cantor)
  have hF_unif : UniformContinuous F :=
    CompactSpace.uniformContinuous_of_continuous hF_cont
  -- F is integrable w.r.t. μ.prod μ (continuous on compact → bounded → integrable)
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
  -- Convert the iterated integral to a product-measure integral (Fubini)
  have hFub : ∫ z, F z ∂(μ.prod μ) = ∫ x, ∫ y, f x * conj (f y) * φ (x⁻¹ * y) ∂μ ∂μ := by
    rw [integral_prod F hF_int]
  rw [← hFub]
  -- Goal: 0 ≤ ∫ z, F z ∂(μ.prod μ)
  set I : ℂ := ∫ z, F z ∂(μ.prod μ)
  -- Strategy: for every ε > 0, build a Riemann sum S ≥ 0 with ‖I - S‖ ≤ ε.
  -- Then Re(I) ≥ 0 and Im(I) = 0, hence 0 ≤ I.
  have hkey : ∀ ε : ℝ, 0 < ε → ∃ S : ℂ, 0 ≤ S ∧ ‖I - S‖ ≤ ε := by
    intro ε εpos
    -- δ from uniform continuity of F on G × G
    obtain ⟨δ, δpos, hδ⟩ := Metric.uniformContinuous_iff.mp hF_unif ε εpos
    -- Cover G by finitely many δ/2-balls
    obtain ⟨t, _, ht_fin, ht_cover⟩ :=
      finite_cover_balls_of_compact (isCompact_univ : IsCompact (Set.univ : Set G)) (half_pos δpos)
    -- Enumerate the finite cover
    let ts : Finset G := ht_fin.toFinset
    have hts_eq : ↑ts = t := ht_fin.coe_toFinset
    -- Enumeration: Fin n ≃ ↥ts
    let n := ts.card
    let e : Fin n ≃ ↥ts := ts.equivFin.symm
    let x : Fin n → G := fun i => (e i : G)
    -- Balls B_i = ball (x_i, δ/2)
    let B : Fin n → Set G := fun i => ball (x i) (δ / 2)
    -- Properties of disjointed B
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
    -- The Riemann sum: S = ∑_{i,j} c_i * conj(c_j) * φ(x_i⁻¹ * x_j) ≥ 0
    let c : Fin n → ℂ := fun i => f (x i) * ((μ.real (disjointed B i)) : ℂ)
    refine ⟨∑ i, ∑ j, c i * conj (c j) * φ ((x i)⁻¹ * x j), ?_, ?_⟩
    · -- S ≥ 0 by PositiveDefinite.sum_nonneg_of_map
      exact hφ.sum_nonneg_of_map Finset.univ x c
    · -- ‖I - S‖ ≤ ε
      -- Partition G × G into cells A_i ×ˢ A_j where A_i = disjointed B i
      have hCover : (Set.univ : Set (G × G)) =
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
        simp only [c, F, map_mul, Complex.conj_ofReal, Complex.ofReal_mul,
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
  · -- Re(I) ≥ 0
    by_contra h
    have hneg : I.re < 0 := lt_of_not_ge h
    obtain ⟨S, hS_nonneg, hS_bound⟩ := hkey (-I.re / 2) (half_pos (neg_pos.mpr hneg))
    have hReS : 0 ≤ S.re := (Complex.nonneg_iff.mp hS_nonneg).1
    have h_abs : |I.re - S.re| ≤ ‖I - S‖ := by
      rw [show I.re - S.re = (I - S).re from rfl]
      exact abs_re_le_norm (I - S)
    have h_bound : |I.re - S.re| ≤ -I.re / 2 := h_abs.trans hS_bound
    have h_lower : I.re ≥ S.re - (-I.re / 2) := by linarith [abs_le.mp h_bound]
    linarith
  · -- Im(I) = 0
    by_contra h
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

/-! ## Mercer-type positive-definite kernels

A kernel `K : X → X → ℂ` is *positive-definite in the Mercer sense* if for all
finite sets `{x_i}` and coefficients `{c_i}`, the quadratic form
`∑ c_i * conj(c_j) * K(x_i, x_j) ≥ 0`.  This generalizes the group-theoretic
notion of positive-definiteness (where `K(x, y) = φ(x⁻¹ * y)` for a PD function
`φ` on a group) to arbitrary spaces, and is the natural notion for the
transfer-matrix kernel which does not factor through a group structure.

The main result is `PositiveDefiniteKernel.integralOperator_nonneg`: a
continuous Mercer-PD kernel on a compact space with a probability measure
defines a positive integral operator.  The proof is the same Riemann-sum
argument as `PositiveDefinite.integralOperator_nonneg`, but using the
Mercer-PD hypothesis directly instead of the group-theoretic PD.

This infrastructure is motivated by the transfer-matrix positivity wiring:
the TM kernel `(Tψ)(u) = ∫ ψ(θ⁻⁰(U⁻,u⁰))·exp(-β·(...)) dμ⁻(U⁻)` is NOT of
the form `φ(u⁻¹·v)` for a PD function `φ` on a group (the reflection map
`θ⁻⁰` is geometric, not group multiplication), so the group-theoretic
`integralOperator_nonneg` cannot be applied directly.  The Mercer version
removes the group-structure requirement, but the remaining work is showing
the TM kernel is Mercer-PD — which itself requires the Peter–Weyl character
expansion (approach (c) in the project docs).  See `Overview.lean` and
`README.md` for the full status. -/

/-- A kernel `K : X → X → ℂ` is positive-definite (Mercer sense): for every
finite set `{x_i}` and coefficients `{c_i}`, the quadratic form
`∑ c_i * conj(c_j) * K(x_i, x_j) ≥ 0`. -/
def PositiveDefiniteKernel {X : Type*} (K : X → X → ℂ) : Prop :=
  ∀ (s : Finset X) (c : X → ℂ),
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * K i j

/-- Helper: sum over fibers of a function.  For any `f : α → X`, the sum
`∑ i ∈ s, w i * Φ (f i)` can be regrouped by the value of `f i`. -/
private lemma sum_fiber_kernel {α X : Type*} [DecidableEq X]
    (s : Finset α) (f : α → X) (w : α → ℂ) (Φ : X → ℂ) :
    ∑ i ∈ s, w i * Φ (f i) =
    ∑ g ∈ s.image f, (∑ i ∈ s.filter (fun i => f i = g), w i) * Φ g := by
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

/-- For a Mercer-PD kernel, the quadratic form with a mapped index set
is non-negative.  This is the key grouping argument: even if `f : α → X` is
not injective, the sum `∑ c_i conj(c_j) K(f i, f j)` is non-negative. -/
lemma PositiveDefiniteKernel.sum_nonneg_of_map
    {X : Type*} {K : X → X → ℂ} (hK : PositiveDefiniteKernel K)
    {α : Type*} (s : Finset α) (f : α → X) (c : α → ℂ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * K (f i) (f j) := by
  classical
  let t := s.image f
  let d : X → ℂ := fun g => ∑ i ∈ s.filter (fun i => f i = g), c i
  have h_conj_d : ∀ h, ∑ j ∈ s.filter (fun j => f j = h), conj (c j) = conj (d h) := by
    intro h
    simp only [d, ← map_sum (starRingEnd ℂ)]
  have h_fiber_i : ∀ j ∈ s, ∑ i ∈ s, c i * K (f i) (f j) =
      ∑ g ∈ t, d g * K g (f j) := by
    intro j hj
    exact sum_fiber_kernel s f c (fun g => K g (f j))
  have h_fiber_j : ∀ g ∈ t, ∑ j ∈ s, conj (c j) * K g (f j) =
      ∑ h ∈ t, conj (d h) * K g h := by
    intro g hg
    rw [sum_fiber_kernel s f (fun j => conj (c j)) (fun h => K g h)]
    apply Finset.sum_congr rfl
    intro h hh
    rw [h_conj_d h]
  calc
    ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * K (f i) (f j)
        = ∑ j ∈ s, ∑ i ∈ s, c i * conj (c j) * K (f i) (f j) := by
      rw [Finset.sum_comm]
    _ = ∑ j ∈ s, conj (c j) * ∑ i ∈ s, c i * K (f i) (f j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have h_rearr : ∑ i ∈ s, c i * conj (c j) * K (f i) (f j) =
          ∑ i ∈ s, conj (c j) * (c i * K (f i) (f j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [mul_comm (c i) (conj (c j)), mul_assoc]
      rw [h_rearr, ← Finset.mul_sum]
    _ = ∑ j ∈ s, conj (c j) * ∑ g ∈ t, d g * K g (f j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [h_fiber_i j hj]
    _ = ∑ g ∈ t, d g * ∑ j ∈ s, conj (c j) * K g (f j) := by
      have h1 : ∑ j ∈ s, conj (c j) * ∑ g ∈ t, d g * K g (f j) =
          ∑ j ∈ s, ∑ g ∈ t, conj (c j) * d g * K g (f j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro g hg
        rw [← mul_assoc]
      have h2 : ∑ j ∈ s, ∑ g ∈ t, conj (c j) * d g * K g (f j) =
          ∑ g ∈ t, ∑ j ∈ s, conj (c j) * d g * K g (f j) := by
        exact Finset.sum_comm ..
      have h3 : ∑ g ∈ t, ∑ j ∈ s, conj (c j) * d g * K g (f j) =
          ∑ g ∈ t, d g * ∑ j ∈ s, conj (c j) * K g (f j) := by
        apply Finset.sum_congr rfl
        intro g hg
        have h_rearr : ∑ j ∈ s, conj (c j) * d g * K g (f j) =
            ∑ j ∈ s, d g * (conj (c j) * K g (f j)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [mul_comm (conj (c j)) (d g), mul_assoc]
        rw [h_rearr, ← Finset.mul_sum]
      rw [h1, h2, h3]
    _ = ∑ g ∈ t, d g * ∑ h ∈ t, conj (d h) * K g h := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [h_fiber_j g hg]
    _ = ∑ g ∈ t, ∑ h ∈ t, d g * conj (d h) * K g h := by
      apply Finset.sum_congr rfl
      intro g hg
      have h_rearr : ∑ h ∈ t, d g * conj (d h) * K g h =
          ∑ h ∈ t, d g * (conj (d h) * K g h) := by
        apply Finset.sum_congr rfl
        intro h hh
        rw [← mul_assoc]
      rw [h_rearr, ← Finset.mul_sum]
    _ ≥ 0 := hK t d

/-- A group-theoretic PD function gives a Mercer-PD kernel `K(x, y) = φ(x⁻¹ * y)`.
This shows the Mercer notion is strictly more general than the group-theoretic one. -/
lemma PositiveDefinite.toPositiveDefiniteKernel
    {G : Type*} [Group G] {φ : G → ℂ} (hφ : PositiveDefinite φ) :
    PositiveDefiniteKernel (fun x y => φ (x⁻¹ * y)) := by
  intro s c
  exact hφ s c

/-- **A continuous Mercer-PD kernel on a compact space defines a positive
integral operator.**

For a compact (pseudo)metric space `X` with probability measure `μ`, a
continuous kernel `K` that is positive-definite in the Mercer sense, and a
continuous function `f`, the integral
`∫∫ f(x) * conj(f(y)) * K(x, y) dμ dμ ≥ 0`.

This is the Mercer-type generalization of
`PositiveDefinite.integralOperator_nonneg`: it removes the group-structure
requirement, so the kernel `K(x, y)` can be any continuous function of two
variables (not just `φ(x⁻¹ * y)` for a PD function on a group).  The proof
is the same Riemann-sum argument: approximate the integral by Riemann sums
(each non-negative by `PositiveDefiniteKernel.sum_nonneg_of_map`) and control
the error via uniform continuity on the compact space `X × X`.

No Haar-measure invariance or group structure is needed. -/
lemma PositiveDefiniteKernel.integralOperator_nonneg
    {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    {K : X → X → ℂ} (hK : PositiveDefiniteKernel K)
    (hK_cont : Continuous (Function.uncurry K))
    {f : X → ℂ} (hf_cont : Continuous f) :
    0 ≤ ∫ x, ∫ y, f x * conj (f y) * K x y ∂μ ∂μ := by
  -- The integrand as a function on X × X
  let F : X × X → ℂ := fun p => f p.1 * conj (f p.2) * K p.1 p.2
  -- F is continuous (product of continuous functions; no group structure needed)
  have hF_cont : Continuous F := by
    have h_fst : Continuous (fun p : X × X => f p.1) := hf_cont.comp continuous_fst
    have h_snd : Continuous (fun p : X × X => f p.2) := hf_cont.comp continuous_snd
    have h_conj_snd : Continuous (fun p : X × X => conj (f p.2)) :=
      Complex.continuous_conj.comp h_snd
    have h_K : Continuous (fun p : X × X => K p.1 p.2) := hK_cont
    convert Continuous.mul (Continuous.mul h_fst h_conj_snd) h_K using 1
    ext p; rfl
  -- X × X is compact
  haveI : CompactSpace (X × X) := inferInstance
  -- F is uniformly continuous (Heine–Cantor)
  have hF_unif : UniformContinuous F :=
    CompactSpace.uniformContinuous_of_continuous hF_cont
  -- F is integrable w.r.t. μ.prod μ (continuous on compact → bounded → integrable)
  have hF_aes : AEStronglyMeasurable F (μ.prod μ) :=
    Continuous.aestronglyMeasurable_of_compactSpace hF_cont
  have hF_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : X × X, ‖F z‖ ≤ C := by
    have h_range_compact : IsCompact (Set.range F) := by
      rw [← Set.image_univ]
      exact isCompact_univ.image hF_cont
    obtain ⟨C, hCpos, hC⟩ := h_range_compact.isBounded.exists_pos_norm_le
    exact ⟨C, hCpos.le, fun z => hC (F z) (Set.mem_range_self _)⟩
  obtain ⟨C, hCnn, hC⟩ := hF_bdd
  have hF_int : Integrable F (μ.prod μ) := by
    apply Integrable.of_bound hF_aes C
    filter_upwards with z using hC z
  -- Convert the iterated integral to a product-measure integral (Fubini)
  have hFub : ∫ z, F z ∂(μ.prod μ) = ∫ x, ∫ y, f x * conj (f y) * K x y ∂μ ∂μ := by
    rw [integral_prod F hF_int]
  rw [← hFub]
  -- Goal: 0 ≤ ∫ z, F z ∂(μ.prod μ)
  set I : ℂ := ∫ z, F z ∂(μ.prod μ)
  -- Strategy: for every ε > 0, build a Riemann sum S ≥ 0 with ‖I - S‖ ≤ ε.
  -- Then Re(I) ≥ 0 and Im(I) = 0, hence 0 ≤ I.
  have hkey : ∀ ε : ℝ, 0 < ε → ∃ S : ℂ, 0 ≤ S ∧ ‖I - S‖ ≤ ε := by
    intro ε εpos
    -- δ from uniform continuity of F on X × X
    obtain ⟨δ, δpos, hδ⟩ := Metric.uniformContinuous_iff.mp hF_unif ε εpos
    -- Cover X by finitely many δ/2-balls
    obtain ⟨t, _, ht_fin, ht_cover⟩ :=
      finite_cover_balls_of_compact (isCompact_univ : IsCompact (Set.univ : Set X)) (half_pos δpos)
    -- Enumerate the finite cover
    let ts : Finset X := ht_fin.toFinset
    have hts_eq : ↑ts = t := ht_fin.coe_toFinset
    -- Enumeration: Fin n ≃ ↥ts
    let n := ts.card
    let e : Fin n ≃ ↥ts := ts.equivFin.symm
    let x : Fin n → X := fun i => (e i : X)
    -- Balls B_i = ball (x_i, δ/2)
    let B : Fin n → Set X := fun i => ball (x i) (δ / 2)
    -- Properties of disjointed B
    have hA_disjoint : Pairwise (Disjoint on disjointed B) := disjoint_disjointed B
    have hA_cover : (Set.univ : Set X) ⊆ ⋃ (i : Fin n), disjointed B i := by
      rw [iUnion_disjointed]
      intro g hg
      simp only [Set.mem_iUnion]
      have hg' := ht_cover hg
      simp only [Set.mem_iUnion₂] at hg'
      obtain ⟨xg, hxg, hg_ball⟩ := hg'
      have hxg_ts : xg ∈ ts := by
        have : xg ∈ (↑ts : Set X) := hts_eq.symm ▸ hxg
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
    -- The Riemann sum: S = ∑_{i,j} c_i * conj(c_j) * K(x_i, x_j) ≥ 0
    let c : Fin n → ℂ := fun i => f (x i) * ((μ.real (disjointed B i)) : ℂ)
    refine ⟨∑ i, ∑ j, c i * conj (c j) * K (x i) (x j), ?_, ?_⟩
    · -- S ≥ 0 by PositiveDefiniteKernel.sum_nonneg_of_map
      exact hK.sum_nonneg_of_map Finset.univ x c
    · -- ‖I - S‖ ≤ ε
      -- Partition X × X into cells A_i ×ˢ A_j where A_i = disjointed B i
      have hCover : (Set.univ : Set (X × X)) =
          ⋃ (ij : Fin n × Fin n), disjointed B ij.1 ×ˢ disjointed B ij.2 := by
        rw [Set.iUnion_prod]
        have hU : (⋃ i, disjointed B i) = (Set.univ : Set X) :=
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
          c ij.1 * conj (c ij.2) * K (x ij.1) (x ij.2) =
          ∫ z in disjointed B ij.1 ×ˢ disjointed B ij.2, F (x ij.1, x ij.2) ∂(μ.prod μ) := by
        intro ij
        rw [setIntegral_const, measureReal_prod_prod]
        simp only [c, F, map_mul, Complex.conj_ofReal, Complex.ofReal_mul,
          Algebra.smul_def, Complex.coe_algebraMap]
        ring
      have hS_part : (∑ i, ∑ j, c i * conj (c j) * K (x i) (x j)) =
          ∑ (ij : Fin n × Fin n),
          ∫ z in disjointed B ij.1 ×ˢ disjointed B ij.2, F (x ij.1, x ij.2) ∂(μ.prod μ) := by
        rw [← Finset.sum_product', Finset.univ_product_univ]
        exact Finset.sum_congr rfl (fun ij _ => h_term ij)
      have hIS : I - ∑ i, ∑ j, c i * conj (c j) * K (x i) (x j) =
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
  · -- Re(I) ≥ 0
    by_contra h
    have hneg : I.re < 0 := lt_of_not_ge h
    obtain ⟨S, hS_nonneg, hS_bound⟩ := hkey (-I.re / 2) (half_pos (neg_pos.mpr hneg))
    have hReS : 0 ≤ S.re := (Complex.nonneg_iff.mp hS_nonneg).1
    have h_abs : |I.re - S.re| ≤ ‖I - S‖ := by
      rw [show I.re - S.re = (I - S).re from rfl]
      exact abs_re_le_norm (I - S)
    have h_bound : |I.re - S.re| ≤ -I.re / 2 := h_abs.trans hS_bound
    have h_lower : I.re ≥ S.re - (-I.re / 2) := by linarith [abs_le.mp h_bound]
    linarith
  · -- Im(I) = 0
    by_contra h
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

/-! ## Algebraic building blocks for Mercer-PD kernels

These lemmas show that Mercer-PD kernels are closed under the algebraic
operations needed to construct the transfer-matrix kernel from the
group-PD Boltzmann factor:
* `PositiveDefiniteKernel.comp`: PD is preserved by composition with `f : X → Y`.
* `PositiveDefiniteKernel.mul`: Schur (Hadamard) product of two Mercer-PD kernels.
* `PositiveDefiniteKernel.smul_nonneg`: non-negative scaling.
* `PositiveDefiniteKernel.finprod`: finite product (n-ary Schur product).
* `PositiveDefiniteKernel.continuous_comp`: continuity is preserved by composition.

Together with `PositiveDefinite.toPositiveDefiniteKernel` (group-PD → Mercer-PD),
these allow the construction: group-PD Boltzmann factor → Mercer-PD kernel →
compose with reflection/projection maps → Mercer-PD TM kernel →
`integralOperator_nonneg`.  See `docs/gap_analysis.md` for the full status. -/

/-- A Mercer-PD kernel is Hermitian: `K(x, y) = conj(K(y, x))`.  This is the
kernel analogue of `PositiveDefinite.conj_inv` for group-PD functions.  The
proof uses the 2-element quadratic form with coefficients `1` and `t` for
varying `t ∈ ℂ`, extracting the real and imaginary constraints. -/
lemma PositiveDefiniteKernel.conj_symm {X : Type*} {K : X → X → ℂ}
    (hK : PositiveDefiniteKernel K) : ∀ x y, K x y = conj (K y x) := by
  intro x y
  classical
  have h_diag : ∀ z, 0 ≤ K z z := fun z => by
    have h := hK (Finset.cons z ∅ (by simp)) (fun _ => 1)
    simp at h
    exact h
  have h_diag_im : ∀ z, (K z z).im = 0 := fun z =>
    (Complex.nonneg_iff.mp (h_diag z)).2.symm
  by_cases hxy : x = y
  · subst hxy; exact (Complex.conj_eq_iff_im.mpr (h_diag_im x)).symm
  · have hne1' : (y : X) ∉ (∅ : Finset X) := by simp
    have hne2 : (x : X) ∉ Finset.cons y ∅ hne1' := by simp [hxy]
    have hS : ∀ t : ℂ,
        0 ≤ K x x + conj t * K x y + t * K y x + (t * conj t) * K y y := by
      intro t
      have h := hK (Finset.cons x (Finset.cons y ∅ hne1') hne2)
          (fun z => if z = x then 1 else t)
      have hsum : (∑ i ∈ Finset.cons x (Finset.cons y ∅ hne1') hne2,
          ∑ j ∈ Finset.cons x (Finset.cons y ∅ hne1') hne2,
          (if i = x then 1 else t) * conj (if j = x then 1 else t) * K i j) =
          K x x + conj t * K x y + t * K y x + (t * conj t) * K y y := by
        simp only [Finset.sum_cons, Finset.sum_empty,
          ite_true, if_neg (Ne.symm hxy), one_mul, mul_one, map_one]
        ring
      rw [hsum] at h
      exact h
    have h_im_sum : (K x y).im + (K y x).im = 0 := by
      have key := (Complex.nonneg_iff.mp (hS 1)).2
      have hkey : K x x + conj 1 * K x y + 1 * K y x + (1 * conj 1) * K y y =
          K x x + K x y + K y x + K y y := by
        simp only [map_one, one_mul, mul_one]
      rw [hkey] at key
      have h2 : (K x x + K x y + K y x + K y y).im =
          (K x x).im + (K x y).im + (K y x).im + (K y y).im := by
        simp [Complex.add_im]
      rw [h2, h_diag_im x, h_diag_im y] at key
      linarith
    have h_re_diff : (K y x).re - (K x y).re = 0 := by
      have key := (Complex.nonneg_iff.mp (hS Complex.I)).2
      have heq : K x x + conj Complex.I * K x y + Complex.I * K y x +
          (Complex.I * conj Complex.I) * K y y =
          K x x + K y y + Complex.I * (K y x - K x y) := by
        simp [Complex.conj_I]; ring
      rw [heq] at key
      have h2 : (K x x + K y y + Complex.I * (K y x - K x y)).im =
          (K x x).im + (K y y).im + ((K y x).re - (K x y).re) := by
        simp [Complex.add_im, Complex.mul_im, Complex.sub_re, Complex.sub_im,
          Complex.I_re, Complex.I_im]
      rw [h2, h_diag_im x, h_diag_im y] at key
      linarith
    apply Complex.ext
    · rw [Complex.conj_re]; linarith
    · rw [Complex.conj_im]; linarith

/-- The constant-one kernel is Mercer-PD. -/
lemma PositiveDefiniteKernel.one (X : Type*) :
    PositiveDefiniteKernel (fun (_ _ : X) => (1 : ℂ)) := by
  intro s c
  have hsum : (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * 1) =
      conj (∑ i ∈ s, c i) * (∑ i ∈ s, c i) := by
    simp only [mul_one]
    rw [← Finset.sum_mul_sum, ← map_sum (starRingEnd ℂ) c s, mul_comm]
  rw [hsum, ← Complex.normSq_eq_conj_mul_self]
  exact Complex.zero_le_real.mpr (Complex.normSq_nonneg _)

/-- A Mercer-PD kernel gives a positive-semidefinite matrix on any finite subset.
This is the kernel analogue of `PositiveDefinite.matrix_posSemidef`. -/
private lemma PositiveDefiniteKernel.matrix_posSemidef {X : Type*}
    {K : X → X → ℂ} (hK : PositiveDefiniteKernel K) (s : Finset X) :
    Matrix.PosSemidef (fun (i j : ↥s) => K i.val j.val : Matrix ↥s ↥s ℂ) := by
  haveI : DecidableEq ↥s := Classical.decEq _
  classical
  refine (Matrix.posSemidef_iff_dotProduct_mulVec
      (M := (fun (i j : ↥s) => K i.val j.val : Matrix ↥s ↥s ℂ))).mpr ?_
  refine ⟨?_, ?_⟩
  · apply Matrix.IsHermitian.ext
    intro i j
    show conj (K j.val i.val) = K i.val j.val
    rw [hK.conj_symm i.val j.val]
  · intro x
    let c' : X → ℂ := fun g => if hg : g ∈ s then conj (x ⟨g, hg⟩) else 0
    have hPD := hK s c'
    have hc'val : ∀ i : ↥s, c' i.val = conj (x i) := by
      intro i
      simp only [c', dif_pos i.property]
    have hc'conj : ∀ j : ↥s, conj (c' j.val) = x j := by
      intro j
      rw [hc'val j]
      exact star_star _
    let M : Matrix ↥s ↥s ℂ := fun i j => K i.val j.val
    have hdot : star x ⬝ᵥ (M *ᵥ x) =
        (∑ i ∈ s, ∑ j ∈ s, c' i * conj (c' j) * K i j) := by
      rw [Matrix.dot_mulVec_eq_sum_sum, Finset.sum_comm]
      simp only [M, Pi.star_apply, Complex.star_def]
      conv_rhs => rw [← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro i _
      conv_rhs => rw [← Finset.sum_coe_sort]
      simp only [hc'val, Complex.conj_conj]
      apply Finset.sum_congr rfl
      intro j _
      exact mul_right_comm _ _ _
    rw [hdot]
    exact hPD

/-- **Schur product theorem for Mercer-PD kernels.**  The pointwise product of
two Mercer-PD kernels is again Mercer-PD.  This is the kernel analogue of
`PositiveDefinite.mul` and follows from the Hadamard (Schur) product theorem
for positive-semidefinite matrices. -/
lemma PositiveDefiniteKernel.mul {X : Type*} {K1 K2 : X → X → ℂ}
    (hK1 : PositiveDefiniteKernel K1) (hK2 : PositiveDefiniteKernel K2) :
    PositiveDefiniteKernel (fun x y => K1 x y * K2 x y) := by
  intro s c
  classical
  haveI : DecidableEq ↥s := Classical.decEq _
  let A : Matrix ↥s ↥s ℂ := fun i j => K1 i.val j.val
  let B : Matrix ↥s ↥s ℂ := fun i j => K2 i.val j.val
  let v : ↥s → ℂ := fun i => c i.val
  have hA : Matrix.PosSemidef A := hK1.matrix_posSemidef s
  have hB : Matrix.PosSemidef B := hK2.matrix_posSemidef s
  have hAB : Matrix.PosSemidef (A ⊙ B) := Matrix.PosSemidef.hadamard hA hB
  let w : ↥s → ℂ := fun i => conj (v i)
  have hquad : 0 ≤ star w ⬝ᵥ ((A ⊙ B) *ᵥ w) :=
    Matrix.PosSemidef.dotProduct_mulVec_nonneg hAB w
  have htarget : (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * (K1 i j * K2 i j)) =
      star w ⬝ᵥ ((A ⊙ B) *ᵥ w) := by
    rw [Matrix.dot_mulVec_eq_sum_sum]
    conv_rhs => rw [Finset.sum_comm]
    simp only [Pi.star_apply, Complex.star_def, A, B, w, v,
      Complex.conj_conj]
    conv_lhs => rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro i _
    conv_lhs => rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_right_comm _ _ _
  rw [htarget]
  exact hquad

/-- Non-negative scaling preserves Mercer-PD. -/
lemma PositiveDefiniteKernel.smul_nonneg {X : Type*} {K : X → X → ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hK : PositiveDefiniteKernel K) :
    PositiveDefiniteKernel (fun x y => (r : ℂ) * K x y) := by
  intro s c
  have h := hK s c
  have hsum : (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * ((r : ℂ) * K i j)) =
      (r : ℂ) * (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * K i j) := by
    simp [Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
  rw [hsum]
  have h_nonneg_complex : (0 : ℂ) ≤ (r : ℂ) := by
    rw [Complex.nonneg_iff]
    constructor
    · simpa using hr
    · simp
  exact mul_nonneg h_nonneg_complex h

/-- **Finite product of Mercer-PD kernels is Mercer-PD** (n-ary Schur product
theorem).  This is the kernel analogue of `PositiveDefinite.finprod`. -/
lemma PositiveDefiniteKernel.finprod {ι X : Type*} (s : Finset ι)
    (f : ι → X → X → ℂ) (hf : ∀ i ∈ s, PositiveDefiniteKernel (f i)) :
    PositiveDefiniteKernel (fun x y => ∏ i ∈ s, f i x y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact PositiveDefiniteKernel.one X
  | insert a s ha ih =>
    have hPDa : PositiveDefiniteKernel (f a) := hf a (Finset.mem_insert_self a s)
    have hPDs : PositiveDefiniteKernel (fun x y => ∏ i ∈ s, f i x y) :=
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have heq : (fun x y => ∏ i ∈ insert a s, f i x y) =
        fun x y => f a x y * ∏ i ∈ s, f i x y := by
      funext x y; rw [Finset.prod_insert ha]
    rw [heq]
    exact PositiveDefiniteKernel.mul hPDa hPDs

/-- **Mercer-PD is preserved by composition with a function on both arguments.**
If `K` is a Mercer-PD kernel on `Y` and `f : X → Y`, then
`fun x y => K (f x) (f y)` is a Mercer-PD kernel on `X`.  This is the key
operation for constructing the TM kernel: the Boltzmann factor (group-PD on the
full link group) is converted to a Mercer-PD kernel via
`toPositiveDefiniteKernel`, then composed with the reflection/projection maps. -/
lemma PositiveDefiniteKernel.comp {X Y : Type*} {K : Y → Y → ℂ}
    (hK : PositiveDefiniteKernel K) (f : X → Y) :
    PositiveDefiniteKernel (fun x y => K (f x) (f y)) := by
  intro s c
  exact hK.sum_nonneg_of_map s f c

/-- **Continuity of a Mercer-PD kernel is preserved by composition with a
continuous function on both arguments.**  If `K` is continuous (as an uncurried
function `Y × Y → ℂ`) and `f : X → Y` is continuous, then
`fun x y => K (f x) (f y)` is continuous (as an uncurried function
`X × X → ℂ`).  This is needed to apply `integralOperator_nonneg` to the
composed TM kernel. -/
lemma PositiveDefiniteKernel.continuous_comp {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    {K : Y → Y → ℂ} (hK_cont : Continuous (Function.uncurry K))
    (f : X → Y) (hf_cont : Continuous f) :
    Continuous (Function.uncurry (fun x y => K (f x) (f y))) := by
  have hf_fst : Continuous (fun p : X × X => f p.1) := hf_cont.comp continuous_fst
  have hf_snd : Continuous (fun p : X × X => f p.2) := hf_cont.comp continuous_snd
  have hf_prod : Continuous (fun p : X × X => (f p.1, f p.2)) :=
    Continuous.prodMk hf_fst hf_snd
  exact hK_cont.comp hf_prod

/-! ## Character-expansion positivity (abstract lemma)

The following abstract lemma is the pure measure-theory scaffold for the
character-orthogonality approach to closing `transferMatrixPositivity_axiom`.
It uses no group structure and no character orthogonality — only the
measure-preserving change of variables and the fact that `f` is real-valued
(so `conj (f x) = (f x : ℂ)`).

If a kernel `K : X → Y → ℂ` has a finite separable decomposition
`K(x, y) = ∑_i a_i · Φ_i(x) · conj(Φ_i(θ y))` with `a_i ≥ 0` and `θ`
measure-preserving (`θ_*ν = μ`), then for real-valued `f`:
`∫∫ f(x) · f(θ y) · K(x, y) dν(y) dμ(x) = ∑_i a_i · ‖∫ f · Φ_i dμ‖² ≥ 0`.

This is the abstract scaffold that the concrete Peter–Weyl character expansion
of the transfer-matrix kernel would plug into.  See `docs/gap_analysis.md` for
the full analysis of the remaining wiring (which requires the Clebsch–Gordan
decomposition for products of characters of the same link variable). -/

/-- **Character-expansion positivity (abstract lemma).**  If a kernel
`K : X → Y → ℂ` has a finite separable decomposition
`K(x, y) = ∑_i a_i · Φ_i(x) · conj(Φ_i(θ y))` with `a_i ≥ 0` and `θ`
measure-preserving (`θ_*ν = μ`), then for real-valued `f`:
`∫∫ f(x) · f(θ y) · K(x, y) dν(y) dμ(x) = ∑_i a_i · ‖∫ f · Φ_i dμ‖²`.

No group structure, no character orthogonality — only the measure-preserving
change of variables and the fact that `f` is real-valued. -/
lemma character_expansion_positivity
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (θ : Y → X) (hθ : MeasurePreserving θ ν μ)
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ)
    (Φ : ι → X → ℂ) (f : X → ℝ)
    (hΦ_meas : ∀ i, AEStronglyMeasurable (Φ i) μ)
    (hf_meas : AEStronglyMeasurable (fun x => (f x : ℂ)) μ)
    (hfΦ_int : ∀ i, Integrable (fun x => (f x : ℂ) * Φ i x) μ)
    (K : X → Y → ℂ)
    (hK : ∀ x y, K x y = ∑ i, (a i : ℂ) * (Φ i x * conj (Φ i (θ y)))) :
    ∫ x, ∫ y, (f x : ℂ) * (f (θ y) : ℂ) * K x y ∂ν ∂μ =
      ↑(∑ i, a i * ‖∫ x, (f x : ℂ) * Φ i x ∂μ‖^2) := by
  -- Helper: AEStronglyMeasurable of conj(Φ i)
  have hΦ_conj_meas : ∀ i, AEStronglyMeasurable (fun x => conj (Φ i x)) μ :=
    fun i => Complex.continuous_conj.comp_aestronglyMeasurable (hΦ_meas i)
  -- Helper: AEStronglyMeasurable of (f * conj(Φ i))
  have hfΦ_conj_meas : ∀ i, AEStronglyMeasurable (fun x => (f x : ℂ) * conj (Φ i x)) μ :=
    fun i => hf_meas.mul (hΦ_conj_meas i)
  -- Helper: Integrable of (f * conj(Φ i)) — derived from hfΦ_int via norm equality
  have hfΦ_conj_int : ∀ i, Integrable (fun x => (f x : ℂ) * conj (Φ i x)) μ := by
    intro i
    refine ⟨hfΦ_conj_meas i, ?_⟩
    have hnorm : ∀ x, ‖(f x : ℂ) * conj (Φ i x)‖ = ‖(f x : ℂ) * Φ i x‖ := fun x => by
      rw [norm_mul, norm_mul, Complex.norm_conj]
    have hfi := (hfΦ_int i).2
    rw [hasFiniteIntegral_iff_norm] at hfi ⊢
    rw [lintegral_congr_ae (ae_of_all μ (fun x => by rw [hnorm]))]
    exact hfi
  -- Helper: Integrable of (f(θy) * conj(Φ i (θy))) w.r.t. ν
  have hfΦ_conj_θ_int : ∀ i, Integrable (fun y => (f (θ y) : ℂ) * conj (Φ i (θ y))) ν :=
    fun i => hθ.integrable_comp (hfΦ_conj_meas i) |>.mpr (hfΦ_conj_int i)
  -- Helper: change of variables ∫_ν f(θy)·conj(Φ_i(θy)) dy = ∫_μ f(x)·conj(Φ_i(x)) dx
  have hchange_var : ∀ i,
      ∫ y, (f (θ y) : ℂ) * conj (Φ i (θ y)) ∂ν = ∫ x, (f x : ℂ) * conj (Φ i x) ∂μ := by
    intro i
    have hfm := hfΦ_conj_meas i
    rw [← hθ.map_eq] at hfm ⊢
    exact (integral_map hθ.measurable.aemeasurable hfm).symm
  -- Helper: ∫_μ f·conj(Φ_i) = conj(∫_μ f·Φ_i)  (since f is real-valued)
  have hconj_int : ∀ i,
      ∫ x, (f x : ℂ) * conj (Φ i x) ∂μ = conj (∫ x, (f x : ℂ) * Φ i x ∂μ) := by
    intro i
    have heq : ∀ x, (f x : ℂ) * conj (Φ i x) = conj ((f x : ℂ) * Φ i x) := by
      intro x
      symm
      rw [map_mul (starRingEnd ℂ), Complex.conj_ofReal]
    rw [show (∫ x, (f x : ℂ) * conj (Φ i x) ∂μ) =
        ∫ x, conj ((f x : ℂ) * Φ i x) ∂μ from by congr 1 with x; exact heq x]
    exact Complex.conjCLE.integral_comp_comm _
  -- Main computation
  -- Substitute hK into the integrand
  have hK_subst : ∀ x y,
      (f x : ℂ) * (f (θ y) : ℂ) * K x y =
        ∑ i, (a i : ℂ) * ((f x : ℂ) * Φ i x) * ((f (θ y) : ℂ) * conj (Φ i (θ y))) := by
    intro x y
    rw [hK, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  -- Integrability of the inner-integral function (for fixed x, each i)
  have hinner_int : ∀ (x : X) (i : ι),
      Integrable (fun y => (a i : ℂ) * ((f x : ℂ) * Φ i x) *
        ((f (θ y) : ℂ) * conj (Φ i (θ y)))) ν := by
    intro x i
    have h := (hfΦ_conj_θ_int i).mul_const ((a i : ℂ) * ((f x : ℂ) * Φ i x))
    have heq_fun : (fun y => (a i : ℂ) * ((f x : ℂ) * Φ i x) *
        ((f (θ y) : ℂ) * conj (Φ i (θ y)))) =
        (fun y => ((f (θ y) : ℂ) * conj (Φ i (θ y))) *
          ((a i : ℂ) * ((f x : ℂ) * Φ i x))) := by
      funext y; ring
    rw [heq_fun]; exact h
  -- Step 1: rewrite the LHS using hK_subst
  rw [show (∫ x, ∫ y, (f x : ℂ) * (f (θ y) : ℂ) * K x y ∂ν ∂μ) =
        ∫ x, ∫ y, ∑ i, (a i : ℂ) * ((f x : ℂ) * Φ i x) *
          ((f (θ y) : ℂ) * conj (Φ i (θ y))) ∂ν ∂μ from by
    congr 1 with x
    congr 1 with y
    exact hK_subst x y]
  -- Step 2: exchange the sum with the inner integral (over y)
  rw [show (∫ x, ∫ y, ∑ i, (a i : ℂ) * ((f x : ℂ) * Φ i x) *
        ((f (θ y) : ℂ) * conj (Φ i (θ y))) ∂ν ∂μ) =
      ∫ x, ∑ i, (a i : ℂ) * ((f x : ℂ) * Φ i x) *
        ∫ y, (f (θ y) : ℂ) * conj (Φ i (θ y)) ∂ν ∂μ from by
    congr 1 with x
    rw [integral_finsetSum Finset.univ (fun i _ => hinner_int x i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [show (fun y => (a i : ℂ) * ((f x : ℂ) * Φ i x) *
        ((f (θ y) : ℂ) * conj (Φ i (θ y)))) =
        (fun y => ((a i : ℂ) * ((f x : ℂ) * Φ i x)) •
          ((f (θ y) : ℂ) * conj (Φ i (θ y)))) from by
      funext y; rw [smul_eq_mul, mul_assoc]]
    rw [integral_smul, smul_eq_mul, mul_assoc]]
  -- Step 3: apply change of variables to the inner integral
  simp only [hchange_var]
  -- Step 4: apply conj integral
  simp only [hconj_int]
  -- Step 5: exchange the sum with the outer integral (over x)
  have houter_int : ∀ i, Integrable (fun x => (a i : ℂ) * ((f x : ℂ) * Φ i x) *
      conj (∫ x, (f x : ℂ) * Φ i x ∂μ)) μ := by
    intro i
    have h := (hfΦ_int i).mul_const ((a i : ℂ) * conj (∫ x, (f x : ℂ) * Φ i x ∂μ))
    have heq_fun : (fun x => (a i : ℂ) * ((f x : ℂ) * Φ i x) *
        conj (∫ x, (f x : ℂ) * Φ i x ∂μ)) =
        (fun x => ((f x : ℂ) * Φ i x) *
          ((a i : ℂ) * conj (∫ x, (f x : ℂ) * Φ i x ∂μ))) := by
      funext x; ring
    rw [heq_fun]; exact h
  rw [show (∫ x, ∑ i, (a i : ℂ) * ((f x : ℂ) * Φ i x) *
        conj (∫ x, (f x : ℂ) * Φ i x ∂μ) ∂μ) =
      ∑ i, ∫ x, (a i : ℂ) * ((f x : ℂ) * Φ i x) *
        conj (∫ x, (f x : ℂ) * Φ i x ∂μ) ∂μ from by
    rw [integral_finsetSum Finset.univ (fun i _ => houter_int i)]]
  -- Step 6: convert RHS ↑(∑ i, a i * ‖...‖^2) to ∑ i, ↑(a i * ‖...‖^2)
  rw [Complex.ofReal_sum]
  -- Step 7: match term-by-term
  apply Finset.sum_congr rfl
  intro i _
  rw [show (fun x => (a i : ℂ) * ((f x : ℂ) * Φ i x) *
        conj (∫ x, (f x : ℂ) * Φ i x ∂μ)) =
      (fun x => ((a i : ℂ) * conj (∫ x, (f x : ℂ) * Φ i x ∂μ)) •
        ((f x : ℂ) * Φ i x)) from by
    funext x; rw [smul_eq_mul]; ring]
  rw [integral_smul, smul_eq_mul]
  -- Step 8: rearrange to conj(z) * z = normSq z = ‖z‖^2 and coerce
  rw [show ((a i : ℂ) * conj (∫ x, (f x : ℂ) * Φ i x ∂μ) *
        ∫ x, (f x : ℂ) * Φ i x ∂μ) =
      (a i : ℂ) * (conj (∫ x, (f x : ℂ) * Φ i x ∂μ) *
        ∫ x, (f x : ℂ) * Φ i x ∂μ) from by ring]
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Complex.ofReal_mul]

/-- **Corollary: the character-expansion integral is non-negative.**  Under the
same hypotheses as `character_expansion_positivity` (in particular `a i ≥ 0`),
the integral `∫∫ f(x)·f(θ y)·K(x, y) dν dμ` is non-negative, since it equals a
sum of non-negative weights `a i` times squared norms `‖∫ f·Φ_i‖²`. -/
lemma character_expansion_nonneg
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (θ : Y → X) (hθ : MeasurePreserving θ ν μ)
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (Φ : ι → X → ℂ) (f : X → ℝ)
    (hΦ_meas : ∀ i, AEStronglyMeasurable (Φ i) μ)
    (hf_meas : AEStronglyMeasurable (fun x => (f x : ℂ)) μ)
    (hfΦ_int : ∀ i, Integrable (fun x => (f x : ℂ) * Φ i x) μ)
    (K : X → Y → ℂ)
    (hK : ∀ x y, K x y = ∑ i, (a i : ℂ) * (Φ i x * conj (Φ i (θ y)))) :
    0 ≤ ∫ x, ∫ y, (f x : ℂ) * (f (θ y) : ℂ) * K x y ∂ν ∂μ := by
  rw [character_expansion_positivity μ ν θ hθ ι a Φ f hΦ_meas hf_meas hfΦ_int K hK]
  have hnn : 0 ≤ ∑ i, a i * ‖∫ x, (f x : ℂ) * Φ i x ∂μ‖^2 := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (ha i) (sq_nonneg _)
  exact Complex.zero_le_real.mpr hnn

/-! ## Shared-variable character-expansion positivity

The following lemma generalizes `character_expansion_nonneg` to the setting
where a variable `z` is **shared** between the `x` and `y` integrals (not a
product measure).  This is the structure that arises in the Lüscher
transfer-matrix positivity proof: after the σ-twist disappears from the test
function `g` (because `f` satisfies `dependsOnlyOnPosSpatialInterface`), the
integral becomes `∫_z ∫_x ∫_y g(x,z) · g(y,z) · K(x,y,z) dμ dμ dν` where `z`
(the spatial interface links) is shared between the `x` (positive links) and
`y` (reflected positive links) integrals.

For each fixed `z`, `character_expansion_positivity` (with `θ = id`) gives the
inner double integral as `↑(∑_i a(z,i) · ‖∫_x g(x,z) · Φ_i(z,x) dμ‖²)`; since
`a(z,i) ≥ 0` this is a non-negative real (as a complex), and integrating over
`z` preserves non-negativity.  The key Mathlib lemmas are `integral_congr_ae`
(no integrability hypothesis) to rewrite the outer integral pointwise,
`integral_ofReal` (`@[norm_cast]`, no integrability hypothesis) to pull the
`ofReal` out of the integral, and `integral_nonneg` for the final real
non-negativity.  See §8.11.37 in the design doc for the full analysis. -/

/-- **Shared-variable character-expansion non-negativity.**  If a kernel
`K : X → X → Z → ℂ` has, for each `z`, a finite separable decomposition
`K(x, y, z) = ∑_i a(z,i) · Φ_i(z,x) · conj(Φ_i(z,y))` with `a(z,i) ≥ 0`, then
for real-valued `g : X → Z → ℝ`:
`∫_z ∫_x ∫_y g(x,z) · g(y,z) · K(x,y,z) dμ dμ dν ≥ 0`.

For each fixed `z` this is `character_expansion_positivity` with `θ = id`; the
inner double integral equals `↑(∑_i a(z,i) · ‖∫_x g(x,z)·Φ_i(z,x) dμ‖²)`, a
non-negative real embedded in `ℂ`, and integrating over `z` preserves
non-negativity. -/
lemma character_expansion_nonneg_shared
    {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure Z) [SigmaFinite μ] [SigmaFinite ν]
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (a : Z → ι → ℝ) (ha : ∀ z i, 0 ≤ a z i)
    (Φ : ι → Z → X → ℂ) (g : X → Z → ℝ)
    (hΦ_meas : ∀ i z, AEStronglyMeasurable (Φ i z) μ)
    (hg_meas : ∀ z, AEStronglyMeasurable (fun x => (g x z : ℂ)) μ)
    (hgΦ_int : ∀ z i, Integrable (fun x => (g x z : ℂ) * Φ i z x) μ)
    (K : X → X → Z → ℂ)
    (hK : ∀ x y z, K x y z = ∑ i, (a z i : ℂ) * (Φ i z x * conj (Φ i z y))) :
    0 ≤ ∫ z, ∫ x, ∫ y, (g x z : ℂ) * (g y z : ℂ) * K x y z ∂μ ∂μ ∂ν := by
  -- Pointwise: for each z, the inner double integral equals
  -- ↑(∑ i, a z i * ‖∫ g(x,z)·Φ_i(z,x) dμ‖²) by character_expansion_positivity
  -- with θ = id (so f(θ y) = f(y) = g(y,z)).
  have heq : ∀ z,
      (∫ x, ∫ y, (g x z : ℂ) * (g y z : ℂ) * K x y z ∂μ ∂μ) =
        ↑(∑ i, a z i * ‖∫ x, (g x z : ℂ) * Φ i z x ∂μ‖^2) := by
    intro z
    exact character_expansion_positivity μ μ id (MeasurePreserving.id μ) ι (a z)
      (fun i x => Φ i z x) (fun x => g x z) (fun i => hΦ_meas i z) (hg_meas z)
      (fun i => hgΦ_int z i) (fun x y => K x y z) (fun x y => hK x y z)
  -- Rewrite the outer integral using the pointwise (hence a.e.) equality.
  rw [integral_congr_ae (ae_of_all ν heq)]
  -- The pointwise equality produces `Complex.ofReal` coercions, while
  -- `integral_ofReal` is stated with `RCLike.ofReal`; they are defeq
  -- (`RCLike.ofReal_eq_complex_ofReal`) but not syntactically equal, so we
  -- normalise the coercion first, then pull the `ofReal` out of the integral.
  simp only [← RCLike.ofReal_eq_complex_ofReal]
  rw [integral_ofReal]
  -- The integral of a non-negative real function is non-negative.
  apply Complex.zero_le_real.mpr
  apply integral_nonneg
  intro z
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (ha z i) (sq_nonneg _)

/-! ## Step 4: cascade integral non-negativity

The 2D character-level cascade `luscher_2site_2D_cascade_charlevel`
(`PositiveDefinite.lean`) reduces the 2-site integral to
`∑_ν cg(s₁,s₂,ν)·cg(t₁,t₂,ν)·(1/dims ν)·χ_ν(W·V)`.  The following
lemma shows this kernel, integrated against `f(W)·f(V⁻¹)`, is
non-negative.  The key is the trace expansion
`χ_ν(W·V) = ∑_{a,b} (ρ_ν W)_{ab}·conj((ρ_ν V⁻¹)_{ab})` (unitarity),
which puts the kernel into the separable form required by
`character_expansion_nonneg` with `θ = inv` (measure-preserving by
`IsInvInvariant`).  The coefficients
`cg(s₁,s₂,ν)·cg(t₁,t₂,ν)·(1/dims ν) ≥ 0` come from `hcg` and
`hDims`. -/

/-- Helper: trace expansion of `χ_ν(W·V)` using unitarity.
`χ_ν(W·V) = Tr(ρ_ν(W)·ρ_ν(V)) = ∑_{a,b} (ρ_ν W)_{ab}·(ρ_ν V)_{ba}`,
and `(ρ_ν V)_{ba} = conj((ρ_ν V⁻¹)_{ab})` by `repMatrixElement_inv`. -/
lemma repCharacter_trace_expand
    {G : Type*} [Group G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hU : IsUnitaryRepresentation ρ) (W V : G) :
    repCharacter ρ (W * V) =
      ∑ a : Fin n, ∑ b : Fin n, (ρ W) a b * conj ((ρ V⁻¹) a b) := by
  have htrace_mul : ∀ (A B : Matrix (Fin n) (Fin n) ℂ),
      Matrix.trace (A * B) = ∑ i : Fin n, ∑ j : Fin n, A i j * B j i := by
    intro A B; simp [Matrix.trace, Matrix.mul_apply]
  rw [repCharacter, MonoidHom.map_mul, htrace_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have h := repMatrixElement_inv ρ hU V a b
  rw [h, Complex.conj_conj]

/-- **Step 4: the cascade integral is non-negative.**  The kernel
`K(W,V) = ∑_ν cg(s₁,s₂,ν)·cg(t₁,t₂,ν)·(1/dims ν)·χ_ν(W·V)` (the output
of `luscher_2site_2D_cascade_charlevel`) integrated against
`f(W)·f(V⁻¹)` is non-negative, since `χ_ν(W·V)` expands via unitarity
into a separable form `∑_{a,b} (ρ_ν W)_{ab}·conj((ρ_ν V⁻¹)_{ab})` with
non-negative coefficients `cg·cg·(1/dims ν) ≥ 0`, and `θ = inv` is
measure-preserving (`IsInvInvariant`). -/
lemma cascade_integral_nonneg
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (hθ : MeasurePreserving (Inv.inv : G → G) μ μ)
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (cg : ι → ι → ι → ℝ)
    (hcg : ∀ s t w, 0 ≤ cg s t w)
    (s₁ s₂ t₁ t₂ : ι)
    (f : G → ℝ)
    (hf_meas : AEStronglyMeasurable (fun g => (f g : ℂ)) μ)
    (hρ_meas : ∀ ν (a b : Fin (dims ν)), AEStronglyMeasurable (fun g => (ρ ν g) a b) μ)
    (hfρ_int : ∀ ν (a b : Fin (dims ν)), Integrable (fun g => (f g : ℂ) * (ρ ν g) a b) μ) :
    0 ≤ ∫ W, ∫ V,
      (f W : ℂ) * (f V⁻¹ : ℂ) *
      ∑ ν : ι, (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν : ℂ) *
        ((1 / dims ν : ℂ) * repCharacter (ρ ν) (W * V)) ∂μ ∂μ := by
  -- Sigma index type: ι' = Σ ν, Fin(dims ν) × Fin(dims ν)
  -- Use the sigma type directly (no let/set binding) so Finset.univ_sigma_univ
  -- and the Fintype instance from inferInstance agree.
  set_option maxHeartbeats 400000 in
  letI : Fintype (Σ ν : ι, Fin (dims ν) × Fin (dims ν)) := inferInstance
  haveI : DecidableEq (Σ ν : ι, Fin (dims ν) × Fin (dims ν)) := Classical.decEq _
  -- Coefficients: a'(i) = cg(s₁,s₂,i.1)·cg(t₁,t₂,i.1)/dims(i.1) ≥ 0
  let a' : (Σ ν : ι, Fin (dims ν) × Fin (dims ν)) → ℝ :=
    fun i => cg s₁ s₂ i.1 * cg t₁ t₂ i.1 / dims i.1
  -- Basis: Φ'(i)(g) = (ρ_{i.1} g)_{i.2.1, i.2.2}
  let Φ' : (Σ ν : ι, Fin (dims ν) × Fin (dims ν)) → G → ℂ :=
    fun i g => (ρ i.1) g i.2.1 i.2.2
  -- Kernel: K(W,V) = ∑_ν cg·cg·(1/dims)·χ_ν(W·V)
  let K : G → G → ℂ := fun W V =>
    ∑ ν, (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν : ℂ) *
      ((1 / dims ν : ℂ) * repCharacter (ρ ν) (W * V))
  -- Non-negativity of coefficients
  have ha' : ∀ i, 0 ≤ a' i := by
    intro i
    exact div_nonneg (mul_nonneg (hcg s₁ s₂ i.1) (hcg t₁ t₂ i.1)) (Nat.cast_nonneg _)
  -- Kernel expansion: K(W,V) = ∑_i a'(i)·Φ'(i)(W)·conj(Φ'(i)(V⁻¹))
  have hK : ∀ W V, K W V =
      ∑ i : Σ ν : ι, Fin (dims ν) × Fin (dims ν), (a' i : ℂ) * (Φ' i W * conj (Φ' i (V⁻¹))) := by
    intro W V
    -- Step 1: Expand K to nested form ∑ ν, ∑ a, ∑ b, ...
    have hK_nested : K W V = ∑ ν, ∑ a, ∑ b,
        (cg s₁ s₂ ν * cg t₁ t₂ ν / dims ν : ℂ) * ((ρ ν W) a b * conj ((ρ ν (V⁻¹)) a b)) := by
      show ∑ ν, (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν : ℂ) *
          ((1 / dims ν : ℂ) * repCharacter (ρ ν) (W * V)) =
        ∑ ν, ∑ a, ∑ b,
          (cg s₁ s₂ ν * cg t₁ t₂ ν / dims ν : ℂ) * ((ρ ν W) a b * conj ((ρ ν (V⁻¹)) a b))
      apply Finset.sum_congr rfl
      intro ν _
      rw [repCharacter_trace_expand (ρ ν) (hU ν) W V]
      rw [show ((cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν : ℂ) * ((1 / dims ν : ℂ) *
            (∑ a, ∑ b, (ρ ν W) a b * conj ((ρ ν V⁻¹) a b)))) =
          ((cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν : ℂ) * (1 / dims ν : ℂ)) *
            (∑ a, ∑ b, (ρ ν W) a b * conj ((ρ ν V⁻¹) a b)) from by ring]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    -- Step 2: Convert nested form to sigma form
    rw [hK_nested]
    have hstep1 : (∑ ν, ∑ a, ∑ b, (cg s₁ s₂ ν * cg t₁ t₂ ν / dims ν : ℂ) *
          ((ρ ν W) a b * conj ((ρ ν (V⁻¹)) a b))) =
        ∑ ν, ∑ p ∈ (Finset.univ : Finset (Fin (dims ν) × Fin (dims ν))),
          (cg s₁ s₂ ν * cg t₁ t₂ ν / dims ν : ℂ) *
          ((ρ ν W) p.1 p.2 * conj ((ρ ν (V⁻¹)) p.1 p.2)) := by
      apply Finset.sum_congr rfl
      intro ν _
      rw [← Finset.sum_product', Finset.univ_product_univ]
    rw [hstep1, Finset.sum_sigma', Finset.univ_sigma_univ]
    apply Finset.sum_congr rfl
    rintro i _
    simp only [a', Φ']
    push_cast [Complex.ofReal_div, Complex.ofReal_mul]
    ring
  -- Measurability of basis functions
  have hΦ'_meas : ∀ i, AEStronglyMeasurable (Φ' i) μ := by
    intro i
    exact hρ_meas i.1 i.2.1 i.2.2
  -- Integrability of f · basis functions
  have hfΦ'_int : ∀ i, Integrable (fun g => (f g : ℂ) * Φ' i g) μ := by
    intro i
    exact hfρ_int i.1 i.2.1 i.2.2
  -- Apply character_expansion_nonneg with θ = Inv.inv (measure-preserving by hθ)
  exact character_expansion_nonneg μ μ (Inv.inv : G → G) hθ _ a' ha' Φ' f
    hΦ'_meas hf_meas hfΦ'_int K hK

#print axioms cascade_integral_nonneg

/-! ## Step 4 (generalized): character-kernel integral non-negativity

The following lemma generalizes `cascade_integral_nonneg` to arbitrary non-negative
coefficients `coeff : ι → ℝ` (instead of the specific `cg s₁ s₂ ν · cg t₁ t₂ ν · (1/dims ν)`
form from the 2-character CG cascade).  This is the key non-negativity lemma for the
Lüscher mechanism (step 4 of the formalization plan, §8.11.45): after the Lüscher cascade
integrates out the temporal links, the resulting kernel has the form
`∑_ν a_ν · χ_ν(W·V)` with `a_ν ≥ 0`, and this lemma gives the non-negativity of the
integral `∫∫ f(W)·f(V⁻¹)·K(W,V) ≥ 0`.

The proof is identical in structure to `cascade_integral_nonneg`: expand `χ_ν(W·V)` via
`repCharacter_trace_expand` (unitarity) into the separable form
`∑_{a,b} (ρ_ν W)_{ab}·conj((ρ_ν V⁻¹)_{ab})`, then apply `character_expansion_nonneg`
with `θ = inv` (measure-preserving by `hθ`).  The only difference is the coefficient:
`a'(i) = coeff(i.1)` instead of `cg s₁ s₂ i.1 · cg t₁ t₂ i.1 / dims i.1`. -/

/-- **Generalized character-kernel integral non-negativity.** For a compact group `G`
with probability measure `μ` (invariant under inversion), a finite family of irreducible
unitary reps `ρ_ν` of dimension `dims ν`, and non-negative coefficients `coeff : ι → ℝ`
with `coeff ν ≥ 0`, the integral

    ∫ W, ∫ V, (f W : ℂ) * (f V⁻¹ : ℂ) * ∑_ν (coeff ν : ℂ) * χ_ν(W * V) ∂μ ∂μ

is non-negative.  The key is the trace expansion
`χ_ν(W·V) = ∑_{a,b} (ρ_ν W)_{ab}·conj((ρ_ν V⁻¹)_{ab})` (unitarity),
which puts the kernel into the separable form required by
`character_expansion_nonneg` with `θ = inv` (measure-preserving by `hθ`).

This generalizes `cascade_integral_nonneg` (which has the specific coefficient
`cg s₁ s₂ ν · cg t₁ t₂ ν · (1/dims ν)`) to arbitrary non-negative coefficients. -/
lemma character_kernel_integral_nonneg
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (hθ : MeasurePreserving (Inv.inv : G → G) μ μ)
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (coeff : ι → ℝ) (hcoeff : ∀ ν, 0 ≤ coeff ν)
    (f : G → ℝ)
    (hf_meas : AEStronglyMeasurable (fun g => (f g : ℂ)) μ)
    (hρ_meas : ∀ ν (a b : Fin (dims ν)), AEStronglyMeasurable (fun g => (ρ ν g) a b) μ)
    (hfρ_int : ∀ ν (a b : Fin (dims ν)), Integrable (fun g => (f g : ℂ) * (ρ ν g) a b) μ) :
    0 ≤ ∫ W, ∫ V,
      (f W : ℂ) * (f V⁻¹ : ℂ) *
      ∑ ν : ι, (coeff ν : ℂ) * repCharacter (ρ ν) (W * V) ∂μ ∂μ := by
  set_option maxHeartbeats 400000 in
  letI : Fintype (Σ ν : ι, Fin (dims ν) × Fin (dims ν)) := inferInstance
  haveI : DecidableEq (Σ ν : ι, Fin (dims ν) × Fin (dims ν)) := Classical.decEq _
  let a' : (Σ ν : ι, Fin (dims ν) × Fin (dims ν)) → ℝ :=
    fun i => coeff i.1
  let Φ' : (Σ ν : ι, Fin (dims ν) × Fin (dims ν)) → G → ℂ :=
    fun i g => (ρ i.1) g i.2.1 i.2.2
  let K : G → G → ℂ := fun W V =>
    ∑ ν, (coeff ν : ℂ) * repCharacter (ρ ν) (W * V)
  have ha' : ∀ i, 0 ≤ a' i := fun i => hcoeff i.1
  have hK : ∀ W V, K W V =
      ∑ i : Σ ν : ι, Fin (dims ν) × Fin (dims ν), (a' i : ℂ) * (Φ' i W * conj (Φ' i (V⁻¹))) := by
    intro W V
    have hK_nested : K W V = ∑ ν, ∑ c, ∑ d,
        (coeff ν : ℂ) * ((ρ ν W) c d * conj ((ρ ν (V⁻¹)) c d)) := by
      show ∑ ν, (coeff ν : ℂ) * repCharacter (ρ ν) (W * V) =
        ∑ ν, ∑ c, ∑ d,
          (coeff ν : ℂ) * ((ρ ν W) c d * conj ((ρ ν (V⁻¹)) c d))
      apply Finset.sum_congr rfl
      intro ν _
      rw [repCharacter_trace_expand (ρ ν) (hU ν) W V]
      rw [show ((coeff ν : ℂ) *
            (∑ a, ∑ b, (ρ ν W) a b * conj ((ρ ν (V⁻¹)) a b))) =
          (∑ a, ∑ b, (coeff ν : ℂ) *
            ((ρ ν W) a b * conj ((ρ ν (V⁻¹)) a b))) from by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]]
    rw [hK_nested]
    have hstep1 : (∑ ν, ∑ c, ∑ d, (coeff ν : ℂ) *
          ((ρ ν W) c d * conj ((ρ ν (V⁻¹)) c d))) =
        ∑ ν, ∑ p ∈ (Finset.univ : Finset (Fin (dims ν) × Fin (dims ν))),
          (coeff ν : ℂ) *
          ((ρ ν W) p.1 p.2 * conj ((ρ ν (V⁻¹)) p.1 p.2)) := by
      apply Finset.sum_congr rfl
      intro ν _
      rw [← Finset.sum_product', Finset.univ_product_univ]
    rw [hstep1, Finset.sum_sigma', Finset.univ_sigma_univ]
  have hΦ'_meas : ∀ i, AEStronglyMeasurable (Φ' i) μ := fun i => hρ_meas i.1 i.2.1 i.2.2
  have hfΦ'_int : ∀ i, Integrable (fun g => (f g : ℂ) * Φ' i g) μ := fun i => hfρ_int i.1 i.2.1 i.2.2
  exact character_expansion_nonneg μ μ (Inv.inv : G → G) hθ _ a' ha' Φ' f
    hΦ'_meas hf_meas hfΦ'_int K hK

#print axioms character_kernel_integral_nonneg

/-! ## Step 3+4 combination: cascade kernel integral non-negativity

The following lemma combines `luscher_2site_cascade_coeff` (step 3: the Lüscher cascade
integrates out temporal links `g₀, g₁`, producing a kernel `∑_s F(s,s)·(1/d_s)·χ_s(W·V)`)
with `character_kernel_integral_nonneg` (step 4: non-negativity of `∫∫ f(W)·f(V⁻¹)·K(W,V)` for
any kernel `K(W,V) = ∑_ν a_ν·χ_ν(W·V)` with `a_ν ≥ 0`).

The result: for arbitrary non-negative coefficients `F : ι → ι → ℝ` with `F s t ≥ 0`, the
full 4-fold integral (outer `W, V` × inner cascade `g₀, g₁`) is non-negative:

    0 ≤ ∫ W ∫ V (f W)·(f V⁻¹)·[∫ g₀ ∫ g₁ ∑_{s,t} F(s,t)·χ_s(g₀·W·g₁⁻¹)·χ_t(g₁·V·g₀⁻¹)] ∂μ ∂μ ∂μ ∂μ

The proof: (1) the inner cascade equals `∑_s (F s s / dims s)·χ_s(W·V)` by
`luscher_2site_cascade_coeff` + coefficient conversion; (2) the coefficient
`F s s / dims s ≥ 0` (since `F s s ≥ 0` and `dims s > 0`); (3) apply
`character_kernel_integral_nonneg` with `coeff s = F s s / dims s`. 0 sorries, 0 new axioms. -/
lemma luscher_2site_cascade_integral_nonneg
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (hθ : MeasurePreserving (Inv.inv : G → G) μ μ)
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (F : ι → ι → ℝ) (hF : ∀ s t, 0 ≤ F s t)
    (f : G → ℝ)
    (hf_meas : AEStronglyMeasurable (fun g => (f g : ℂ)) μ)
    (hρ_meas : ∀ ν (a b : Fin (dims ν)), AEStronglyMeasurable (fun g => (ρ ν g) a b) μ)
    (hfρ_int : ∀ ν (a b : Fin (dims ν)), Integrable (fun g => (f g : ℂ) * (ρ ν g) a b) μ) :
    0 ≤ ∫ W, ∫ V, (f W : ℂ) * (f V⁻¹ : ℂ) *
      ∫ g₀, ∫ g₁, ∑ s, ∑ t, (F s t : ℂ) *
        (repCharacter (ρ s) (g₀ * W * g₁⁻¹) * repCharacter (ρ t) (g₁ * V * g₀⁻¹)) ∂μ ∂μ ∂μ ∂μ := by
  let coeff : ι → ℝ := fun s => F s s / dims s
  have hcoeff : ∀ s, 0 ≤ coeff s := fun s => div_nonneg (hF s s) (Nat.cast_nonneg _)
  have hKernel : ∀ W V,
      (∫ g₀, ∫ g₁, ∑ s, ∑ t, (F s t : ℂ) *
        (repCharacter (ρ s) (g₀ * W * g₁⁻¹) * repCharacter (ρ t) (g₁ * V * g₀⁻¹)) ∂μ ∂μ) =
      ∑ s, (coeff s : ℂ) * repCharacter (ρ s) (W * V) := by
    intro W V
    rw [luscher_2site_cascade_coeff μ ι dims hDims ρ hU hIrr F hF W V]
    apply Finset.sum_congr rfl
    intro s _
    have hne : (dims s : ℂ) ≠ 0 := by
      have h : 0 < (dims s : ℂ) := by exact mod_cast (hDims s)
      exact ne_of_gt h
    rw [show coeff s = F s s / dims s from rfl]
    push_cast
    field_simp
  rw [show (∫ W, ∫ V, (f W : ℂ) * (f V⁻¹ : ℂ) *
        (∫ g₀, ∫ g₁, ∑ s, ∑ t, (F s t : ℂ) *
          (repCharacter (ρ s) (g₀ * W * g₁⁻¹) * repCharacter (ρ t) (g₁ * V * g₀⁻¹)) ∂μ ∂μ) ∂μ ∂μ) =
      (∫ W, ∫ V, (f W : ℂ) * (f V⁻¹ : ℂ) *
        (∑ s, (coeff s : ℂ) * repCharacter (ρ s) (W * V)) ∂μ ∂μ) from by
    congr 1 with W
    congr 1 with V
    rw [hKernel]]
  exact character_kernel_integral_nonneg μ hθ ι dims hDims ρ hU coeff hcoeff
    f hf_meas hρ_meas hfρ_int

#print axioms luscher_2site_cascade_integral_nonneg

/-! ## Key finding: 3-site cascade does NOT directly combine with character_kernel_integral_nonneg

The 3-site cascade (`luscher_3site_cascade_coeff` in `PositiveDefinite.lean`) evaluates to
`∑_s F(s,s,s) · (1/d_s)² · χ_s(W₀·W₁·W₂)` — a CONSTANT (not a kernel in W, V).
The outer integral `∫ W ∫ V f(W)·f(V⁻¹)·[constant]` = `[constant]·|∫f|²`,
and the constant is a sum of characters (complex in general), so the product is
NOT necessarily non-negative.

This contrasts with the 2-site case, where the cascade produces a KERNEL
`K(W,V) = ∑_s coeff_s · χ_s(W·V)` (a function of W·V), which matches
`character_kernel_integral_nonneg` directly.

The 3-site cascade coefficient lemma is correct and useful for evaluating cascades,
but the non-negativity combination requires a different approach: either (a) a generalized
non-negativity lemma for kernels of the form `χ_s(W·M·V)` with a fixed bridge M, (b) the
specific lattice structure where the cascade produces `χ_s(W·V)` directly, or (c) pairwise
decomposition using the 2-site cascade repeatedly. See §8.11.49 of the design doc. -/

end YangMills
