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
  group), the kernel does not factor through the group structure.  Closing the
  axiom requires either (a) a more general PD kernel theory (Mercer-type, not
  group-theoretic), (b) showing the TM kernel reduces to the group-theoretic
  form (unlikely given the reflection structure), or (c) applying the Peter–Weyl
  character expansion directly to the TM kernel.  See the status notes in
  `Overview.lean` and `README.md`.

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
import YangMills.Proofs.PositiveDefinite

namespace YangMills

open Finset MeasureTheory Complex Metric

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

end YangMills
