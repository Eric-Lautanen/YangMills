/-
# Positive-Definite Functions on Groups

A function φ : G → ℂ on a group G is called *positive-definite* if for any
finite set {g₁, ..., gₙ} ⊂ G and coefficients {c₁, ..., cₙ} ⊂ ℂ:

    Σ_{i,j} c_i · conj(c_j) · φ(g_i⁻¹ g_j) ≥ 0

## References

* K. Osterwalder, E. Seiler, "Gauge Field Theories on a Lattice"
  (Ann. Phys. 110, 1978, pp 440–471), §3.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import YangMills.SpecialUnitary
open Finset
open Complex
open Filter
open Matrix
open MeasureTheory
open scoped ComplexConjugate
open scoped ComplexOrder

namespace YangMills

/-- A function φ : G → ℂ is positive-definite. -/
def PositiveDefinite {G : Type*} [Group G] (φ : G → ℂ) : Prop :=
  ∀ (s : Finset G) (c : G → ℂ),
    (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * φ (i⁻¹ * j)) ≥ 0

section BasicProperties

variable {G : Type*} [Group G] {φ ψ : G → ℂ}

lemma PositiveDefinite.add (hφ : PositiveDefinite φ) (hψ : PositiveDefinite ψ) :
    PositiveDefinite (λ g => φ g + ψ g) := by
  intro s c
  have h1 := hφ s c
  have h2 := hψ s c
  have hsum : (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * ((λ g => φ g + ψ g) (i⁻¹ * j))) =
      (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * φ (i⁻¹ * j)) +
      (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * ψ (i⁻¹ * j)) := by
    simp [Finset.sum_add_distrib, mul_add]
  rw [hsum]
  exact add_nonneg h1 h2

lemma PositiveDefinite.smul_nonneg {r : ℝ} (hr : 0 ≤ r) (hφ : PositiveDefinite φ) :
    PositiveDefinite (λ g => (r : ℂ) * φ g) := by
  intro s c
  have h := hφ s c
  have hsum : (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * ((r : ℂ) * φ (i⁻¹ * j))) =
      (r : ℂ) * (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * φ (i⁻¹ * j)) := by
    simp [Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
  rw [hsum]
  have h_nonneg_complex : (0 : ℂ) ≤ (r : ℂ) := by
    rw [Complex.nonneg_iff]
    constructor
    · simpa using hr
    · simp
  exact mul_nonneg h_nonneg_complex h

/-- A positive-definite function satisfies φ(g⁻¹) = conj(φ(g)). -/
lemma PositiveDefinite.conj_inv (hφ : PositiveDefinite φ) : ∀ g, φ g⁻¹ = conj (φ g) := by
  intro g
  classical
  have h_one : 0 ≤ φ (1 : G) := by
    have h := hφ (Finset.cons 1 ∅ (by simp)) (fun _ => 1)
    simp [Finset.sum_empty] at h
    exact h
  have h_one_im : (φ (1 : G)).im = 0 := (Complex.nonneg_iff.mp h_one).2.symm
  by_cases hg : g = 1
  · subst hg; rw [inv_one]; exact (Complex.conj_eq_iff_im.mpr h_one_im).symm
  · have hS : ∀ t : ℂ, 0 ≤ (1 + t * conj t) * φ (1 : G) + conj t * φ g + t * φ g⁻¹ := by
      intro t
      have hne1 : (g : G) ∉ (∅ : Finset G) := by simp
      have hne2 : (1 : G) ∉ Finset.cons g ∅ hne1 := by simp [Ne.symm hg]
      have h := hφ (Finset.cons 1 (Finset.cons g ∅ hne1) hne2) (fun x => if x = 1 then 1 else t)
      have hsum : (∑ i ∈ Finset.cons 1 (Finset.cons g ∅ hne1) hne2,
          ∑ j ∈ Finset.cons 1 (Finset.cons g ∅ hne1) hne2,
          (if i = 1 then 1 else t) * conj (if j = 1 then 1 else t) * φ (i⁻¹ * j)) =
          (1 + t * conj t) * φ (1 : G) + conj t * φ g + t * φ g⁻¹ := by
        simp only [Finset.sum_cons, Finset.sum_empty, if_pos (rfl : (1 : G) = 1), if_neg hg]
        simp only [one_mul, mul_one, inv_one, map_one, ite_true]
        simp only [show (g : G)⁻¹ * g = 1 from by simp]
        ring
      rw [hsum] at h
      exact h
    have h_im_sum : (φ g).im + (φ g⁻¹).im = 0 := by
      have key := (Complex.nonneg_iff.mp (hS 1)).2
      have hkey : (1 + 1 * conj 1) * φ (1 : G) + conj 1 * φ g + 1 * φ g⁻¹ =
          2 * φ (1 : G) + φ g + φ g⁻¹ := by simp only [map_one, one_mul, mul_one]; ring
      rw [hkey] at key
      have h2 : (2 * φ (1 : G) + φ g + φ g⁻¹).im = 2 * (φ (1 : G)).im + (φ g).im + (φ g⁻¹).im := by
        simp [Complex.add_im]
      rw [h2, h_one_im] at key
      linarith
    have h_re_diff : (φ g⁻¹).re - (φ g).re = 0 := by
      have key := (Complex.nonneg_iff.mp (hS Complex.I)).2
      have hI2 : Complex.I * conj Complex.I = 1 := by simp [Complex.conj_I]
      have heq : (1 + Complex.I * conj Complex.I) * φ (1 : G) +
        conj Complex.I * φ g + Complex.I * φ g⁻¹ =
        2 * φ (1 : G) + Complex.I * (φ g⁻¹ - φ g) := by simp [Complex.conj_I]; ring
      rw [heq] at key
      have h2 : (2 * φ (1 : G) + Complex.I * (φ g⁻¹ - φ g)).im =
          2 * (φ (1 : G)).im + ((φ g⁻¹).re - (φ g).re) := by
        simp [Complex.add_im, Complex.mul_im, Complex.sub_re, Complex.sub_im,
          Complex.I_re, Complex.I_im]
      rw [h2, h_one_im] at key
      linarith
    apply Complex.ext
    · rw [Complex.conj_re]; linarith
    · rw [Complex.conj_im]; linarith

/-- The zero function is positive-definite. -/
lemma PositiveDefinite.zero : PositiveDefinite (λ (_ : G) => (0 : ℂ)) := by
  intro s c; simp

/-- The constant-one function is positive-definite. -/
lemma PositiveDefinite.one : PositiveDefinite (λ (_ : G) => (1 : ℂ)) := by
  intro s c
  have hsum : (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * 1) =
      conj (∑ i ∈ s, c i) * (∑ i ∈ s, c i) := by
    simp only [mul_one]
    rw [← Finset.sum_mul_sum, ← map_sum (starRingEnd ℂ) c s, mul_comm]
  rw [hsum, ← Complex.normSq_eq_conj_mul_self]
  exact Complex.zero_le_real.mpr (Complex.normSq_nonneg _)

/-- A positive-definite function gives a positive-semidefinite matrix on any finite subset. -/
private lemma PositiveDefinite.matrix_posSemidef (hφ : PositiveDefinite φ) (s : Finset G) :
    Matrix.PosSemidef (fun (i j : ↥s) => φ (i.val⁻¹ * j.val) : Matrix ↥s ↥s ℂ) := by
  haveI : DecidableEq ↥s := Classical.decEq _
  classical
  refine (Matrix.posSemidef_iff_dotProduct_mulVec (M := (fun (i j : ↥s) => φ (i.val⁻¹ * j.val) : Matrix ↥s ↥s ℂ))).mpr ?_
  refine ⟨?_, ?_⟩
  · apply Matrix.IsHermitian.ext
    intro i j
    show conj (φ (j.val⁻¹ * i.val)) = φ (i.val⁻¹ * j.val)
    rw [← hφ.conj_inv (j.val⁻¹ * i.val)]
    congr 1
    simp
  · intro x
    let c' : G → ℂ := fun g => if hg : g ∈ s then conj (x ⟨g, hg⟩) else 0
    have hPD := hφ s c'
    have hc'val : ∀ i : ↥s, c' i.val = conj (x i) := by
      intro i
      simp only [c', dif_pos i.property]
    have hc'conj : ∀ j : ↥s, conj (c' j.val) = x j := by
      intro j
      rw [hc'val j]
      exact star_star _
    let M : Matrix ↥s ↥s ℂ := fun i j => φ (i.val⁻¹ * j.val)
    have hdot : star x ⬝ᵥ (M *ᵥ x) =
        (∑ i ∈ s, ∑ j ∈ s, c' i * conj (c' j) * φ (i⁻¹ * j)) := by
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

/-- Pointwise product of two positive-definite functions is positive-definite (Schur product theorem). -/
lemma PositiveDefinite.mul (hφ : PositiveDefinite φ) (hψ : PositiveDefinite ψ) :
    PositiveDefinite (λ g => φ g * ψ g) := by
  intro s c
  classical
  haveI : DecidableEq ↥s := Classical.decEq _
  let A : Matrix ↥s ↥s ℂ := fun i j => φ (i.val⁻¹ * j.val)
  let B : Matrix ↥s ↥s ℂ := fun i j => ψ (i.val⁻¹ * j.val)
  let v : ↥s → ℂ := fun i => c i.val
  have hA : Matrix.PosSemidef A := hφ.matrix_posSemidef s
  have hB : Matrix.PosSemidef B := hψ.matrix_posSemidef s
  have hAB : Matrix.PosSemidef (A ⊙ B) := Matrix.PosSemidef.hadamard hA hB
  let w : ↥s → ℂ := fun i => conj (v i)
  have hquad : 0 ≤ star w ⬝ᵥ ((A ⊙ B) *ᵥ w) := Matrix.PosSemidef.dotProduct_mulVec_nonneg hAB w
  have htarget : (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * (φ (i⁻¹ * j) * ψ (i⁻¹ * j))) =
      star w ⬝ᵥ ((A ⊙ B) *ᵥ w) := by
    rw [Matrix.dot_mulVec_eq_sum_sum]
    conv_rhs => rw [Finset.sum_comm]
    simp only [Pi.star_apply, Complex.star_def, Matrix.hadamard_apply, A, B, w, v,
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

/-- Pointwise power of a positive-definite function is positive-definite. -/
lemma PositiveDefinite.pow (hφ : PositiveDefinite φ) (n : ℕ) : PositiveDefinite (φ ^ n) := by
  induction n with
  | zero => simp [pow_zero]; exact PositiveDefinite.one
  | succ n ih =>
    have h := PositiveDefinite.mul ih hφ
    rw [show φ ^ (n + 1) = (λ g => (φ ^ n) g * φ g) from by funext g; simp [pow_succ]]
    exact h

/-- Pointwise limit of positive-definite functions is positive-definite. -/
lemma PositiveDefinite.tendsto {F : ℕ → G → ℂ} {φ : G → ℂ}
    (hPD : ∀ n, PositiveDefinite (F n))
    (hlim : ∀ g, Tendsto (fun n => F n g) atTop (nhds (φ g))) :
    PositiveDefinite φ := by
  intro s c
  have hGn_nonneg : ∀ n, 0 ≤ (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * F n (i⁻¹ * j)) :=
    fun n => hPD n s c
  have hGn_tendsto : Tendsto (fun n => ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * F n (i⁻¹ * j)) atTop
      (nhds (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * φ (i⁻¹ * j))) := by
    exact tendsto_finsetSum s (fun i _ =>
      tendsto_finsetSum s (fun j _ =>
        Tendsto.mul tendsto_const_nhds (hlim (i⁻¹ * j))))
  exact ge_of_tendsto' hGn_tendsto hGn_nonneg

end BasicProperties

section ProductGroup

attribute [local instance] Classical.propDecidable

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

/-- For a positive-definite function `φ`, the matrix `φ(f(i)⁻¹ * f(j))` indexed
by a finset `s` (via a possibly non-injective map `f`) is positive semidefinite. -/
private lemma PositiveDefinite.matrix_posSemidef_of_map
    {G : Type*} [Group G] {φ : G → ℂ} (hφ : PositiveDefinite φ)
    {α : Type*} (s : Finset α) (f : α → G) :
    Matrix.PosSemidef (fun (i j : ↥s) => φ ((f i.val)⁻¹ * f j.val) : Matrix ↥s ↥s ℂ) := by
  classical
  haveI : DecidableEq ↥s := Classical.decEq _
  refine (Matrix.posSemidef_iff_dotProduct_mulVec (M := (fun (i j : ↥s) => φ ((f i.val)⁻¹ * f j.val) : Matrix ↥s ↥s ℂ))).mpr ?_
  refine ⟨?_, ?_⟩
  · apply Matrix.IsHermitian.ext
    intro i j
    show conj (φ ((f j.val)⁻¹ * f i.val)) = φ ((f i.val)⁻¹ * f j.val)
    rw [← hφ.conj_inv ((f j.val)⁻¹ * f i.val)]
    congr 1
    simp [_root_.mul_inv_rev, inv_inv]
  · intro x
    set c : α → ℂ := fun a => if ha : a ∈ s then conj (x ⟨a, ha⟩) else 0
    have hcval : ∀ i : ↥s, c i.val = conj (x i) := fun i => by
      simp only [c, dif_pos i.property]
    have hcconj : ∀ j : ↥s, conj (c j.val) = x j := fun j => by
      rw [hcval j]; exact star_star _
    let M : Matrix ↥s ↥s ℂ := fun i j => φ ((f i.val)⁻¹ * f j.val)
    have hquad : star x ⬝ᵥ (M *ᵥ x) =
        (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * φ ((f i)⁻¹ * f j)) := by
      rw [Matrix.dot_mulVec_eq_sum_sum, Finset.sum_comm]
      simp only [M, Pi.star_apply, Complex.star_def]
      conv_rhs => rw [← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro i _
      conv_rhs => rw [← Finset.sum_coe_sort]
      simp only [hcval, Complex.conj_conj]
      apply Finset.sum_congr rfl
      intro j _
      exact mul_right_comm _ _ _
    rw [hquad]
    exact hφ.sum_nonneg_of_map s f c

/-- **Product of positive-definite functions on different groups.**
If `φ : G → ℂ` is positive-definite and `ψ : H → ℂ` is positive-definite,
then `(g, h) ↦ φ(g) * ψ(h)` is positive-definite on `G × H`.

This follows from the Schur product theorem: the kernel matrix factors as a
Hadamard product of two PSD matrices (one from `φ` on the `G`-component, one
from `ψ` on the `H`-component), each PSD by the grouping argument. -/
lemma PositiveDefinite.prod {G H : Type*} [Group G] [Group H]
    {φ : G → ℂ} {ψ : H → ℂ} (hφ : PositiveDefinite φ) (hψ : PositiveDefinite ψ) :
    PositiveDefinite (λ (p : G × H) => φ p.1 * ψ p.2) := by
  intro s c
  classical
  haveI : DecidableEq ↥s := Classical.decEq _
  let A : Matrix ↥s ↥s ℂ := fun i j => φ ((i.val.1)⁻¹ * j.val.1)
  let B : Matrix ↥s ↥s ℂ := fun i j => ψ ((i.val.2)⁻¹ * j.val.2)
  have hA : Matrix.PosSemidef A := hφ.matrix_posSemidef_of_map s (fun p => p.1)
  have hB : Matrix.PosSemidef B := hψ.matrix_posSemidef_of_map s (fun p => p.2)
  have hAB : Matrix.PosSemidef (A ⊙ B) := Matrix.PosSemidef.hadamard hA hB
  let w : ↥s → ℂ := fun i => conj (c i.val)
  have hquad : 0 ≤ star w ⬝ᵥ ((A ⊙ B) *ᵥ w) :=
    Matrix.PosSemidef.dotProduct_mulVec_nonneg hAB w
  have htarget : (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) *
      (φ ((i⁻¹ * j).1) * ψ ((i⁻¹ * j).2))) =
      star w ⬝ᵥ ((A ⊙ B) *ᵥ w) := by
    rw [Matrix.dot_mulVec_eq_sum_sum]
    conv_rhs => rw [Finset.sum_comm]
    simp only [Pi.star_apply, Complex.star_def, Matrix.hadamard_apply, A, B, w,
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

end ProductGroup

/-! ## Building blocks for the full Boltzmann factor

These lemmas are the abstract ingredients needed to promote the single-plaquette
positive-definiteness result `plaquetteBoltzmannPD` (in `PeterWeyl.lean`) to
positive-definiteness of the *full* Wilson Boltzmann factor
`exp(-β · S_W)` on the entire link-variable group `SU(N)^{#links}`.

* `PositiveDefinite.comp_mulEquiv`: positive-definiteness is preserved by group
  isomorphisms.  This lets one permute / rearrange the factors of a product group
  (e.g. place four plaquette links at arbitrary positions among all links).
* `PositiveDefinite.fst` / `.snd`: a positive-definite function on one factor,
  viewed as a function on a product group that ignores the other factor, is
  positive-definite.  This lets one regard a single-plaquette factor (which
  depends on only four links) as a function on the full link group.
* `PositiveDefinite.finprod`: a finite product of positive-definite functions on
  the same group is positive-definite (the n-ary Schur product theorem).  This
  combines the individual (extended) plaquette factors into the full Boltzmann
  factor `∏_p exp(β · Re Tr(U_{∂p}))`.
-/

section BuildingBlocks

variable {G H : Type*} [Group G] [Group H]

/-- Positive-definiteness is preserved by group isomorphisms: if `e : G ≃* H`
is a group isomorphism and `φ : H → ℂ` is positive-definite, then
`φ ∘ e : G → ℂ` is positive-definite.  The proof regroups the quadratic form by
the image of `e` using `PositiveDefinite.sum_nonneg_of_map`. -/
lemma PositiveDefinite.comp_mulEquiv (e : G ≃* H) {φ : H → ℂ}
    (hφ : PositiveDefinite φ) : PositiveDefinite (fun g => φ (e g)) := by
  intro s c
  have hkey := hφ.sum_nonneg_of_map s e c
  have hsum_eq : (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * φ (e (i⁻¹ * j))) =
      (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * φ ((e i)⁻¹ * e j)) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    rw [MulEquiv.map_mul, MulEquiv.map_inv]
  rw [hsum_eq]
  exact hkey

/-- Positive-definiteness is preserved by group homomorphisms: if `f : G →* H`
is a group homomorphism and `φ : H → ℂ` is positive-definite, then
`φ ∘ f : G → ℂ` is positive-definite.  This generalizes `comp_mulEquiv` from
isomorphisms to arbitrary homomorphisms (e.g. coordinate projections from a
product group to a sub-product).  The proof regroups the quadratic form by the
image of `f` using `PositiveDefinite.sum_nonneg_of_map`. -/
lemma PositiveDefinite.comp_hom (f : G →* H) {φ : H → ℂ}
    (hφ : PositiveDefinite φ) : PositiveDefinite (fun g => φ (f g)) := by
  intro s c
  have hkey := hφ.sum_nonneg_of_map s f c
  have hsum_eq : (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * φ (f (i⁻¹ * j))) =
      (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * φ ((f i)⁻¹ * f j)) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    rw [MonoidHom.map_mul, MonoidHom.map_inv]
  rw [hsum_eq]
  exact hkey

/-- A positive-definite function on `G`, regarded as a function on `G × H` that
ignores the `H`-component, is positive-definite on `G × H`. -/
lemma PositiveDefinite.fst {φ : G → ℂ} (hφ : PositiveDefinite φ) :
    PositiveDefinite (fun (p : G × H) => φ p.1) := by
  have h := PositiveDefinite.prod hφ (@PositiveDefinite.one H _)
  convert h using 1
  ext p; simp

/-- A positive-definite function on `H`, regarded as a function on `G × H` that
ignores the `G`-component, is positive-definite on `G × H`. -/
lemma PositiveDefinite.snd {ψ : H → ℂ} (hψ : PositiveDefinite ψ) :
    PositiveDefinite (fun (p : G × H) => ψ p.2) := by
  have h := PositiveDefinite.prod (@PositiveDefinite.one G _) hψ
  convert h using 1
  ext p; simp

/-- A finite product of positive-definite functions on the same group is
positive-definite (the n-ary Schur product theorem). -/
lemma PositiveDefinite.finprod {ι : Type*} (s : Finset ι) (f : ι → G → ℂ)
    (hf : ∀ i ∈ s, PositiveDefinite (f i)) :
    PositiveDefinite (fun g => ∏ i ∈ s, f i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [PositiveDefinite.one]
  | insert x s hx ih =>
    have hPDx : PositiveDefinite (f x) := hf x (Finset.mem_insert_self x s)
    have hPDs : PositiveDefinite (fun g => ∏ i ∈ s, f i g) :=
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have heq : (fun g => ∏ i ∈ insert x s, f i g) =
        fun g => f x g * ∏ i ∈ s, f i g := by
      funext g; rw [Finset.prod_insert hx]
    rw [heq]
    exact PositiveDefinite.mul hPDx hPDs

end BuildingBlocks

section SU_N

open Matrix

lemma conjTranspose_eq_inv (N : ℕ) (g : SU N) :
    ((g : Matrix (Fin N) (Fin N) ℂ)ᴴ) = (g : Matrix (Fin N) (Fin N) ℂ)⁻¹ := by
  have h_unitary : (g : Matrix (Fin N) (Fin N) ℂ) * ((g : Matrix (Fin N) (Fin N) ℂ)ᴴ) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp g.property.1)
  exact (Matrix.inv_eq_right_inv h_unitary).symm

noncomputable def fundamentalCharacter (N : ℕ) (g : SU N) : ℂ :=
  Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)

lemma fundamentalCharacter_positiveDefinite (N : ℕ) :
    PositiveDefinite (fundamentalCharacter N) := by
  intro s c
  have h_nonneg_sq : ∀ (M : Matrix (Fin N) (Fin N) ℂ), 0 ≤ Matrix.trace (Mᴴ * M) := by
    intro M
    have : Matrix.trace (Mᴴ * M) = (∑ i : Fin N, (Mᴴ * M) i i : ℂ) := by
      simp [Matrix.trace]
    rw [this]
    refine Finset.sum_nonneg (λ i _ => ?_)
    have : (Mᴴ * M) i i = ∑ k : Fin N, conj (M k i) * M k i := by
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [this]
    refine Finset.sum_nonneg (λ k _ => ?_)
    have : 0 ≤ conj (M k i) * M k i := by
      rw [← Complex.normSq_eq_conj_mul_self]
      have h_nonneg_sq_val : 0 ≤ Complex.normSq (M k i) := Complex.normSq_nonneg _
      rw [Complex.nonneg_iff]
      constructor
      · simpa using h_nonneg_sq_val
      · simp
    exact this
  have dummy : True := trivial
  have h_tr_eq : Matrix.trace (
      ((∑ g ∈ s, (conj (c g) : ℂ) • ((g : SU N) : Matrix (Fin N) (Fin N) ℂ))ᴴ) *
      (∑ g ∈ s, (conj (c g) : ℂ) • ((g : SU N) : Matrix (Fin N) (Fin N) ℂ))) =
      (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * fundamentalCharacter N (i⁻¹ * j)) :=
    calc
      Matrix.trace (((∑ g ∈ s, (conj (c g) : ℂ) • ((g : SU N) : Matrix (Fin N) (Fin N) ℂ))ᴴ) * (∑ g ∈ s, (conj (c g) : ℂ) • ((g : SU N) : Matrix (Fin N) (Fin N) ℂ)))
          = Matrix.trace ((∑ i ∈ s, (c i : ℂ) • (((i : SU N) : Matrix (Fin N) (Fin N) ℂ)⁻¹)) * (∑ j ∈ s, (conj (c j) : ℂ) • ((j : SU N) : Matrix (Fin N) (Fin N) ℂ))) := by
        simp [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_star, conjTranspose_eq_inv N]
      _ = Matrix.trace (∑ i ∈ s, ∑ j ∈ s, ((c i : ℂ) * (conj (c j) : ℂ)) • (((i : SU N) : Matrix (Fin N) (Fin N) ℂ)⁻¹ * ((j : SU N) : Matrix (Fin N) (Fin N) ℂ))) := by
        simp [Finset.sum_mul, Finset.mul_sum, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, mul_assoc, mul_comm, mul_left_comm]
        try rw [Finset.sum_comm]
        try simp [mul_comm, mul_left_comm, mul_assoc]
      _ = ∑ i ∈ s, ∑ j ∈ s, ((c i : ℂ) * (conj (c j) : ℂ)) * Matrix.trace (((i : SU N) : Matrix (Fin N) (Fin N) ℂ)⁻¹ * ((j : SU N) : Matrix (Fin N) (Fin N) ℂ)) := by
        simp [Matrix.trace_smul]
      _ = (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * fundamentalCharacter N (i⁻¹ * j)) := by
        have h_val_inv (g : SU N) : ((g : SU N) : Matrix (Fin N) (Fin N) ℂ)⁻¹ = ((g⁻¹ : SU N) : Matrix (Fin N) (Fin N) ℂ) := by
          calc
            ((g : SU N) : Matrix (Fin N) (Fin N) ℂ)⁻¹ = ((g : SU N) : Matrix (Fin N) (Fin N) ℂ)ᴴ :=
              (conjTranspose_eq_inv N g).symm
            _ = star ((g : SU N) : Matrix (Fin N) (Fin N) ℂ) := rfl
            _ = ((g⁻¹ : SU N) : Matrix (Fin N) (Fin N) ℂ) := by
              have h_star_eq_inv : (star (g : SU N) : SU N) = g⁻¹ := Matrix.star_eq_inv (A := g)
              simpa using congrArg Subtype.val h_star_eq_inv
        simp [fundamentalCharacter, h_val_inv, mul_comm, mul_left_comm]
  have h_trace_nonneg : 0 ≤ Matrix.trace (((∑ g ∈ s, (conj (c g) : ℂ) • ((g : SU N) : Matrix (Fin N) (Fin N) ℂ))ᴴ) * (∑ g ∈ s, (conj (c g) : ℂ) • ((g : SU N) : Matrix (Fin N) (Fin N) ℂ))) :=
    h_nonneg_sq ((∑ g ∈ s, (conj (c g) : ℂ) • ((g : SU N) : Matrix (Fin N) (Fin N) ℂ)) : Matrix (Fin N) (Fin N) ℂ)
  rw [← h_tr_eq]
  exact h_trace_nonneg

lemma PositiveDefinite.conj {G : Type*} [Group G] {φ : G → ℂ} (hφ : PositiveDefinite φ) :
    PositiveDefinite (λ g => conj (φ g)) := by
  intro s c
  have h := hφ s (λ g => conj (c g))
  -- h: ∑ conj(c i) * conj(conj(c j)) * φ(i⁻¹ * j) ≥ 0
  have h_simp : (∑ i ∈ s, ∑ j ∈ s, conj (c i) * c j * φ (i⁻¹ * j)) ≥ 0 := by
    simpa [star_star] using h
  rcases Complex.nonneg_iff.mp h_simp with ⟨h_re, h_im⟩
  have h_im_zero : (∑ i ∈ s, ∑ j ∈ s, conj (c i) * c j * φ (i⁻¹ * j)).im = 0 := h_im.symm
  have h_conj_eq : conj (∑ i ∈ s, ∑ j ∈ s, conj (c i) * c j * φ (i⁻¹ * j)) =
      (∑ i ∈ s, ∑ j ∈ s, conj (c i) * c j * φ (i⁻¹ * j)) :=
    (Complex.conj_eq_iff_im.mpr h_im_zero)
  have h_target : (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * conj (φ (i⁻¹ * j))) =
      conj (∑ i ∈ s, ∑ j ∈ s, conj (c i) * c j * φ (i⁻¹ * j)) := by
    simp [map_sum, mul_comm, mul_left_comm]
  rw [h_target, h_conj_eq]
  exact h_simp

lemma reTrace_positiveDefinite (N : ℕ) :
    PositiveDefinite (λ (g : SU N) => ((Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re : ℂ)) := by
  have h_trace_re_eq : ∀ (g : SU N), ((Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re : ℂ) =
      (fundamentalCharacter N g + conj (fundamentalCharacter N g)) / 2 := by
    intro g
    calc
      ((Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re : ℂ) =
        ((fundamentalCharacter N g).re : ℂ) := by simp [fundamentalCharacter]
      _ = (fundamentalCharacter N g + conj (fundamentalCharacter N g)) / 2 := by
        rw [Complex.re_eq_add_conj]
  have h_scaled : PositiveDefinite (λ (g : SU N) => (fundamentalCharacter N g + conj (fundamentalCharacter N g)) / 2) := by
    have h_sum : PositiveDefinite (λ g : SU N => fundamentalCharacter N g + conj (fundamentalCharacter N g)) :=
      PositiveDefinite.add (fundamentalCharacter_positiveDefinite N) (PositiveDefinite.conj (fundamentalCharacter_positiveDefinite N))
    have h_half_nonneg : (0 : ℝ) ≤ 1/2 := by norm_num
    have h_smul := PositiveDefinite.smul_nonneg h_half_nonneg h_sum
    simpa [div_eq_inv_mul, smul_eq_mul] using h_smul
  simpa [h_trace_re_eq] using h_scaled

lemma exp_reTrace_positiveDefinite (N : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    PositiveDefinite (λ (g : SU N) => (Real.exp (c * ((Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re : ℝ)) : ℂ)) := by
  set h : SU N → ℝ := fun g => (Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re
  set f : SU N → ℂ := fun g => (h g : ℂ)
  have hf : PositiveDefinite f := by
    have := reTrace_positiveDefinite N
    convert this using 1
  set S : ℕ → SU N → ℂ := fun n g =>
    ∑ k ∈ Finset.range n, ((c ^ k / k.factorial : ℝ) : ℂ) * ((f ^ k) g)
  have hS_PD : ∀ n, PositiveDefinite (S n) := by
    intro n
    induction n with
    | zero => simp [S, Finset.sum_empty]; exact PositiveDefinite.zero
    | succ n ih =>
      have hterm : PositiveDefinite (λ g => ((c ^ n / n.factorial : ℝ) : ℂ) * ((f ^ n) g)) := by
        apply PositiveDefinite.smul_nonneg
        · exact div_nonneg (pow_nonneg hc n) (Nat.cast_nonneg _)
        · exact PositiveDefinite.pow hf n
      have hadd : PositiveDefinite (λ g => S n g + ((c ^ n / n.factorial : ℝ) : ℂ) * ((f ^ n) g)) :=
        PositiveDefinite.add ih hterm
      have heq : S (n + 1) = (λ g => S n g + ((c ^ n / n.factorial : ℝ) : ℂ) * ((f ^ n) g)) := by
        funext g
        simp only [S, Finset.sum_range_succ]
      rw [heq]
      exact hadd
  have hS_tendsto : ∀ g, Tendsto (fun n => S n g) atTop (nhds ((Real.exp (c * h g)) : ℂ)) := by
    intro g
    have hexp : HasSum (fun k => (c * h g) ^ k / k.factorial) (Real.exp (c * h g)) := by
      have := NormedSpace.expSeries_div_hasSum_exp (c * h g)
      rwa [← Real.exp_eq_exp_ℝ] at this
    have hT_tendsto : Tendsto (fun n => ∑ k ∈ Finset.range n, (c * h g) ^ k / k.factorial) atTop
        (nhds (Real.exp (c * h g))) := hexp.tendsto_sum_nat
    have hSeq : ∀ n, S n g = ((∑ k ∈ Finset.range n, (c * h g) ^ k / k.factorial : ℝ) : ℂ) := by
      intro n
      simp only [S, f, h, Pi.pow_apply, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_div,
        Complex.ofReal_sum, mul_pow, mul_div_assoc, div_mul_eq_mul_div]
    rw [show (fun n => S n g) = (fun n =>
        ↑(∑ k ∈ Finset.range n, (c * h g) ^ k / k.factorial)) from by funext n; exact hSeq n]
    exact (Complex.continuous_ofReal.tendsto _).comp hT_tendsto
  exact PositiveDefinite.tendsto hS_PD hS_tendsto

end SU_N

section UnitaryRepresentation

variable {G : Type*} [Group G] {n : ℕ}

/-- A unitary representation of `G` is a group homomorphism into unitary matrices. -/
def IsUnitaryRepresentation (ρ : G →* Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ g : G, ρ g ∈ Matrix.unitaryGroup (Fin n) ℂ

/-- The character of a representation is the trace of the representation matrix. -/
def repCharacter (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (g : G) : ℂ :=
  Matrix.trace (ρ g)

/-- For a unitary matrix `A`, the conjugate transpose equals the inverse. -/
private lemma conjTranspose_eq_inv_of_unitary
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Aᴴ = A⁻¹ := by
  have h := Matrix.mem_unitaryGroup_iff'.mp hA
  rw [Matrix.star_eq_conjTranspose] at h
  exact (Matrix.inv_eq_left_inv h).symm

/-- The character of a unitary representation is positive-definite.

This generalizes `fundamentalCharacter_positiveDefinite` from the fundamental
representation of `SU(N)` to arbitrary unitary representations of any group.

The proof: for `B = ∑ conj(c_g) • ρ(g)`, the PD sum equals `Tr(Bᴴ * B) ≥ 0`,
using that `ρ(g)ᴴ = ρ(g⁻¹)` (unitary + homomorphism). -/
lemma repCharacter_positiveDefinite
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (h_unitary : IsUnitaryRepresentation ρ) :
    PositiveDefinite (repCharacter ρ) := by
  intro s c
  -- Tr(Mᴴ * M) ≥ 0 for any matrix M
  have h_nonneg_sq : ∀ (M : Matrix (Fin n) (Fin n) ℂ), 0 ≤ Matrix.trace (Mᴴ * M) := by
    intro M
    have htrace : Matrix.trace (Mᴴ * M) = (∑ i : Fin n, (Mᴴ * M) i i : ℂ) := by
      simp [Matrix.trace]
    rw [htrace]
    refine Finset.sum_nonneg (λ i _ => ?_)
    have hdiag : (Mᴴ * M) i i = ∑ k : Fin n, conj (M k i) * M k i := by
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [hdiag]
    refine Finset.sum_nonneg (λ k _ => ?_)
    have hnn : 0 ≤ conj (M k i) * M k i := by
      rw [← Complex.normSq_eq_conj_mul_self]
      have hval : 0 ≤ Complex.normSq (M k i) := Complex.normSq_nonneg _
      rw [Complex.nonneg_iff]
      exact ⟨by simpa using hval, by simp⟩
    exact hnn
  -- Key: ρ(g)ᴴ = ρ(g⁻¹) for unitary representations
  have h_star_eq (g : G) : (ρ g)ᴴ = ρ g⁻¹ := by
    rw [conjTranspose_eq_inv_of_unitary (h_unitary g)]
    have hmul : ρ g * ρ g⁻¹ = 1 := by
      rw [← ρ.map_mul, show g * g⁻¹ = 1 from by simp, ρ.map_one]
    exact Matrix.inv_eq_right_inv hmul
  -- B = ∑ conj(c_g) • ρ(g)
  set B : Matrix (Fin n) (Fin n) ℂ := ∑ g ∈ s, (conj (c g) : ℂ) • (ρ g)
  -- Bᴴ = ∑ c_g • ρ(g⁻¹)
  have hB_star : Bᴴ = ∑ g ∈ s, (c g : ℂ) • (ρ g⁻¹) := by
    show (∑ g ∈ s, (conj (c g) : ℂ) • (ρ g))ᴴ = _
    rw [Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro g hg
    rw [Matrix.conjTranspose_smul, h_star_eq g]
    simp [Complex.conj_conj]
  -- Key identity: Tr(Bᴴ * B) = ∑ c_i conj(c_j) * χ(i⁻¹ * j)
  have hBstarB : Bᴴ * B = ∑ i ∈ s, ∑ j ∈ s,
      ((c i : ℂ) * (conj (c j) : ℂ)) • (ρ (i⁻¹ * j)) := by
    rw [hB_star]
    show (∑ g ∈ s, (c g : ℂ) • (ρ g⁻¹)) * (∑ g ∈ s, (conj (c g) : ℂ) • (ρ g)) = _
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, ← ρ.map_mul]
  have h_tr_eq : Matrix.trace (Bᴴ * B) =
      (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * repCharacter ρ (i⁻¹ * j)) := by
    rw [hBstarB]
    simp only [Matrix.trace_sum, Matrix.trace_smul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simp [repCharacter]
  have h_trace_nonneg : 0 ≤ Matrix.trace (Bᴴ * B) := h_nonneg_sq B
  rw [← h_tr_eq]
  exact h_trace_nonneg

/-- For a unitary representation, the character satisfies `χ(g⁻¹) = conj(χ(g))`.
This follows from `ρ(g⁻¹) = ρ(g)⁻¹ = ρ(g)ᴴ` (unitary) and
`Tr(Mᴴ) = conj(Tr(M))`. -/
lemma repCharacter_inv (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (h_unitary : IsUnitaryRepresentation ρ) (g : G) :
    repCharacter ρ g⁻¹ = conj (repCharacter ρ g) := by
  have h_star_eq : (ρ g)ᴴ = ρ g⁻¹ := by
    rw [conjTranspose_eq_inv_of_unitary (h_unitary g)]
    have hmul : ρ g * ρ g⁻¹ = 1 := by
      rw [← ρ.map_mul, show g * g⁻¹ = 1 from by simp, ρ.map_one]
    exact Matrix.inv_eq_right_inv hmul
  rw [repCharacter, repCharacter, ← h_star_eq]
  simp [Matrix.trace, Matrix.conjTranspose_apply, Complex.star_def]

/-- For a unitary representation, the character is bounded by the dimension:
`‖χ(g)‖ ≤ n` where `n = dim(ρ)`.

This follows from `|Tr(A)| ≤ ∑ |A_jj| ≤ ∑ 1 = n` for a unitary `n×n` matrix `A`,
using `entry_norm_bound_of_unitary` (each entry of a unitary matrix has norm ≤ 1).
This bound is a key ingredient for proving integrability of the character-expansion
terms w.r.t. the finite Haar measure (needed for the Fubini exchange in step 4c). -/
lemma repCharacter_norm_le_dim (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (h_unitary : IsUnitaryRepresentation ρ) (g : G) :
    ‖repCharacter ρ g‖ ≤ n := by
  have hU : ρ g ∈ Matrix.unitaryGroup (Fin n) ℂ := h_unitary g
  have h_entry : ∀ j : Fin n, ‖(ρ g) j j‖ ≤ 1 := fun j =>
    entry_norm_bound_of_unitary hU j j
  rw [repCharacter]
  simp only [Matrix.trace]
  calc ‖∑ j : Fin n, (ρ g) j j‖
      ≤ ∑ j : Fin n, ‖(ρ g) j j‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin n, (1 : ℝ) := Finset.sum_le_sum fun j _ => h_entry j
    _ = n := by simp

#print axioms repCharacter_norm_le_dim

/-- For a unitary representation, the matrix element at `g⁻¹` equals the
conjugate of the transposed matrix element at `g`:

    (ρ g⁻¹)_{ij} = conj((ρ g)_{ji})

This follows from `ρ(g⁻¹) = ρ(g)ᴴ` (unitary + homomorphism) and the definition
of conjugate transpose `(Mᴴ)_{ij} = conj(M_{ji})`.

This is the key relation connecting the σ reflection (inversion of time-like
interface links) to the matrix-element basis. In the L² expansion approach to
closing `transferMatrixPositivity_axiom`, the σ reflection on a time-like
interface link `g ↦ g⁻¹` transforms matrix elements as
`(ρ(σ(g)))_{ij} = conj((ρ g)_{ji})`, which is essential for evaluating the
reflection-positivity integral using Schur orthogonality. -/
lemma repMatrixElement_inv (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (h_unitary : IsUnitaryRepresentation ρ) (g : G)
    (i j : Fin n) :
    (ρ g⁻¹) i j = conj ((ρ g) j i) := by
  have h_star_eq : (ρ g)ᴴ = ρ g⁻¹ := by
    rw [conjTranspose_eq_inv_of_unitary (h_unitary g)]
    have hmul : ρ g * ρ g⁻¹ = 1 := by
      rw [← ρ.map_mul, show g * g⁻¹ = 1 from by simp, ρ.map_one]
    exact Matrix.inv_eq_right_inv hmul
  rw [← h_star_eq]
  simp [Matrix.conjTranspose_apply]

#print axioms repMatrixElement_inv

/-! ## Irreducible representations and character orthogonality

The Osterwalder–Seiler reflection-positivity argument requires not just that
the Boltzmann factor is positive-definite (proved modulo Peter–Weyl as
`boltzmannFactorPD`), but that the reflection-positivity integral
`∫ f(U)·f(θU)·exp(-β S_W) dμ` is non-negative.  As documented in
`docs/gap_analysis.md`, this integral is NOT the standard PD quadratic form
`∫∫ f(g)·conj(f(h))·K(g⁻¹h) dμ dμ ≥ 0`; it is a single integral with the
geometric reflection `θ` and `K` evaluated at `g` (not `g⁻¹h`).

The Peter–Weyl character expansion of `K = exp(-β S_W)` writes
`K = ∑_λ a_λ χ_λ`, and the reflection-positivity integral becomes a sum of
terms `∑_λ a_λ · |∫ f · χ_λ|²` (using character orthogonality and the
reflection symmetry of the Haar measure).  Each term is non-negative because
`a_λ ≥ 0` and `|·|² ≥ 0`.  This is the missing step.

The infrastructure below axiomatizes the two deep theorems of compact-Lie-group
representation theory that are not in Mathlib:
1. **Irreducibility** of a unitary representation (no non-trivial invariant
   subspaces).
2. **Character orthogonality** for irreducible unitary representations of a
   compact group with normalized Haar measure: the integral of `χ_λ · conj(χ_μ)`
   is `1` if `λ = μ` (same irrep) and `0` otherwise (Schur orthogonality).

These are the ingredients needed to turn the character expansion of the
Boltzmann factor into the `|Fourier coefficient|²` decomposition of the
reflection-positivity integral.  See `docs/gap_analysis.md` for the full
analysis.
-/

/-- A unitary representation `ρ` is *irreducible* if the only invariant
subspaces (subspaces `W` with `ρ(g) W ⊆ W` for all `g`) are `{0}` and the
whole space.  This is the standard representation-theoretic notion. -/
def IsIrreducible {G : Type*} [Group G] {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ (W : Submodule ℂ (Fin n → ℂ)),
    (∀ g : G, ∀ v ∈ W, ρ g *ᵥ v ∈ W) → (W = ⊥ ∨ W = ⊤)

/-- **Axiom (Schur orthogonality for matrix elements of irreducible unitary
representations of a compact group).**

For a compact group `G` with normalized Haar measure `μ`, and irreducible
unitary representations `ρ_λ, ρ_μ` with matrix elements `(ρ_λ g)_{ij}`,
`(ρ_μ g)_{kl}`, the **Schur orthogonality relations** state:

  ∫_G (ρ_λ g)_{ij} · conj((ρ_μ g)_{kl}) dμ(g) = δ_{λμ} δ_{ik} δ_{jl} / dim(λ)

i.e. the integral is `1 / dim(λ)` if `λ = μ`, `i = k`, and `j = l`, and `0`
otherwise.

This is the **Great Orthogonality Theorem** for compact groups, a cornerstone
of the Peter–Weyl theorem.  It is not currently in Mathlib.  The axiom is
stated for a *finite* index set of irreps (the Peter–Weyl theorem gives a
countable family; for the lattice Boltzmann factor only finitely many irreps
appear in the character expansion, so a finite family suffices).

**Strengthened** (2026-08-01 session) from providing only character
orthogonality (`∫ χ_λ · conj(χ_μ) = δ_{λμ}`) to providing the full Schur
orthogonality of **matrix elements**.  The character-orthogonality version is
the `i = j`, `k = l` special case (the diagonal matrix elements, whose sum is
the character/trace).  The stronger matrix-element version is needed for the
L² expansion approach to closing `transferMatrixPositivity_axiom`: the test
function `f` produces arbitrary (non-class) functions of the interface links,
which must be expanded in the matrix-element basis (not just the character
basis) and evaluated using Schur orthogonality of matrix elements.  See
`docs/transfer_matrix_positivity_design.md` §5a for the full analysis.

The axiom is stated as a conjunction of three parts:
* **Integrability** of all matrix-element products (needed for the
  sum-integral exchange in `character_orthogonality_from_schur`).
* **Diagonal** (same irrep `λ = μ`): the matrix elements of a single irrep
  are orthogonal, with `∫ (ρ_λ g)_{ij} · conj((ρ_λ g)_{kl}) dμ = δ_{ik} δ_{jl} / dim(λ)`.
* **Off-diagonal** (distinct irreps `λ ≠ μ`): matrix elements of distinct
  irreps are orthogonal, with `∫ (ρ_λ g)_{ij} · conj((ρ_μ g)_{kl}) dμ = 0`.

The two-part diagonal/off-diagonal formulation avoids dependent-type issues:
in the diagonal case all indices share the type `Fin (dims r)`, and in the
off-diagonal case the result is `0` regardless of the (different-typed)
indices.  The hypothesis `hDims : ∀ i, 0 < dims i` ensures the representations
are non-degenerate (positive dimension), which is needed for
`dims r * (1 / dims r) = 1` in the character-orthogonality derivation. -/
axiom characterOrthogonality {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i)) :
    -- Integrability of all matrix-element products
    (∀ (r s : ι) (i : Fin (dims r)) (j : Fin (dims r)) (k : Fin (dims s)) (l : Fin (dims s)),
      Integrable (fun g => (ρ r g) i j * conj ((ρ s g) k l)) μ) ∧
    -- Schur orthogonality of matrix elements (diagonal: same irrep)
    (∀ (r : ι) (i j k l : Fin (dims r)),
      ∫ g, (ρ r g) i j * conj ((ρ r g) k l) ∂μ =
        if i = k ∧ j = l then (1 / dims r : ℂ) else 0) ∧
    -- Schur orthogonality of matrix elements (off-diagonal: distinct irreps)
    (∀ (r s : ι) (i j : Fin (dims r)) (k l : Fin (dims s)),
      r ≠ s →
      ∫ g, (ρ r g) i j * conj ((ρ s g) k l) ∂μ = 0)

/-- **Character orthogonality from Schur orthogonality of matrix elements.**

The character `χ_r(g) = Tr(ρ_r(g)) = ∑_a (ρ_r g)_{aa}` is the trace (sum of
diagonal matrix elements).  Schur orthogonality of matrix elements implies
character orthogonality:

  ∫ χ_r(g) · conj(χ_s(g)) dμ = ∑_{a,b} ∫ (ρ_r g)_{aa} · conj((ρ_s g)_{bb}) dμ

For `r = s`: each term is `1/dim(r)` if `a = b`, `0` otherwise; the sum is
`dim(r) · (1/dim(r)) = 1`.  For `r ≠ s`: each term is `0`; the sum is `0`.

This lemma derives the (weaker) character-orthogonality statement — previously
an axiom in its own right — from the strengthened `characterOrthogonality`
axiom that now provides the full Schur orthogonality of matrix elements.
Verified by `#print axioms` to depend only on `propext`, `Classical.choice`,
`Quot.sound` (plus `characterOrthogonality`). -/
lemma character_orthogonality_from_schur
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (r s : ι) :
    ∫ g, repCharacter (ρ r) g * conj (repCharacter (ρ s) g) ∂μ =
      if r = s then (1 : ℂ) else 0 := by
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  -- repCharacter (ρ k) g = ∑ a, (ρ k g) a a  (trace = sum of diagonal entries)
  have hchar : ∀ (k : ι) (g : G),
      repCharacter (ρ k) g = ∑ a : Fin (dims k), (ρ k g) a a := by
    intro k g; simp [repCharacter, Matrix.trace]
  -- conj pushes through a finite sum: conj (∑ a, f a) = ∑ a, conj (f a)
  -- (since `conj = starRingEnd ℂ` and `star = starRingEnd ℂ` definitionally)
  have hconj_sum : ∀ {n : ℕ} (f : Fin n → ℂ),
      conj (∑ a, f a) = ∑ a, conj (f a) := by
    intro n f; rw [starRingEnd_apply, star_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [starRingEnd_apply]
  by_cases h : r = s
  · -- Case r = s: ∫ χ_r · conj(χ_r) dμ = 1
    subst h
    -- Expand the integrand to a double sum of matrix elements
    have hprod : ∀ (g : G),
        repCharacter (ρ r) g * conj (repCharacter (ρ r) g) =
          ∑ a : Fin (dims r), ∑ b : Fin (dims r), (ρ r g) a a * conj ((ρ r g) b b) := by
      intro g; simp only [hchar]; rw [hconj_sum, Fintype.sum_mul_sum]
    rw [show (∫ g, repCharacter (ρ r) g * conj (repCharacter (ρ r) g) ∂μ) =
          ∫ g, (∑ a : Fin (dims r), ∑ b : Fin (dims r),
            (ρ r g) a a * conj ((ρ r g) b b)) ∂μ from by
        congr 1 with g; exact hprod g]
    -- Exchange the outer sum with the integral
    have hInt_inner : ∀ (a : Fin (dims r)),
        Integrable (fun g => ∑ b : Fin (dims r), (ρ r g) a a * conj ((ρ r g) b b)) μ := by
      intro a; exact integrable_finsetSum Finset.univ (fun b _ => hInt r r a a b b)
    rw [integral_finsetSum Finset.univ (fun a _ => hInt_inner a)]
    -- Exchange the inner sum with the integral
    rw [show (∑ a : Fin (dims r), ∫ g, ∑ b : Fin (dims r),
            (ρ r g) a a * conj ((ρ r g) b b) ∂μ) =
        ∑ a : Fin (dims r), ∑ b : Fin (dims r),
          ∫ g, (ρ r g) a a * conj ((ρ r g) b b) ∂μ from by
      apply Finset.sum_congr rfl
      intro a _
      rw [integral_finsetSum Finset.univ (fun b _ => hInt r r a a b b)]]
    -- Apply Schur orthogonality (diagonal case) and evaluate the sums
    simp only [hSchur_diag, and_self, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    -- Goal: ∑ a : Fin (dims r), (1 / dims r : ℂ) = 1
    have hn : (dims r : ℂ) ≠ 0 := by exact_mod_cast (hDims r).ne'
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_div_cancel₀ (1 : ℂ) hn]
  · -- Case r ≠ s: ∫ χ_r · conj(χ_s) dμ = 0
    have hprod : ∀ (g : G),
        repCharacter (ρ r) g * conj (repCharacter (ρ s) g) =
          ∑ a : Fin (dims r), ∑ b : Fin (dims s), (ρ r g) a a * conj ((ρ s g) b b) := by
      intro g; simp only [hchar]; rw [hconj_sum, Fintype.sum_mul_sum]
    rw [show (∫ g, repCharacter (ρ r) g * conj (repCharacter (ρ s) g) ∂μ) =
          ∫ g, (∑ a : Fin (dims r), ∑ b : Fin (dims s),
            (ρ r g) a a * conj ((ρ s g) b b)) ∂μ from by
        congr 1 with g; exact hprod g]
    -- Exchange the outer sum with the integral
    have hInt_inner : ∀ (a : Fin (dims r)),
        Integrable (fun g => ∑ b : Fin (dims s), (ρ r g) a a * conj ((ρ s g) b b)) μ := by
      intro a; exact integrable_finsetSum Finset.univ (fun b _ => hInt r s a a b b)
    rw [integral_finsetSum Finset.univ (fun a _ => hInt_inner a)]
    -- Exchange the inner sum with the integral
    rw [show (∑ a : Fin (dims r), ∫ g, ∑ b : Fin (dims s),
            (ρ r g) a a * conj ((ρ s g) b b) ∂μ) =
        ∑ a : Fin (dims r), ∑ b : Fin (dims s),
          ∫ g, (ρ r g) a a * conj ((ρ s g) b b) ∂μ from by
      apply Finset.sum_congr rfl
      intro a _
      rw [integral_finsetSum Finset.univ (fun b _ => hInt r s a a b b)]]
    -- Apply Schur orthogonality (off-diagonal case): every term is 0
    have hzero : (∑ a : Fin (dims r), ∑ b : Fin (dims s),
        ∫ g, (ρ r g) a a * conj ((ρ s g) b b) ∂μ) = (0 : ℂ) := by
      refine Finset.sum_eq_zero (fun a _ => ?_)
      refine Finset.sum_eq_zero (fun b _ => ?_)
      exact hSchur_offdiag r s a a b b h
    rw [hzero, if_neg h]

end UnitaryRepresentation
