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
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import YangMills.SpecialUnitary
open Finset
open Complex
open Filter
open Matrix
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
