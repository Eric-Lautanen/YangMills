import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Finsupp.Basic

/-!
# General L² integral-operator positivity for positive-definite kernels

This file proves a **general** version of `integralOperator_nonneg` that removes
the compactness and continuity hypotheses of the compact/continuous version
(`PositiveDefiniteKernelMathlibCandidate.lean`).

**Main theorem.** For a finite measure space `(X, μ)`, a pointwise positive-definite
kernel `K` with bounded diagonal (`K(x,x) ≤ M`), and a strongly measurable feature
map, and `f ∈ L²(μ)`, the integral `∫∫ f(x) * conj(f(y)) * K(x,y) dμ dμ ≥ 0`.

The proof uses the Moore–Aronszajn feature map `φ : X → H` into the RKHS `H`,
defines `F = ∫ conj(f) • φ dμ` as a Bochner integral in `H`, and shows
`∫∫ f(x) * conj(f(y)) * K(x,y) dμ dμ = ⟨F, F⟩_H = ‖F‖² ≥ 0`.

No topology on `X`, no continuity of `K` or `f`, no compactness.
-/

open Finsupp MeasureTheory Complex Matrix

open scoped ComplexConjugate ComplexOrder

/-! ## PositiveDefiniteKernel definition and key lemmas (copied from the
priority candidate file for self-containment). -/

/-- A kernel `K : X → X → ℂ` is positive-definite (Mercer sense): every finite
submatrix `(K x_i x_j)_{i,j ∈ s}` is positive-semidefinite. -/
def PositiveDefiniteKernel {X : Type*} (K : X → X → ℂ) : Prop :=
  ∀ (s : Finset X), Matrix.PosSemidef (Matrix.of fun (i j : ↥s) => K i.val j.val)

/-- The quadratic form `Σ c_i * conj(c_j) * K(x_i, x_j) ≥ 0`. -/
lemma PositiveDefiniteKernel.quadratic_form_nonneg
    {X : Type*} {K : X → X → ℂ} (hK : PositiveDefiniteKernel K)
    (s : Finset X) (c : X → ℂ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * K i j := by
  classical
  haveI : DecidableEq ↥s := Classical.decEq _
  let M : Matrix ↥s ↥s ℂ := fun i j => K i.val j.val
  have hM : M.PosSemidef := hK s
  let x : ↥s → ℂ := fun i => conj (c i.val)
  have hquad : 0 ≤ star x ⬝ᵥ (M *ᵥ x) :=
    Matrix.PosSemidef.dotProduct_mulVec_nonneg hM x
  have hdot : star x ⬝ᵥ (M *ᵥ x) =
      ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * K i j := by
    rw [Matrix.dot_mulVec_eq_sum_sum, Finset.sum_comm]
    simp only [M, x, Pi.star_apply, Complex.star_def, Complex.conj_conj]
    rw [Finset.sum_coe_sort s
        (fun a => ∑ j : ↥s, c a * K a j.val * conj (c j.val))]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_coe_sort s (fun b => c i * K i b * conj (c b))]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_right_comm _ _ _
  rw [← hdot]; exact hquad

private lemma quadratic_form_conj_symm
    {X : Type*} (K : X → X → ℂ)
    (h : ∀ (s : Finset X) (c : X → ℂ),
      0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * K i j) :
    ∀ x y, K x y = conj (K y x) := by
  intro x y
  classical
  have h_diag : ∀ z, 0 ≤ K z z := fun z => by
    have h' := h (Finset.cons z ∅ (by simp)) (fun _ => 1)
    simp at h'; exact h'
  have h_diag_im : ∀ z, (K z z).im = 0 := fun z =>
    (Complex.nonneg_iff.mp (h_diag z)).2.symm
  by_cases hxy : x = y
  · subst hxy; exact (Complex.conj_eq_iff_im.mpr (h_diag_im x)).symm
  · have hne1' : (y : X) ∉ (∅ : Finset X) := by simp
    have hne2 : (x : X) ∉ Finset.cons y ∅ hne1' := by simp [hxy]
    have hS : ∀ t : ℂ,
        0 ≤ K x x + conj t * K x y + t * K y x + (t * conj t) * K y y := by
      intro t
      have h' := h (Finset.cons x (Finset.cons y ∅ hne1') hne2)
          (fun z => if z = x then 1 else t)
      have hsum : (∑ i ∈ Finset.cons x (Finset.cons y ∅ hne1') hne2,
          ∑ j ∈ Finset.cons x (Finset.cons y ∅ hne1') hne2,
          (if i = x then 1 else t) * conj (if j = x then 1 else t) * K i j) =
          K x x + conj t * K x y + t * K y x + (t * conj t) * K y y := by
        simp only [Finset.sum_cons, Finset.sum_empty,
          ite_true, if_neg (Ne.symm hxy), one_mul, mul_one, map_one]
        ring
      rw [hsum] at h'; exact h'
    have h_im_sum : (K x y).im + (K y x).im = 0 := by
      have key := (Complex.nonneg_iff.mp (hS 1)).2
      have hkey : K x x + conj 1 * K x y + 1 * K y x + (1 * conj 1) * K y y =
          K x x + K x y + K y x + K y y := by simp
      rw [hkey] at key
      have h2 : (K x x + K x y + K y x + K y y).im =
          (K x x).im + (K x y).im + (K y x).im + (K y y).im := by simp [Complex.add_im]
      rw [h2, h_diag_im x, h_diag_im y] at key; linarith
    have h_re_diff : (K y x).re - (K x y).re = 0 := by
      have key := (Complex.nonneg_iff.mp (hS Complex.I)).2
      have heq : K x x + conj Complex.I * K x y + Complex.I * K y x +
          (Complex.I * conj Complex.I) * K y y =
          K x x + K y y + Complex.I * (K y x - K x y) := by simp [Complex.conj_I]; ring
      rw [heq] at key
      have h2 : (K x x + K y y + Complex.I * (K y x - K x y)).im =
          (K x x).im + (K y y).im + ((K y x).re - (K x y).re) := by
        simp [Complex.add_im, Complex.mul_im, Complex.sub_re, Complex.sub_im,
          Complex.I_re, Complex.I_im]
      rw [h2, h_diag_im x, h_diag_im y] at key; linarith
    apply Complex.ext
    · rw [Complex.conj_re]; linarith
    · rw [Complex.conj_im]; linarith

/-- A Mercer-PD kernel is Hermitian: `K(x, y) = conj(K(y, x))`. -/
lemma PositiveDefiniteKernel.conj_symm {X : Type*} {K : X → X → ℂ}
    (hK : PositiveDefiniteKernel K) : ∀ x y, K x y = conj (K y x) :=
  quadratic_form_conj_symm K hK.quadratic_form_nonneg

/-! ## RKHS construction from a PD kernel (scalar case) -/

namespace GeneralKernel

variable {X : Type*}

/-- Type alias so the inner-product instance can mention `K` (needed for
typeclass synthesis, following the `Reproducing.lean` pattern). -/
@[nolint unusedArguments]
abbrev H₀ (K : X → X → ℂ) := X →₀ ℂ

variable {K : X → X → ℂ} [Fact (PositiveDefiniteKernel K)]

noncomputable section

/-- Pre-inner product space structure on `H₀ K` (finitely supported functions)
with inner product `⟨f, g⟩ = Σ_{x,y} conj(f x) * g(y) * K(x,y)`. -/
instance kernelCore : PreInnerProductSpace.Core ℂ (H₀ K) where
  inner f g := f.sum fun x z => g.sum fun y w => conj z * w * K x y
  conj_inner_symm f g := by
    show conj (g.sum fun x z => f.sum fun y w => conj z * w * K x y) =
         f.sum fun x z => g.sum fun y w => conj z * w * K x y
    rw [Finsupp.sum_comm]
    simp only [map_finsuppSum, map_finsuppSum]
    apply Finsupp.sum_congr
    intro x _
    apply Finsupp.sum_congr
    intro y _
    show star (star (g y) * f x * K y x) = star (f x) * g y * K x y
    have hK : star (K y x) = K x y :=
      (Fact.out : PositiveDefiniteKernel K).conj_symm x y |>.symm
    simp only [star_mul', star_star, hK]
    ring
  re_inner_nonneg f := by
    have hkey := (Fact.out : PositiveDefiniteKernel K).quadratic_form_nonneg
      f.support (fun x => conj (f x))
    simp only [conj_conj] at hkey
    change 0 ≤ re (∑ x ∈ f.support, ∑ y ∈ f.support, conj (f x) * f y * K x y)
    exact (Complex.nonneg_iff.mp hkey).1
  add_left f g h := by
    show (f + g).sum (fun x z => h.sum (fun y w => conj z * w * K x y)) =
         f.sum (fun x z => h.sum (fun y w => conj z * w * K x y)) +
         g.sum (fun x z => h.sum (fun y w => conj z * w * K x y))
    rw [Finsupp.sum_add_index'] <;> simp [add_mul]
  smul_left r f g := by
    show (g • r).sum (fun x z => f.sum (fun y w => conj z * w * K x y)) =
      conj g * r.sum (fun x z => f.sum (fun y w => conj z * w * K x y))
    rw [Finsupp.sum_smul_index] <;> simp [Finsupp.mul_sum, ← mul_assoc]
instance : SeminormedAddCommGroup (H₀ K) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ)

instance : InnerProductSpace ℂ (H₀ K) :=
  InnerProductSpace.ofCore kernelCore

/-- The RKHS (Hilbert space) generated by the PD kernel `K`, defined as the
completion of the pre-inner product space `H₀ K`. -/
abbrev H (K : X → X → ℂ) [Fact (PositiveDefiniteKernel K)] :=
  UniformSpace.Completion (H₀ K)

instance : InnerProductSpace ℂ (H K) :=
  UniformSpace.Completion.innerProductSpace

/-- The feature map `φ : X → H` sending `x` to the kernel function at `x`
(the equivalence class of `Finsupp.single x 1` in the completion). -/
def featureMap (K : X → X → ℂ) [Fact (PositiveDefiniteKernel K)] (x : X) : H K :=
  (single x 1 : H₀ K)

/-- The inner product of two feature maps equals the kernel:
`⟨φ(x), φ(y)⟩_H = K(x, y)`. -/
lemma inner_featureMap (x y : X) :
    inner ℂ (featureMap K x) (featureMap K y) = K x y := by
  show inner ℂ ((single x 1 : H₀ K) : H K) ((single y 1 : H₀ K) : H K) = K x y
  rw [UniformSpace.Completion.inner_coe]
  change (single x 1 : H₀ K).sum (fun a z =>
    (single y 1 : H₀ K).sum (fun b w => conj z * w * K a b)) = K x y
  rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
  simp

/-- The squared norm of a feature map equals the (real part of the) diagonal:
`‖φ(x)‖²_H = (K(x, x)).re`. -/
lemma normSq_featureMap (x : X) :
    ‖featureMap K x‖^2 = (K x x).re := by
  have h := @inner_self_eq_norm_sq ℂ (H K) _ _ _ (featureMap K x)
  rw [inner_featureMap] at h
  exact h.symm

end

end GeneralKernel

open GeneralKernel

/-! ## Main theorem: general L² integralOperator_nonneg (bounded case) -/

/-- **A PD kernel with bounded diagonal on a finite measure space defines a
positive integral operator (general L² version).**

For a finite measure space `(X, μ)`, a pointwise PD kernel `K` with bounded
diagonal (`K(x,x) ≤ M`), with strongly measurable feature map, and `f ∈ L²(μ)`,
the integral `∫∫ f(x) * conj(f(y)) * K(x, y) dμ dμ ≥ 0`.

The proof uses the Moore–Aronszajn feature map `φ : X → H` into the RKHS `H`,
defines `F = ∫ conj(f) • φ dμ` as a Bochner integral in `H`, and shows
`∫∫ f(x) * conj(f(y)) * K(x,y) dμ dμ = ⟨F, F⟩_H = ‖F‖² ≥ 0`.

No topology on `X`, no continuity of `K` or `f`, no compactness. -/
lemma PositiveDefiniteKernel.integralOperator_nonneg_general
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {K : X → X → ℂ} [Fact (PositiveDefiniteKernel K)]
    (hM : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, K x x ≤ M)
    (hφ_meas : StronglyMeasurable (featureMap K))
    {f : X → ℂ} (hf : MemLp f 2 μ) :
    0 ≤ ∫ x, ∫ y, f x * conj (f y) * K x y ∂μ ∂μ := by
  obtain ⟨M, hMnn, hM⟩ := hM
  -- Step 1: The feature map is bounded: ‖φ(x)‖ = √(K(x,x)) ≤ √M
  have hφ_norm : ∀ x, ‖featureMap K x‖ ≤ Real.sqrt M := by
    intro x
    have hsq := @normSq_featureMap X K _ x
    have hKxx_nn : 0 ≤ K x x := by
      have := (Fact.out : PositiveDefiniteKernel K).quadratic_form_nonneg
        (Finset.cons x ∅ (by simp)) (fun _ => (1 : ℂ))
      simp at this
      exact this
    have hKxx_re_nn : 0 ≤ (K x x).re := (Complex.nonneg_iff.mp hKxx_nn).1
    have hKxx_re_le : (K x x).re ≤ M := (Complex.le_def.mp (hM x)).1
    have h1 : ‖featureMap K x‖ = Real.sqrt (‖featureMap K x‖^2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    rw [h1, hsq]
    exact Real.sqrt_le_sqrt hKxx_re_le
  -- Step 2: f ∈ L²(μ) and μ finite ⟹ f ∈ L¹(μ)
  have hf_int : Integrable f μ := hf.integrable (by norm_num)
  -- Step 3: The integrand conj(f) • φ is strongly measurable
  have hφ_smul_meas : AEStronglyMeasurable
      (fun x => conj (f x) • featureMap K x) μ := by
    refine AEStronglyMeasurable.smul (𝕜 := ℂ) ?_ hφ_meas.aestronglyMeasurable
    exact Complex.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable
  -- Step 4: The integrand conj(f) • φ is integrable (by Integrable.mono')
  have hφ_smul_int : Integrable (fun x => conj (f x) • featureMap K x) μ := by
    apply Integrable.mono' (g := fun x => Real.sqrt M * ‖f x‖)
    · exact hf_int.norm.const_mul (Real.sqrt M)
    · exact hφ_smul_meas
    · filter_upwards with x
      rw [norm_smul, Complex.norm_conj, mul_comm (‖f x‖)]
      exact mul_le_mul_of_nonneg_right (hφ_norm x) (norm_nonneg _)
  -- Step 5: Define F = ∫ conj(f) • φ dμ (Bochner integral in H)
  set F := ∫ x, conj (f x) • featureMap K x ∂μ
  -- Step 6: inner ℂ (featureMap K x) F = ∫ y, conj(f y) * K x y ∂μ
  have hstep1 : ∀ x, inner ℂ (featureMap K x) F = ∫ y, conj (f y) * K x y ∂μ := by
    intro x
    rw [← integral_inner hφ_smul_int (featureMap K x)]
    apply integral_congr_ae
    filter_upwards with y
    rw [inner_smul_right, inner_featureMap]
  -- Step 7: inner ℂ F (conj(f x) • φ x) = ∫ y, conj(f x) * K y x * f y ∂μ
  have hstep2 : ∀ x, inner ℂ F (conj (f x) • featureMap K x) =
      ∫ y, conj (f x) * K y x * f y ∂μ := by
    intro x
    rw [inner_smul_right, ← inner_conj_symm, hstep1, ← integral_conj,
        ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    have hK : star (K x y) = K y x :=
      (Fact.out : PositiveDefiniteKernel K).conj_symm y x |>.symm
    show star (f x) * star (star (f y) * K x y) = star (f x) * K y x * f y
    rw [star_mul', star_star, hK]
    ring
  -- Step 8: inner ℂ F F = conj (∫∫ f x * conj(f y) * K x y ∂μ ∂μ)
  have hkey : inner ℂ F F =
      conj (∫ x, ∫ y, f x * conj (f y) * K x y ∂μ ∂μ) := by
    rw [← integral_inner hφ_smul_int F, ← integral_conj]
    apply integral_congr_ae
    filter_upwards with x
    rw [hstep2, ← integral_conj]
    apply integral_congr_ae
    filter_upwards with y
    have hK : star (K x y) = K y x :=
      (Fact.out : PositiveDefiniteKernel K).conj_symm y x |>.symm
    show star (f x) * K y x * f y = star (f x * star (f y) * K x y)
    rw [star_mul', star_mul', star_star, hK]
    ring
  -- Step 9: 0 ≤ inner ℂ F F = ‖F‖², and conj(goal) = goal
  have hconj : conj (inner ℂ F F) = inner ℂ F F := inner_conj_symm F F
  rw [hkey] at hconj
  simp only [Complex.conj_conj] at hconj
  have h_nonneg : 0 ≤ inner ℂ F F := by
    rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
    exact Complex.zero_le_real.mpr (sq_nonneg _)
  rw [hkey] at h_nonneg
  rw [← hconj] at h_nonneg
  exact h_nonneg

#print axioms PositiveDefiniteKernel.integralOperator_nonneg_general
