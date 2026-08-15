/-
# Positive Definite Integral: Character Expansion Positivity

Abstract measure-theory scaffold for character-orthogonality approach:
character_expansion_positivity, character_expansion_nonneg, and
the shared-variable variant character_expansion_nonneg_shared.
-/

import YangMills.Proofs.PositiveDefiniteIntegral.MercerKernel

open Finset MeasureTheory Complex Metric Matrix

open scoped ComplexConjugate ComplexOrder Function

namespace YangMills

variable {G : Type*} [Group G]
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


end YangMills
