/-
# Positive Definite: Step 3 Bridge Lemma
-/

import YangMills.Proofs.PositiveDefinite.LuscherCascade

open Finset
open Complex
open Filter
open Matrix
open MeasureTheory
open scoped ComplexConjugate
open scoped ComplexOrder

namespace YangMills
variable {G : Type*} [Group G] {n : Nat}

/-! ## Step 3 bridge lemma: plaquette product expansion → Lüscher cascade

The following lemma is the key bridge connecting the plaquette product expansion
(step 2: `∑_{s,t} F(s,t) · χ_s(·) · χ_t(·)` with `F(s,t) ≥ 0`) to the Lüscher
cascade (step 3: integrating out temporal links `g₀, g₁`).  It takes arbitrary
non-negative coefficients `F : ι → ι → ℝ` and evaluates the 2-site cascade:

    ∫∫ ∑_{s,t} F(s,t) · χ_s(g₀·W·g₁⁻¹) · χ_t(g₁·V·g₀⁻¹) dg₁ dg₀
      = ∑_s F(s,s) · (1/d_s) · χ_s(W·V)

The resulting kernel `K(W,V) = ∑_s (F(s,s) · (1/d_s)) · χ_s(W·V)` has non-negative
coefficients `F(s,s) · (1/d_s) ≥ 0` (since `F(s,s) ≥ 0` and `1/d_s > 0`), matching
`character_kernel_integral_nonneg` (step 4).

The proof follows the same pattern as `luscher_2site_2D_cascade_charlevel` but is
simpler: no Clebsch–Gordan decomposition is needed since the integrand is already
a sum of single-character products.  The key steps are:
(1) establish integrability of each character product w.r.t. `g₁` using
    `characterOrthogonality` (matrix-element integrability) and the unitary
    expansion `ρ(g₁⁻¹) = ρ(g₁)†`;
(2) exchange the finite sums with the inner `g₁` integral via `integral_finsetSum`;
(3) apply `luscher_key_identity` to each `(s,t)` term (Schur orthogonality forces
    `s = t`);
(4) integrate out `g₀` (the result is constant, so the integral equals the
    constant over a probability measure);
(5) collapse the `if t = s` to keep only the diagonal `t = s` terms.
See `docs/transfer_matrix_positivity_design.md` §8.11.47. -/

/-- **2-site Lüscher cascade with arbitrary non-negative coefficients (Step 3 bridge).**

For irreducible unitary representations of a compact group with normalized Haar
measure, and arbitrary non-negative coefficients `F : ι → ι → ℝ` with `F s t ≥ 0`,
the 2-site cascade with summed character products evaluates to:

    ∫∫ ∑_{s,t} F(s,t) · χ_s(g₀·W·g₁⁻¹) · χ_t(g₁·V·g₀⁻¹) dg₁ dg₀
      = ∑_s F(s,s) · (1/d_s) · χ_s(W·V)

The coefficient `F(s,s) · (1/d_s) ≥ 0` (since `F(s,s) ≥ 0` and `1/d_s > 0`),
so the resulting kernel matches `character_kernel_integral_nonneg`.  0 sorries,
0 new axioms. -/
lemma luscher_2site_cascade_coeff
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (F : ι → ι → ℝ) (hF : ∀ s t, 0 ≤ F s t)
    (W V : G) :
    ∫ g₀, ∫ g₁,
      ∑ s, ∑ t, (F s t : ℂ) *
        (repCharacter (ρ s) (g₀ * W * g₁⁻¹) * repCharacter (ρ t) (g₁ * V * g₀⁻¹)) ∂μ ∂μ =
    ∑ s, (F s s : ℂ) * ((1 / dims s : ℂ) * repCharacter (ρ s) (W * V)) := by
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  have htrace_mul : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ),
      Matrix.trace (A * B) = ∑ i : Fin n, ∑ j : Fin n, A i j * B j i := by
    intro n A B; simp [Matrix.trace, Matrix.mul_apply]
  -- Integrability of character product w.r.t. g₁ (for fixed g₀, s, t)
  have hInt_char : ∀ (g₀ : G) (s t : ι),
      Integrable (fun g₁ =>
        repCharacter (ρ s) (g₀ * W * g₁⁻¹) * repCharacter (ρ t) (g₁ * V * g₀⁻¹)) μ := by
    intro g₀ s t
    have hchar_s : ∀ (g₁ : G),
        repCharacter (ρ s) (g₀ * W * g₁⁻¹) =
        ∑ a : Fin (dims s), ∑ b : Fin (dims s),
          (ρ s (g₀ * W)) a b * conj ((ρ s g₁) a b) := by
      intro g₁
      rw [repCharacter, MonoidHom.map_mul, htrace_mul]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [repMatrixElement_inv (ρ s) (hU s) g₁ b a]
    have hchar_t : ∀ (g₁ : G),
        repCharacter (ρ t) (g₁ * V * g₀⁻¹) =
        ∑ c : Fin (dims t), ∑ d : Fin (dims t),
          (ρ t g₁) c d * (ρ t (V * g₀⁻¹)) d c := by
      intro g₁
      rw [show g₁ * V * g₀⁻¹ = g₁ * (V * g₀⁻¹) from mul_assoc _ _ _,
          repCharacter, MonoidHom.map_mul, htrace_mul]
    have hprod_expand : ∀ (g₁ : G),
        repCharacter (ρ s) (g₀ * W * g₁⁻¹) * repCharacter (ρ t) (g₁ * V * g₀⁻¹) =
        ∑ a : Fin (dims s), ∑ c : Fin (dims t),
          ∑ b : Fin (dims s), ∑ d : Fin (dims t),
            (ρ s (g₀ * W)) a b * (ρ t (V * g₀⁻¹)) d c *
            ((ρ t g₁) c d * conj ((ρ s g₁) a b)) := by
      intro g₁
      rw [hchar_s, hchar_t]
      simp only [Fintype.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro d _
      ring
    have hInt_term : ∀ (a : Fin (dims s)) (b : Fin (dims s))
        (c : Fin (dims t)) (d : Fin (dims t)),
        Integrable (fun g₁ =>
          (ρ s (g₀ * W)) a b * (ρ t (V * g₀⁻¹)) d c *
          ((ρ t g₁) c d * conj ((ρ s g₁) a b))) μ := by
      intro a b c d
      have h_gdep : Integrable (fun g₁ => (ρ t g₁) c d * conj ((ρ s g₁) a b)) μ :=
        hInt t s c d a b
      exact (h_gdep.smul ((ρ s (g₀ * W)) a b * (ρ t (V * g₀⁻¹)) d c)).congr
        (Filter.Eventually.of_forall (fun g₁ => by
          simp only [Pi.smul_def, smul_eq_mul]))
    have hInt_d : ∀ (a : Fin (dims s)) (c : Fin (dims t)) (b : Fin (dims s)),
        Integrable (fun g₁ => ∑ d : Fin (dims t),
          (ρ s (g₀ * W)) a b * (ρ t (V * g₀⁻¹)) d c *
          ((ρ t g₁) c d * conj ((ρ s g₁) a b))) μ :=
      fun a c b => integrable_finsetSum Finset.univ (fun d _ => hInt_term a b c d)
    have hInt_b : ∀ (a : Fin (dims s)) (c : Fin (dims t)),
        Integrable (fun g₁ => ∑ b : Fin (dims s), ∑ d : Fin (dims t),
          (ρ s (g₀ * W)) a b * (ρ t (V * g₀⁻¹)) d c *
          ((ρ t g₁) c d * conj ((ρ s g₁) a b))) μ :=
      fun a c => integrable_finsetSum Finset.univ (fun b _ => hInt_d a c b)
    have hInt_c : ∀ (a : Fin (dims s)),
        Integrable (fun g₁ => ∑ c : Fin (dims t), ∑ b : Fin (dims s), ∑ d : Fin (dims t),
          (ρ s (g₀ * W)) a b * (ρ t (V * g₀⁻¹)) d c *
          ((ρ t g₁) c d * conj ((ρ s g₁) a b))) μ :=
      fun a => integrable_finsetSum Finset.univ (fun c _ => hInt_b a c)
    have hInt_sum : Integrable (fun g₁ =>
        ∑ a : Fin (dims s), ∑ c : Fin (dims t),
          ∑ b : Fin (dims s), ∑ d : Fin (dims t),
            (ρ s (g₀ * W)) a b * (ρ t (V * g₀⁻¹)) d c *
            ((ρ t g₁) c d * conj ((ρ s g₁) a b))) μ :=
      integrable_finsetSum Finset.univ (fun a _ => hInt_c a)
    exact hInt_sum.congr (Filter.Eventually.of_forall (fun g₁ => (hprod_expand g₁).symm))
  -- Integrability of each (s, t) term w.r.t. g₁
  have hInt_term_st : ∀ (g₀ : G) (s t : ι),
      Integrable (fun g₁ =>
        (F s t : ℂ) *
        (repCharacter (ρ s) (g₀ * W * g₁⁻¹) * repCharacter (ρ t) (g₁ * V * g₀⁻¹))) μ := by
    intro g₀ s t
    exact ((hInt_char g₀ s t).smul (F s t : ℂ)).congr
      (Filter.Eventually.of_forall (fun g₁ => by
        simp only [Pi.smul_def, smul_eq_mul]))
  have hInt_t : ∀ (g₀ : G) (s : ι),
      Integrable (fun g₁ =>
        ∑ t : ι, (F s t : ℂ) *
        (repCharacter (ρ s) (g₀ * W * g₁⁻¹) * repCharacter (ρ t) (g₁ * V * g₀⁻¹))) μ :=
    fun g₀ s => integrable_finsetSum Finset.univ (fun t _ => hInt_term_st g₀ s t)
  -- Inner integral via luscher_key_identity
  have hInner : ∀ (g₀ : G) (s t : ι),
      ∫ g₁, repCharacter (ρ s) (g₀ * W * g₁⁻¹) * repCharacter (ρ t) (g₁ * V * g₀⁻¹) ∂μ =
      if t = s then (1 / dims t : ℂ) * repCharacter (ρ t) (V * W) else 0 := by
    intro g₀ s t
    rw [show (∫ g₁, repCharacter (ρ s) (g₀ * W * g₁⁻¹) *
          repCharacter (ρ t) (g₁ * V * g₀⁻¹) ∂μ) =
        ∫ g₁, repCharacter (ρ t) (g₁ * (V * g₀⁻¹)) *
          repCharacter (ρ s) (g₁⁻¹ * (g₀ * W)) ∂μ from by
      congr 1 with g₁
      rw [show repCharacter (ρ s) (g₀ * W * g₁⁻¹) = repCharacter (ρ s) (g₁⁻¹ * (g₀ * W)) from by
        rw [repCharacter_cyclic, repCharacter_cyclic, mul_assoc]]
      rw [show repCharacter (ρ t) (g₁ * V * g₀⁻¹) = repCharacter (ρ t) (g₁ * (V * g₀⁻¹)) from by
        rw [mul_assoc]]
      ring]
    rw [luscher_key_identity μ ι dims hDims ρ hU hIrr t s (V * g₀⁻¹) (g₀ * W)]
    by_cases h : t = s
    · rw [if_pos h, if_pos h]
      rw [show (V * g₀⁻¹) * (g₀ * W) = V * W from by
        have hinv : g₀⁻¹ * g₀ = 1 := inv_mul_cancel _
        calc (V * g₀⁻¹) * (g₀ * W) = V * (g₀⁻¹ * (g₀ * W)) := by rw [mul_assoc]
          _ = V * ((g₀⁻¹ * g₀) * W) := by rw [← mul_assoc g₀⁻¹ g₀ W]
          _ = V * (1 * W) := by rw [hinv]
          _ = V * W := by rw [one_mul]]
    · rw [if_neg h, if_neg h]
  -- Inner integral with constants pulled out
  have hInner_full : ∀ (g₀ : G) (s t : ι),
      ∫ g₁, (F s t : ℂ) *
        (repCharacter (ρ s) (g₀ * W * g₁⁻¹) * repCharacter (ρ t) (g₁ * V * g₀⁻¹)) ∂μ =
      (F s t : ℂ) *
        (if t = s then (1 / dims t : ℂ) * repCharacter (ρ t) (V * W) else 0) := by
    intro g₀ s t
    rw [integral_const_mul, hInner g₀ s t]
  -- Exchange s sum with g₁ integral
  rw [show (∫ g₀, ∫ g₁,
        (∑ s : ι, ∑ t : ι, (F s t : ℂ) *
          (repCharacter (ρ s) (g₀ * W * g₁⁻¹) * repCharacter (ρ t) (g₁ * V * g₀⁻¹))) ∂μ ∂μ) =
      ∫ g₀, ∑ s : ι, ∫ g₁,
        (∑ t : ι, (F s t : ℂ) *
          (repCharacter (ρ s) (g₀ * W * g₁⁻¹) * repCharacter (ρ t) (g₁ * V * g₀⁻¹))) ∂μ ∂μ from by
    congr 1 with g₀
    rw [integral_finsetSum Finset.univ (fun s _ => hInt_t g₀ s)]]
  -- Exchange t sum with g₁ integral
  rw [show (∫ g₀, ∑ s : ι, ∫ g₁,
        (∑ t : ι, (F s t : ℂ) *
          (repCharacter (ρ s) (g₀ * W * g₁⁻¹) * repCharacter (ρ t) (g₁ * V * g₀⁻¹))) ∂μ ∂μ) =
      ∫ g₀, ∑ s : ι, ∑ t : ι, ∫ g₁,
        ((F s t : ℂ) *
          (repCharacter (ρ s) (g₀ * W * g₁⁻¹) * repCharacter (ρ t) (g₁ * V * g₀⁻¹))) ∂μ ∂μ from by
    congr 1 with g₀
    apply Finset.sum_congr rfl
    intro s _
    rw [integral_finsetSum Finset.univ (fun t _ => hInt_term_st g₀ s t)]]
  -- Apply hInner_full to each inner integral
  rw [show (∫ g₀, ∑ s : ι, ∑ t : ι, ∫ g₁,
        ((F s t : ℂ) *
          (repCharacter (ρ s) (g₀ * W * g₁⁻¹) * repCharacter (ρ t) (g₁ * V * g₀⁻¹))) ∂μ ∂μ) =
      ∫ g₀, ∑ s : ι, ∑ t : ι,
        (F s t : ℂ) *
        (if t = s then (1 / dims t : ℂ) * repCharacter (ρ t) (V * W) else 0) ∂μ from by
    congr 1 with g₀
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    exact hInner_full g₀ s t]
  -- Pull constant out of g₀ integral (integrand is independent of g₀)
  rw [show (∫ g₀, ∑ s : ι, ∑ t : ι,
        (F s t : ℂ) *
        (if t = s then (1 / dims t : ℂ) * repCharacter (ρ t) (V * W) else 0) ∂μ) =
      ∑ s : ι, ∑ t : ι,
        (F s t : ℂ) *
        (if t = s then (1 / dims t : ℂ) * repCharacter (ρ t) (V * W) else 0) from by
    haveI : IsFiniteMeasure μ := inferInstance
    simp [integral_const, IsProbabilityMeasure.measure_univ]]
  -- Collapse the if and simplify
  rw [show (∑ s : ι, ∑ t : ι,
        (F s t : ℂ) *
        (if t = s then (1 / dims t : ℂ) * repCharacter (ρ t) (V * W) else 0)) =
      ∑ s : ι, (F s s : ℂ) *
        ((1 / dims s : ℂ) * repCharacter (ρ s) (V * W)) from by
    apply Finset.sum_congr rfl
    intro s _
    have key : ∑ t : ι, (F s t : ℂ) *
        (if t = s then (1 / dims t : ℂ) * repCharacter (ρ t) (V * W) else 0) =
      (F s s : ℂ) *
        (if s = s then (1 / dims s : ℂ) * repCharacter (ρ s) (V * W) else 0) := by
      refine Finset.sum_eq_single s ?_ ?_
      · intro t _ hne
        rw [if_neg (fun h => hne h)]
        ring
      · intro h; exact absurd (Finset.mem_univ s) h
    rw [key, if_pos rfl]]
  -- χ_s(V*W) = χ_s(W*V) by trace_mul_comm
  apply Finset.sum_congr rfl
  intro s _
  rw [show repCharacter (ρ s) (V * W) = repCharacter (ρ s) (W * V) from by
    show Matrix.trace (ρ s (V * W)) = Matrix.trace (ρ s (W * V))
    rw [show ρ s (V * W) = ρ s V * ρ s W from MonoidHom.map_mul _ _ _,
        show ρ s (W * V) = ρ s W * ρ s V from MonoidHom.map_mul _ _ _,
        Matrix.trace_mul_comm]]

#print axioms luscher_2site_cascade_coeff

/-- **3-site Lüscher cascade with arbitrary non-negative coefficients (Step 3, multi-plaquette).**

For irreducible unitary representations of a compact group with normalized Haar
measure, and arbitrary non-negative coefficients `F : ι → ι → ι → ℝ` with
`F s t u ≥ 0`, the 3-site cascade with summed character products evaluates to:

    ∫∫∫ ∑_{s,t,u} F(s,t,u) · χ_s(g₀·W₀·g₁⁻¹) · χ_t(g₁·W₁·g₂⁻¹) · χ_u(g₂·W₂·g₀⁻¹) dg₁ dg₂ dg₀
      = ∑_s F(s,s,s) · (1/d_s)² · χ_s(W₀·W₁·W₂)

The coefficient `F(s,s,s) · (1/d_s)² ≥ 0` (since `F(s,s,s) ≥ 0` and `(1/d_s)² > 0`),
so the resulting kernel matches `character_kernel_integral_nonneg`. This generalizes
`luscher_2site_cascade_coeff` to the 3-plaquette case (three plaquettes sharing three
temporal links `g₀, g₁, g₂`). 0 sorries, 0 new axioms.

The proof uses an inductive approach: (1) integrate out `g₁` via `luscher_key_identity`
(Schur orthogonality forces `t = s`), producing a 2-site cascade with coefficients
`G(s,u) = F(s,s,u) · (1/d_s) ≥ 0`; (2) apply `luscher_2site_cascade_coeff` to integrate
out `g₂` (Schur orthogonality forces `u = s`), producing the final kernel with
coefficients `F(s,s,s) · (1/d_s)² ≥ 0`. -/
lemma luscher_3site_cascade_coeff
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (F : ι → ι → ι → ℝ) (hF : ∀ s t u, 0 ≤ F s t u)
    (W₀ W₁ W₂ : G) :
    ∫ g₀, ∫ g₂, ∫ g₁,
      ∑ s, ∑ t, ∑ u, (F s t u : ℂ) *
        (repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) *
         repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹) *
         repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹)) ∂μ ∂μ ∂μ =
    ∑ s, (F s s s : ℂ) * ((1 / dims s : ℂ)^2 * repCharacter (ρ s) (W₀ * W₁ * W₂)) := by
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  -- Step 1: Integrability of each (s,t,u) term w.r.t. g₁
  have hInt_stu : ∀ (g₀ g₂ : G) (s t u : ι),
      Integrable (fun g₁ =>
        (F s t u : ℂ) *
        (repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) *
         repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹) *
         repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹))) μ := by
    intro g₀ g₂ s t u
    have hst : Integrable (fun g₁ =>
      repCharacter (ρ s) ((g₀ * W₀) * g₁⁻¹) *
      repCharacter (ρ t) (g₁ * (W₁ * g₂⁻¹))) μ :=
      char_product_integrable μ ι dims hDims ρ hU hIrr s t (g₀ * W₀) (W₁ * g₂⁻¹)
    exact (hst.smul ((F s t u : ℂ) * repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹))).congr
      (Filter.Eventually.of_forall (fun g₁ => by
        simp only [Pi.smul_def, smul_eq_mul]
        rw [show g₁ * W₁ * g₂⁻¹ = g₁ * (W₁ * g₂⁻¹) from mul_assoc g₁ W₁ g₂⁻¹]
        ring))
  have hInt_tu : ∀ (g₀ g₂ : G) (s t : ι),
      Integrable (fun g₁ =>
        ∑ u : ι, (F s t u : ℂ) *
        (repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) *
         repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹) *
         repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹))) μ :=
    fun g₀ g₂ s t => integrable_finsetSum Finset.univ (fun u _ => hInt_stu g₀ g₂ s t u)
  have hInt_u : ∀ (g₀ g₂ : G) (s : ι),
      Integrable (fun g₁ =>
        ∑ t : ι, ∑ u : ι, (F s t u : ℂ) *
        (repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) *
         repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹) *
         repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹))) μ :=
    fun g₀ g₂ s => integrable_finsetSum Finset.univ (fun t _ => hInt_tu g₀ g₂ s t)
  -- Step 2: Inner integral via luscher_key_identity (following luscher_3site_cascade pattern)
  have hInner : ∀ (g₀ g₂ : G) (s t u : ι),
      ∫ g₁, repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) *
             repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹) *
             repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹) ∂μ =
        (if t = s then (1 / dims t : ℂ) * repCharacter (ρ t) (g₀ * W₀ * W₁ * g₂⁻¹) else 0) *
        repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹) := by
    intro g₀ g₂ s t u
    rw [show (∫ g₁, repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) *
          repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹) *
          repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹) ∂μ) =
        ∫ g₁, repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹) *
          (repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) * repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹)) ∂μ from by
      congr 1 with g₁; ring]
    rw [integral_const_mul]
    rw [show (∫ g₁, repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) *
          repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹) ∂μ) =
        ∫ g₁, repCharacter (ρ t) (g₁ * (W₁ * g₂⁻¹)) *
          repCharacter (ρ s) (g₁⁻¹ * (g₀ * W₀)) ∂μ from by
      congr 1 with g₁
      rw [show repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) = repCharacter (ρ s) (g₁⁻¹ * (g₀ * W₀)) from by
        rw [repCharacter_cyclic, repCharacter_cyclic, mul_assoc]]
      rw [show repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹) = repCharacter (ρ t) (g₁ * (W₁ * g₂⁻¹)) from by
        rw [mul_assoc]]
      ring]
    rw [luscher_key_identity μ ι dims hDims ρ hU hIrr t s (W₁ * g₂⁻¹) (g₀ * W₀)]
    by_cases h : t = s
    · rw [if_pos h, if_pos h]
      rw [show repCharacter (ρ t) ((W₁ * g₂⁻¹) * (g₀ * W₀)) =
            repCharacter (ρ t) (g₀ * W₀ * W₁ * g₂⁻¹) from by
        rw [← mul_assoc (W₁ * g₂⁻¹) g₀ W₀, repCharacter_cyclic, ← mul_assoc (g₀ * W₀) W₁ g₂⁻¹]]
      ring
    · rw [if_neg h, if_neg h]
      ring
  have hInner_full : ∀ (g₀ g₂ : G) (s t u : ι),
      ∫ g₁, (F s t u : ℂ) *
        (repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) *
         repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹) *
         repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹)) ∂μ =
      (F s t u : ℂ) *
        ((if t = s then (1 / dims t : ℂ) * repCharacter (ρ t) (g₀ * W₀ * W₁ * g₂⁻¹) else 0) *
         repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹)) := by
    intro g₀ g₂ s t u
    rw [integral_const_mul, hInner g₀ g₂ s t u]
  -- Step 3: Exchange ∑_s with ∫ g₁
  rw [show (∫ g₀, ∫ g₂, ∫ g₁,
        (∑ s : ι, ∑ t : ι, ∑ u : ι, (F s t u : ℂ) *
          (repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) *
           repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹) *
           repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹))) ∂μ ∂μ ∂μ) =
      ∫ g₀, ∫ g₂, ∑ s : ι, ∫ g₁,
        (∑ t : ι, ∑ u : ι, (F s t u : ℂ) *
          (repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) *
           repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹) *
           repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹))) ∂μ ∂μ ∂μ from by
    congr 1 with g₀
    congr 1 with g₂
    rw [integral_finsetSum Finset.univ (fun s _ => hInt_u g₀ g₂ s)]]
  -- Step 4: Exchange ∑_t with ∫ g₁
  rw [show (∫ g₀, ∫ g₂, ∑ s : ι, ∫ g₁,
        (∑ t : ι, ∑ u : ι, (F s t u : ℂ) *
          (repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) *
           repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹) *
           repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹))) ∂μ ∂μ ∂μ) =
      ∫ g₀, ∫ g₂, ∑ s : ι, ∑ t : ι, ∫ g₁,
        (∑ u : ι, (F s t u : ℂ) *
          (repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) *
           repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹) *
           repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹))) ∂μ ∂μ ∂μ from by
    congr 1 with g₀
    congr 1 with g₂
    apply Finset.sum_congr rfl
    intro s _
    rw [integral_finsetSum Finset.univ (fun t _ => hInt_tu g₀ g₂ s t)]]
  -- Step 5: Exchange ∑_u with ∫ g₁
  rw [show (∫ g₀, ∫ g₂, ∑ s : ι, ∑ t : ι, ∫ g₁,
        (∑ u : ι, (F s t u : ℂ) *
          (repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) *
           repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹) *
           repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹))) ∂μ ∂μ ∂μ) =
      ∫ g₀, ∫ g₂, ∑ s : ι, ∑ t : ι, ∑ u : ι, ∫ g₁,
        ((F s t u : ℂ) *
          (repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) *
           repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹) *
           repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹))) ∂μ ∂μ ∂μ from by
    congr 1 with g₀
    congr 1 with g₂
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    rw [integral_finsetSum Finset.univ (fun u _ => hInt_stu g₀ g₂ s t u)]]
  -- Step 6: Apply hInner_full to each inner integral
  rw [show (∫ g₀, ∫ g₂, ∑ s : ι, ∑ t : ι, ∑ u : ι, ∫ g₁,
        ((F s t u : ℂ) *
          (repCharacter (ρ s) (g₀ * W₀ * g₁⁻¹) *
           repCharacter (ρ t) (g₁ * W₁ * g₂⁻¹) *
           repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹))) ∂μ ∂μ ∂μ) =
      ∫ g₀, ∫ g₂, ∑ s : ι, ∑ t : ι, ∑ u : ι,
        (F s t u : ℂ) *
        ((if t = s then (1 / dims t : ℂ) * repCharacter (ρ t) (g₀ * W₀ * W₁ * g₂⁻¹) else 0) *
         repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹)) ∂μ ∂μ from by
    congr 1 with g₀
    congr 1 with g₂
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro u _
    exact hInner_full g₀ g₂ s t u]
  -- Step 7: Collapse the if t = s (keep only t = s terms)
  rw [show (∫ g₀, ∫ g₂, ∑ s : ι, ∑ t : ι, ∑ u : ι,
        (F s t u : ℂ) *
        ((if t = s then (1 / dims t : ℂ) * repCharacter (ρ t) (g₀ * W₀ * W₁ * g₂⁻¹) else 0) *
         repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹)) ∂μ ∂μ) =
      ∫ g₀, ∫ g₂, ∑ s : ι, ∑ u : ι,
        (F s s u : ℂ) *
        ((1 / dims s : ℂ) * repCharacter (ρ s) (g₀ * W₀ * W₁ * g₂⁻¹) *
         repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹)) ∂μ ∂μ from by
    congr 1 with g₀
    congr 1 with g₂
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    have key : ∑ t : ι, (F s t u : ℂ) *
        ((if t = s then (1 / dims t : ℂ) * repCharacter (ρ t) (g₀ * W₀ * W₁ * g₂⁻¹) else 0) *
         repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹)) =
      (F s s u : ℂ) *
        ((if s = s then (1 / dims s : ℂ) * repCharacter (ρ s) (g₀ * W₀ * W₁ * g₂⁻¹) else 0) *
         repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹)) := by
      refine Finset.sum_eq_single s ?_ ?_
      · intro t _ hne
        rw [if_neg (fun h => hne h)]
        ring
      · intro h; exact absurd (Finset.mem_univ s) h
    rw [key, if_pos rfl]]
  -- Step 8: Apply luscher_2site_cascade_coeff
  let G : ι → ι → ℝ := fun s u => F s s u / dims s
  have hG : ∀ s u, 0 ≤ G s u := fun s u => div_nonneg (hF s s u) (Nat.cast_nonneg _)
  have hG_eq : ∀ s u, (G s u : ℂ) = (F s s u : ℂ) * (1 / (dims s : ℂ)) := by
    intro s u
    rw [show G s u = F s s u / dims s from rfl]
    push_cast
    field_simp
  rw [show (∫ g₀, ∫ g₂, ∑ s : ι, ∑ u : ι,
        (F s s u : ℂ) *
        ((1 / dims s : ℂ) * repCharacter (ρ s) (g₀ * W₀ * W₁ * g₂⁻¹) *
         repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹)) ∂μ ∂μ) =
      ∫ g₀, ∫ g₂, ∑ s : ι, ∑ u : ι,
        (G s u : ℂ) *
        (repCharacter (ρ s) (g₀ * (W₀ * W₁) * g₂⁻¹) *
         repCharacter (ρ u) (g₂ * W₂ * g₀⁻¹)) ∂μ ∂μ from by
    congr 1 with g₀
    congr 1 with g₂
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro u _
    rw [hG_eq s u]
    rw [show g₀ * W₀ * W₁ * g₂⁻¹ = g₀ * (W₀ * W₁) * g₂⁻¹ from by rw [mul_assoc g₀ W₀ W₁]]
    ring]
  rw [luscher_2site_cascade_coeff μ ι dims hDims ρ hU hIrr G hG (W₀ * W₁) W₂]
  -- Step 9: Simplify to final form
  apply Finset.sum_congr rfl
  intro s _
  rw [show repCharacter (ρ s) ((W₀ * W₁) * W₂) = repCharacter (ρ s) (W₀ * W₁ * W₂) from rfl]
  rw [hG_eq s s]
  push_cast
  ring

#print axioms luscher_3site_cascade_coeff

/-- **Conjugation integral** (key building block for the Lüscher cascade, §8.11.71).

For an irreducible unitary representation `ρ_γ` of a compact group `G` with
normalized Haar measure `μ`, and any `M, N : G`:

    ∫_G χ_γ(g⁻¹ · M · g · N) ∂μ(g) = (1/d_γ) · χ_γ(M) · χ_γ(N)

This is the fundamental identity for the Lüscher cascade with conjugation
(the L=2 case): expanding `χ_γ(g⁻¹·M·g·N) = Tr(ρ(g⁻¹)·ρ(M)·ρ(g)·ρ(N))` in
matrix elements, using the unitary property `ρ(g⁻¹) = ρ(g)†` to replace
`ρ(g⁻¹)_{ac}` with `conj(ρ(g)_{ca})`, and applying Schur orthogonality
`∫ ρ(g)_{bd} · conj(ρ(g)_{ca}) dg = δ_{bc}·δ_{ad}/d_γ`, the Kronecker
deltas collapse the 4-index sum to `(1/d_γ) · Tr(ρ(M)) · Tr(ρ(N)) =
(1/d_γ) · χ_γ(M) · χ_γ(N)`.

The coefficient `1/d_γ > 0` is strictly positive, and `χ_γ` is positive-definite.
0 sorries, 0 new axioms. -/
lemma conjugation_integral
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (γ : ι) (M N : G) :
    ∫ g, repCharacter (ρ γ) (g⁻¹ * M * g * N) ∂μ =
      (1 / dims γ : ℂ) * repCharacter (ρ γ) M * repCharacter (ρ γ) N := by
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  -- Helper: unitary matrix element (ρ i g⁻¹) c d = conj ((ρ i g) d c)
  have h_unitary_elem : ∀ (i : ι) (g : G) (c d : Fin (dims i)),
      (ρ i g⁻¹) c d = conj ((ρ i g) d c) := by
    intro i g c d
    have h_star : (ρ i g)ᴴ = ρ i g⁻¹ := by
      rw [conjTranspose_eq_inv_of_unitary (hU i g)]
      have hmul : ρ i g * ρ i g⁻¹ = 1 := by
        rw [← MonoidHom.map_mul, show g * g⁻¹ = 1 from by simp, MonoidHom.map_one]
      exact Matrix.inv_eq_right_inv hmul
    rw [← h_star, Matrix.conjTranspose_apply]
    simp [Complex.star_def]
  -- Helper: trace of product Tr(AB) = ∑ i j, A i j * B j i
  have htrace_mul : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ),
      Matrix.trace (A * B) = ∑ i : Fin n, ∑ j : Fin n, A i j * B j i := by
    intro n A B
    simp [Matrix.trace, Matrix.mul_apply]
  -- Step 1: regroup g⁻¹ * M * g * N = (g⁻¹ * M) * (g * N) and map_mul
  have hmap : ∀ (g : G), ρ γ (g⁻¹ * M * g * N) = ρ γ (g⁻¹ * M) * ρ γ (g * N) := by
    intro g
    rw [mul_assoc, MonoidHom.map_mul]
  -- Step 2: Expand χ_γ(g⁻¹ * M * g * N) = Σ a b, (ρ(g⁻¹ * M))_{ab} * (ρ(g * N))_{ba}
  have hchar : ∀ (g : G),
      repCharacter (ρ γ) (g⁻¹ * M * g * N) =
        ∑ a : Fin (dims γ), ∑ b : Fin (dims γ),
          (ρ γ (g⁻¹ * M)) a b * (ρ γ (g * N)) b a := by
    intro g
    rw [repCharacter, hmap, htrace_mul]
  -- Step 3: Expand matrix elements with unitarity
  have hME1 : ∀ (g : G) (a b : Fin (dims γ)),
      (ρ γ (g⁻¹ * M)) a b = ∑ c : Fin (dims γ), conj ((ρ γ g) c a) * (ρ γ M) c b := by
    intro g a b
    rw [show ρ γ (g⁻¹ * M) = ρ γ g⁻¹ * ρ γ M from MonoidHom.map_mul (ρ γ) g⁻¹ M, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro c _
    rw [h_unitary_elem γ g a c]
  have hME2 : ∀ (g : G) (b a : Fin (dims γ)),
      (ρ γ (g * N)) b a = ∑ d : Fin (dims γ), (ρ γ g) b d * (ρ γ N) d a := by
    intro g b a
    rw [show ρ γ (g * N) = ρ γ g * ρ γ N from MonoidHom.map_mul (ρ γ) g N, Matrix.mul_apply]
  -- Step 4: Combine into 4-index sum
  have hchar4 : ∀ (g : G),
      repCharacter (ρ γ) (g⁻¹ * M * g * N) =
        ∑ a : Fin (dims γ), ∑ b : Fin (dims γ), ∑ c : Fin (dims γ), ∑ d : Fin (dims γ),
          conj ((ρ γ g) c a) * (ρ γ M) c b * (ρ γ g) b d * (ρ γ N) d a := by
    intro g
    rw [hchar]
    rw [show (∑ a : Fin (dims γ), ∑ b : Fin (dims γ),
          (ρ γ (g⁻¹ * M)) a b * (ρ γ (g * N)) b a) =
        ∑ a : Fin (dims γ), ∑ b : Fin (dims γ),
          (∑ c : Fin (dims γ), conj ((ρ γ g) c a) * (ρ γ M) c b) *
          (∑ d : Fin (dims γ), (ρ γ g) b d * (ρ γ N) d a) from by
      congr 1 with a
      congr 1 with b
      rw [hME1, hME2]]
    simp only [Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    ring
  -- Step 5: Rewrite the integral using the pointwise identity
  rw [show (∫ g, repCharacter (ρ γ) (g⁻¹ * M * g * N) ∂μ) =
        ∫ g, (∑ a : Fin (dims γ), ∑ b : Fin (dims γ), ∑ c : Fin (dims γ), ∑ d : Fin (dims γ),
          conj ((ρ γ g) c a) * (ρ γ M) c b * (ρ γ g) b d * (ρ γ N) d a) ∂μ from by
    congr 1 with g; exact hchar4 g]
  -- Step 6: Integrability of each 4-index term
  have hInt_term : ∀ (a b c d : Fin (dims γ)),
      Integrable (fun g =>
        conj ((ρ γ g) c a) * (ρ γ M) c b * (ρ γ g) b d * (ρ γ N) d a) μ := by
    intro a b c d
    have h_gdep : Integrable (fun g => (ρ γ g) b d * conj ((ρ γ g) c a)) μ :=
      hInt γ γ b d c a
    refine (h_gdep.smul ((ρ γ M) c b * (ρ γ N) d a)).congr ?_
    exact Filter.Eventually.of_forall (fun g => by
      simp only [Pi.smul_def, smul_eq_mul]
      ring)
  -- Integrability helpers for each sum level (order: a, b, c, d)
  have hInt_d : ∀ (a b c : Fin (dims γ)),
      Integrable (fun g => ∑ d : Fin (dims γ),
        conj ((ρ γ g) c a) * (ρ γ M) c b * (ρ γ g) b d * (ρ γ N) d a) μ :=
    fun a b c => integrable_finsetSum Finset.univ (fun d _ => hInt_term a b c d)
  have hInt_c : ∀ (a b : Fin (dims γ)),
      Integrable (fun g => ∑ c : Fin (dims γ), ∑ d : Fin (dims γ),
        conj ((ρ γ g) c a) * (ρ γ M) c b * (ρ γ g) b d * (ρ γ N) d a) μ :=
    fun a b => integrable_finsetSum Finset.univ (fun c _ => hInt_d a b c)
  have hInt_b : ∀ (a : Fin (dims γ)),
      Integrable (fun g => ∑ b : Fin (dims γ), ∑ c : Fin (dims γ), ∑ d : Fin (dims γ),
        conj ((ρ γ g) c a) * (ρ γ M) c b * (ρ γ g) b d * (ρ γ N) d a) μ :=
    fun a => integrable_finsetSum Finset.univ (fun b _ => hInt_c a b)
  -- Step 7: Exchange 4 sums with integral
  rw [integral_finsetSum Finset.univ (fun a _ => hInt_b a)]
  rw [show (∑ a : Fin (dims γ), ∫ g, ∑ b : Fin (dims γ), ∑ c : Fin (dims γ), ∑ d : Fin (dims γ),
        conj ((ρ γ g) c a) * (ρ γ M) c b * (ρ γ g) b d * (ρ γ N) d a ∂μ) =
      ∑ a : Fin (dims γ), ∑ b : Fin (dims γ), ∫ g, ∑ c : Fin (dims γ), ∑ d : Fin (dims γ),
        conj ((ρ γ g) c a) * (ρ γ M) c b * (ρ γ g) b d * (ρ γ N) d a ∂μ from by
    apply Finset.sum_congr rfl
    intro a _
    rw [integral_finsetSum Finset.univ (fun b _ => hInt_c a b)]]
  rw [show (∑ a : Fin (dims γ), ∑ b : Fin (dims γ), ∫ g, ∑ c : Fin (dims γ), ∑ d : Fin (dims γ),
        conj ((ρ γ g) c a) * (ρ γ M) c b * (ρ γ g) b d * (ρ γ N) d a ∂μ) =
      ∑ a : Fin (dims γ), ∑ b : Fin (dims γ), ∑ c : Fin (dims γ), ∫ g, ∑ d : Fin (dims γ),
        conj ((ρ γ g) c a) * (ρ γ M) c b * (ρ γ g) b d * (ρ γ N) d a ∂μ from by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [integral_finsetSum Finset.univ (fun c _ => hInt_d a b c)]]
  rw [show (∑ a : Fin (dims γ), ∑ b : Fin (dims γ), ∑ c : Fin (dims γ), ∫ g, ∑ d : Fin (dims γ),
        conj ((ρ γ g) c a) * (ρ γ M) c b * (ρ γ g) b d * (ρ γ N) d a ∂μ) =
      ∑ a : Fin (dims γ), ∑ b : Fin (dims γ), ∑ c : Fin (dims γ), ∑ d : Fin (dims γ),
        ∫ g, conj ((ρ γ g) c a) * (ρ γ M) c b * (ρ γ g) b d * (ρ γ N) d a ∂μ from by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    rw [integral_finsetSum Finset.univ (fun d _ => hInt_term a b c d)]]
  -- Step 8: Factor constants out of each integral
  have hfactor : ∀ (a b c d : Fin (dims γ)),
      ∫ g, conj ((ρ γ g) c a) * (ρ γ M) c b * (ρ γ g) b d * (ρ γ N) d a ∂μ
        = (ρ γ M) c b * (ρ γ N) d a * ∫ g, (ρ γ g) b d * conj ((ρ γ g) c a) ∂μ := by
    intro a b c d
    rw [show (∫ g, conj ((ρ γ g) c a) * (ρ γ M) c b * (ρ γ g) b d * (ρ γ N) d a ∂μ) =
          ∫ g, ((ρ γ M) c b * (ρ γ N) d a) • ((ρ γ g) b d * conj ((ρ γ g) c a)) ∂μ from by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun g => by simp only [smul_eq_mul]; ring)]
    rw [integral_smul]
    simp only [smul_eq_mul]
  -- Apply hfactor to all terms
  rw [show (∑ a : Fin (dims γ), ∑ b : Fin (dims γ), ∑ c : Fin (dims γ), ∑ d : Fin (dims γ),
        ∫ g, conj ((ρ γ g) c a) * (ρ γ M) c b * (ρ γ g) b d * (ρ γ N) d a ∂μ) =
      ∑ a : Fin (dims γ), ∑ b : Fin (dims γ), ∑ c : Fin (dims γ), ∑ d : Fin (dims γ),
        (ρ γ M) c b * (ρ γ N) d a * ∫ g, (ρ γ g) b d * conj ((ρ γ g) c a) ∂μ from by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    exact hfactor a b c d]
  -- Step 9: Apply Schur orthogonality (diagonal: same irrep γ)
  simp only [hSchur_diag]
  -- Step 10: Collapse the d-sum (picks d = a)
  have hd : ∀ (a b c : Fin (dims γ)),
      ∑ d : Fin (dims γ), (ρ γ M) c b * (ρ γ N) d a *
        (if b = c ∧ d = a then (1 / dims γ : ℂ) else 0)
      = (ρ γ M) c b * (ρ γ N) a a * (if b = c then (1 / dims γ : ℂ) else 0) := by
    intro a b c
    have heq : ∑ d : Fin (dims γ), (ρ γ M) c b * (ρ γ N) d a *
        (if b = c ∧ d = a then (1 / dims γ : ℂ) else 0)
      = (ρ γ M) c b * (ρ γ N) a a * (if b = c ∧ a = a then (1 / dims γ : ℂ) else 0) := by
      refine Finset.sum_eq_single a ?_ ?_
      · intro d _ hd
        have hda : ¬ (d = a) := hd
        have hneg : ¬ (b = c ∧ d = a) := fun h => hda h.2
        rw [if_neg hneg]
        ring
      · intro h
        exact absurd (Finset.mem_univ a) h
    rw [heq]
    simp only [eq_self_iff_true, and_true]
  -- Apply hd to simplify the d-sum
  rw [show (∑ a : Fin (dims γ), ∑ b : Fin (dims γ), ∑ c : Fin (dims γ), ∑ d : Fin (dims γ),
        (ρ γ M) c b * (ρ γ N) d a * (if b = c ∧ d = a then (1 / dims γ : ℂ) else 0)) =
      ∑ a : Fin (dims γ), ∑ b : Fin (dims γ), ∑ c : Fin (dims γ),
        (ρ γ M) c b * (ρ γ N) a a * (if b = c then (1 / dims γ : ℂ) else 0) from by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    exact hd a b c]
  -- Step 11: Collapse the c-sum (picks c = b)
  have hc : ∀ (a b : Fin (dims γ)),
      ∑ c : Fin (dims γ), (ρ γ M) c b * (ρ γ N) a a *
        (if b = c then (1 / dims γ : ℂ) else 0)
      = (ρ γ M) b b * (ρ γ N) a a * (1 / dims γ : ℂ) := by
    intro a b
    have heq : ∑ c : Fin (dims γ), (ρ γ M) c b * (ρ γ N) a a *
        (if b = c then (1 / dims γ : ℂ) else 0)
      = (ρ γ M) b b * (ρ γ N) a a * (if b = b then (1 / dims γ : ℂ) else 0) := by
      refine Finset.sum_eq_single b ?_ ?_
      · intro c _ hcb
        have hneg : ¬ (b = c) := fun h => hcb h.symm
        rw [if_neg hneg]
        ring
      · intro h
        exact absurd (Finset.mem_univ b) h
    rw [heq]
    simp only [eq_self_iff_true, if_true]
  -- Apply hc to simplify the c-sum
  rw [show (∑ a : Fin (dims γ), ∑ b : Fin (dims γ), ∑ c : Fin (dims γ),
        (ρ γ M) c b * (ρ γ N) a a * (if b = c then (1 / dims γ : ℂ) else 0)) =
      ∑ a : Fin (dims γ), ∑ b : Fin (dims γ),
        (ρ γ M) b b * (ρ γ N) a a * (1 / dims γ : ℂ) from by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    exact hc a b]
  -- Step 12: Factor out (1 / dims γ) and recognize the traces
  rw [show (∑ a : Fin (dims γ), ∑ b : Fin (dims γ),
        (ρ γ M) b b * (ρ γ N) a a * (1 / dims γ : ℂ)) =
      (1 / dims γ : ℂ) * (∑ b : Fin (dims γ), (ρ γ M) b b) * (∑ a : Fin (dims γ), (ρ γ N) a a) from by
    -- Factor (1 / dims γ) out of the inner sum
    rw [show ∑ a, ∑ b, (ρ γ M) b b * (ρ γ N) a a * (1 / dims γ : ℂ) =
          ∑ a, (∑ b, (ρ γ M) b b * (ρ γ N) a a) * (1 / dims γ : ℂ) from by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_mul]]
    -- Factor (1 / dims γ) out of the outer sum
    rw [show ∑ a, (∑ b, (ρ γ M) b b * (ρ γ N) a a) * (1 / dims γ : ℂ) =
          (∑ a, ∑ b, (ρ γ M) b b * (ρ γ N) a a) * (1 / dims γ : ℂ) from by
      rw [Finset.sum_mul]]
    -- Factor the double sum into a product of sums
    rw [Finset.sum_comm, ← Fintype.sum_mul_sum]
    ring]
  rw [show (∑ b : Fin (dims γ), (ρ γ M) b b) = repCharacter (ρ γ) M from by
      simp [repCharacter, Matrix.trace]]
  rw [show (∑ a : Fin (dims γ), (ρ γ N) a a) = repCharacter (ρ γ) N from by
      simp [repCharacter, Matrix.trace]]

#print axioms conjugation_integral

set_option maxHeartbeats 400000 in
/-- **Cyclic bipartite L-site cascade (Step 3b, cyclic closure).**

Closing the bipartite chain (a = b = g₀, integrated out) via `conjugation_integral`
gives the separable kernel:

    ∫ g₀, bipartiteChainIntegral g₀ g₀ [(γ₀,V₀,W₀),...,(γₙ,Vₙ,Wₙ)] dg₀
      = δ_{all γ=γ₀} · (1/d_γ)^(n+1) · χ_γ(W-product⁻¹) · χ_γ(V-product)

The coefficient `(1/d_γ)^(n+1) > 0` and the kernel `χ(W-product⁻¹) · χ(V-product)`
is separable with non-negative coefficients — the form needed for
`shared_cascade_factorization_nonneg`. 0 sorries, 0 new axioms. -/
lemma bipartiteCyclicCascade_eq
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (γ₀ : ι) (V₀ W₀ : G) (rest : List (ι × G × G)) :
    ∫ g₀, bipartiteChainIntegral μ ι dims ρ g₀ g₀ ((γ₀, V₀, W₀) :: rest) ∂μ =
      if allSameRep3 γ₀ rest then
        (1 / dims γ₀ : ℂ)^(rest.length + 1) *
        repCharacter (ρ γ₀) ((W₀ :: rest.map (fun x => x.2.2)).prod)⁻¹ *
        repCharacter (ρ γ₀) (V₀ :: rest.map (fun x => x.2.1)).prod
      else 0 := by
  rw [show (∫ g₀, bipartiteChainIntegral μ ι dims ρ g₀ g₀ ((γ₀, V₀, W₀) :: rest) ∂μ) =
      ∫ g₀, (if allSameRep3 γ₀ rest then
        (1 / dims γ₀ : ℂ) ^ rest.length *
          repCharacter (ρ γ₀) (g₀ * (V₀ :: rest.map (fun x => x.2.1)).prod * g₀⁻¹ *
            (W₀ :: rest.map (fun x => x.2.2)).prod⁻¹)
        else 0) ∂μ from by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun g₀ =>
      bipartiteChainIntegral_eq μ ι dims hDims ρ hU hIrr g₀ g₀ γ₀ V₀ W₀ rest)]
  by_cases h : allSameRep3 γ₀ rest
  · -- True case: all reps match
    simp only [if_pos h]
    -- Pull constant (1/d)^n out of the integral
    rw [integral_const_mul]
    -- Cyclic rewrite: χ(g₀·V·g₀⁻¹·W⁻¹) = χ(g₀⁻¹·W⁻¹·g₀·V) via repCharacter_cyclic
    have hcyc : ∀ g, repCharacter (ρ γ₀) (g * (V₀ :: rest.map (fun x => x.2.1)).prod * g⁻¹ *
          ((W₀ :: rest.map (fun x => x.2.2)).prod)⁻¹) =
        repCharacter (ρ γ₀) (g⁻¹ * ((W₀ :: rest.map (fun x => x.2.2)).prod)⁻¹ *
          g * (V₀ :: rest.map (fun x => x.2.1)).prod) := by
      intro g
      rw [repCharacter_cyclic (ρ γ₀) (g * (V₀ :: rest.map (fun x => x.2.1)).prod) g⁻¹
        ((W₀ :: rest.map (fun x => x.2.2)).prod)⁻¹]
      congr 1
      ac_rfl
    rw [show ∫ g₀, repCharacter (ρ γ₀) (g₀ * (V₀ :: rest.map (fun x => x.2.1)).prod * g₀⁻¹ *
          ((W₀ :: rest.map (fun x => x.2.2)).prod)⁻¹) ∂μ =
        ∫ g₀, repCharacter (ρ γ₀) (g₀⁻¹ * ((W₀ :: rest.map (fun x => x.2.2)).prod)⁻¹ *
          g₀ * (V₀ :: rest.map (fun x => x.2.1)).prod) ∂μ from by
      exact integral_congr_ae (Filter.Eventually.of_forall hcyc)]
    -- Apply conjugation_integral: ∫ χ(g⁻¹·M·g·N) = (1/d)·χ(M)·χ(N)
    rw [show ∫ g₀, repCharacter (ρ γ₀) (g₀⁻¹ * ((W₀ :: rest.map (fun x => x.2.2)).prod)⁻¹ *
          g₀ * (V₀ :: rest.map (fun x => x.2.1)).prod) ∂μ =
        (1 / dims γ₀ : ℂ) * repCharacter (ρ γ₀) ((W₀ :: rest.map (fun x => x.2.2)).prod)⁻¹ *
          repCharacter (ρ γ₀) (V₀ :: rest.map (fun x => x.2.1)).prod from by
      exact conjugation_integral μ ι dims hDims ρ hU hIrr γ₀
        ((W₀ :: rest.map (fun x => x.2.2)).prod)⁻¹
        (V₀ :: rest.map (fun x => x.2.1)).prod]
    -- Simplify powers: (1/d)^n * (1/d) = (1/d)^(n+1)
    rw [pow_add, pow_one]
    ring
  · -- False case: reps don't all match → 0
    simp only [if_neg h, integral_zero]

#print axioms bipartiteCyclicCascade_eq

/-- **Integrability of the conjugation character** `χ_γ(g⁻¹ · M · g · N)`.

For irreducible unitary representations of a compact group with normalized Haar
measure, the function `g ↦ χ_γ(g⁻¹ · M · g · N)` is integrable. This follows from
expanding the character into matrix elements and applying Schur orthogonality
integrability. Extracted from the local `hInt_char_conj` in
`luscher_2site_cascade_separable` for reuse in the cyclic cascade. -/
lemma char_conjugation_integrable
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (γ : ι) (M N : G) :
    Integrable (fun g => repCharacter (ρ γ) (g⁻¹ * M * g * N)) μ := by
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  have h_unitary_elem : ∀ (g : G) (c d : Fin (dims γ)),
      (ρ γ g⁻¹) c d = conj ((ρ γ g) d c) := by
    intro g c d
    have h_star : (ρ γ g)ᴴ = ρ γ g⁻¹ := by
      rw [conjTranspose_eq_inv_of_unitary (hU γ g)]
      have hmul : ρ γ g * ρ γ g⁻¹ = 1 := by
        rw [← MonoidHom.map_mul, show g * g⁻¹ = 1 from by simp, MonoidHom.map_one]
      exact Matrix.inv_eq_right_inv hmul
    rw [← h_star, Matrix.conjTranspose_apply]
    simp [Complex.star_def]
  have htrace_mul : ∀ (A B : Matrix (Fin (dims γ)) (Fin (dims γ)) ℂ),
      Matrix.trace (A * B) = ∑ a : Fin (dims γ), ∑ b : Fin (dims γ), A a b * B b a := by
    intro A B
    simp [Matrix.trace, Matrix.mul_apply]
  have hmap : ∀ (g : G), ρ γ (g⁻¹ * M * g * N) = ρ γ (g⁻¹ * M) * ρ γ (g * N) := by
    intro g
    rw [mul_assoc, MonoidHom.map_mul]
  have hchar : ∀ (g : G),
      repCharacter (ρ γ) (g⁻¹ * M * g * N) =
        ∑ a : Fin (dims γ), ∑ b : Fin (dims γ),
          (ρ γ (g⁻¹ * M)) a b * (ρ γ (g * N)) b a := by
    intro g
    rw [repCharacter, hmap, htrace_mul]
  have hME1 : ∀ (g : G) (a b : Fin (dims γ)),
      (ρ γ (g⁻¹ * M)) a b = ∑ c : Fin (dims γ), conj ((ρ γ g) c a) * (ρ γ M) c b := by
    intro g a b
    rw [show ρ γ (g⁻¹ * M) = ρ γ g⁻¹ * ρ γ M from MonoidHom.map_mul (ρ γ) g⁻¹ M, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro c _
    rw [h_unitary_elem g a c]
  have hME2 : ∀ (g : G) (b a : Fin (dims γ)),
      (ρ γ (g * N)) b a = ∑ d : Fin (dims γ), (ρ γ g) b d * (ρ γ N) d a := by
    intro g b a
    rw [show ρ γ (g * N) = ρ γ g * ρ γ N from MonoidHom.map_mul (ρ γ) g N, Matrix.mul_apply]
  have hchar4 : ∀ (g : G),
      repCharacter (ρ γ) (g⁻¹ * M * g * N) =
        ∑ a : Fin (dims γ), ∑ b : Fin (dims γ), ∑ c : Fin (dims γ), ∑ d : Fin (dims γ),
          conj ((ρ γ g) c a) * (ρ γ M) c b * (ρ γ g) b d * (ρ γ N) d a := by
    intro g
    rw [hchar]
    rw [show (∑ a : Fin (dims γ), ∑ b : Fin (dims γ),
          (ρ γ (g⁻¹ * M)) a b * (ρ γ (g * N)) b a) =
        ∑ a : Fin (dims γ), ∑ b : Fin (dims γ),
          (∑ c : Fin (dims γ), conj ((ρ γ g) c a) * (ρ γ M) c b) *
          (∑ d : Fin (dims γ), (ρ γ g) b d * (ρ γ N) d a) from by
      congr 1 with a
      congr 1 with b
      rw [hME1, hME2]]
    simp only [Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    ring
  have hInt_term : ∀ (a b c d : Fin (dims γ)),
      Integrable (fun g =>
        conj ((ρ γ g) c a) * (ρ γ M) c b * (ρ γ g) b d * (ρ γ N) d a) μ := by
    intro a b c d
    have h_gdep : Integrable (fun g => (ρ γ g) b d * conj ((ρ γ g) c a)) μ :=
      hInt γ γ b d c a
    refine (h_gdep.smul ((ρ γ M) c b * (ρ γ N) d a)).congr ?_
    exact Filter.Eventually.of_forall (fun g => by
      simp only [Pi.smul_def, smul_eq_mul]
      ring)
  have hInt_d : ∀ (a b c : Fin (dims γ)),
      Integrable (fun g => ∑ d : Fin (dims γ),
        conj ((ρ γ g) c a) * (ρ γ M) c b * (ρ γ g) b d * (ρ γ N) d a) μ :=
    fun a b c => integrable_finsetSum Finset.univ (fun d _ => hInt_term a b c d)
  have hInt_c : ∀ (a b : Fin (dims γ)),
      Integrable (fun g => ∑ c : Fin (dims γ), ∑ d : Fin (dims γ),
        conj ((ρ γ g) c a) * (ρ γ M) c b * (ρ γ g) b d * (ρ γ N) d a) μ :=
    fun a b => integrable_finsetSum Finset.univ (fun c _ => hInt_d a b c)
  have hInt_b : ∀ (a : Fin (dims γ)),
      Integrable (fun g => ∑ b : Fin (dims γ), ∑ c : Fin (dims γ), ∑ d : Fin (dims γ),
        conj ((ρ γ g) c a) * (ρ γ M) c b * (ρ γ g) b d * (ρ γ N) d a) μ :=
    fun a => integrable_finsetSum Finset.univ (fun b _ => hInt_c a b)
  have hInt_sum : Integrable (fun g =>
      ∑ a : Fin (dims γ), ∑ b : Fin (dims γ), ∑ c : Fin (dims γ), ∑ d : Fin (dims γ),
        conj ((ρ γ g) c a) * (ρ γ M) c b * (ρ γ g) b d * (ρ γ N) d a) μ :=
    integrable_finsetSum Finset.univ (fun a _ => hInt_b a)
  exact hInt_sum.congr (Filter.Eventually.of_forall (fun g => (hchar4 g).symm))

#print axioms char_conjugation_integrable

/-- **2-site Lüscher cascade with separable kernel (Step 3c, L=2 cascade).**

For irreducible unitary representations of a compact group with normalized Haar
measure, and arbitrary non-negative coefficients `F : ι → ι → ℝ` with `F s t ≥ 0`,
the 2-site cascade with two temporal plaquettes (each with W and V parts) evaluates
to a separable kernel:

    ∫∫ ∑_{s,t} F(s,t) · χ_s(g₀·V₀·g₁⁻¹·W₀⁻¹) · χ_t(g₁·V₁·g₀⁻¹·W₁⁻¹) dg₁ dg₀
      = ∑_s F(s,s) · (1/d_s)² · χ_s(W₁⁻¹·W₀⁻¹) · χ_s(V₀·V₁)

The kernel `K(W,V) = Σ_s (F(s,s)·(1/d_s)²) · χ_s(W₁⁻¹·W₀⁻¹) · χ_s(V₀·V₁)` is
separable with non-negative coefficients `F(s,s)·(1/d_s)² ≥ 0` (since `F(s,s) ≥ 0`
and `(1/d_s)² > 0`), matching `character_kernel_integral_nonneg` (step 3d).

Proof: (1) integrate out `g₁` via `luscher_key_identity` (Schur orthogonality forces
`t = s`, giving `(1/d_s)·χ_s((V₁·g₀⁻¹·W₁⁻¹)·(W₀⁻¹·g₀·V₀))`); (2) cyclically
rewrite the character to `g₀⁻¹·(W₁⁻¹·W₀⁻¹)·g₀·(V₀·V₁)` form; (3) integrate out
`g₀` via `conjugation_integral` (giving `(1/d_s)·χ_s(W₁⁻¹·W₀⁻¹)·χ_s(V₀·V₁)`).
The combined coefficient is `(1/d_s)² > 0`. 0 sorries, 0 new axioms. -/
lemma luscher_2site_cascade_separable
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (F : ι → ι → ℝ) (hF : ∀ s t, 0 ≤ F s t)
    (W₀ W₁ V₀ V₁ : G) :
    ∫ g₀, ∫ g₁,
      ∑ s, ∑ t, (F s t : ℂ) *
        (repCharacter (ρ s) (g₀ * V₀ * g₁⁻¹ * W₀⁻¹) *
         repCharacter (ρ t) (g₁ * V₁ * g₀⁻¹ * W₁⁻¹)) ∂μ ∂μ =
    ∑ s, (F s s : ℂ) * ((1 / dims s : ℂ)^2 *
      repCharacter (ρ s) (W₁⁻¹ * W₀⁻¹) * repCharacter (ρ s) (V₀ * V₁)) := by
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  -- Helper: χ(a * b) = χ(b * a) by trace_mul_comm
  have hmul_comm : ∀ (i : ι) (a b : G),
      repCharacter (ρ i) (a * b) = repCharacter (ρ i) (b * a) := by
    intro i a b
    show Matrix.trace (ρ i (a * b)) = Matrix.trace (ρ i (b * a))
    rw [MonoidHom.map_mul, MonoidHom.map_mul, Matrix.trace_mul_comm]
  -- Helper: cyclic shift of first plaquette
  have hcyc₁ : ∀ (s : ι) (g₀ g₁ : G),
      repCharacter (ρ s) (g₀ * V₀ * g₁⁻¹ * W₀⁻¹) =
      repCharacter (ρ s) (g₁⁻¹ * (W₀⁻¹ * g₀ * V₀)) := by
    intro s g₀ g₁
    rw [repCharacter_cyclic (ρ s) (g₀ * V₀) g₁⁻¹ W₀⁻¹]
    simp only [mul_assoc]
  -- Helper: cyclic shift to conjugation form
  have hcyc₂ : ∀ (s : ι) (g₀ : G),
      repCharacter (ρ s) ((V₁ * g₀⁻¹ * W₁⁻¹) * (W₀⁻¹ * g₀ * V₀)) =
      repCharacter (ρ s) (g₀⁻¹ * (W₁⁻¹ * W₀⁻¹) * g₀ * (V₀ * V₁)) := by
    intro s g₀
    rw [hmul_comm s (V₁ * g₀⁻¹ * W₁⁻¹) (W₀⁻¹ * g₀ * V₀)]
    rw [show (W₀⁻¹ * g₀ * V₀) * (V₁ * g₀⁻¹ * W₁⁻¹) = (W₀⁻¹ * g₀ * V₀ * V₁) * (g₀⁻¹ * W₁⁻¹) from by
      simp only [mul_assoc]]
    rw [hmul_comm s (W₀⁻¹ * g₀ * V₀ * V₁) (g₀⁻¹ * W₁⁻¹)]
    simp only [mul_assoc]
  -- Helper: integrability of χ_s(g⁻¹ * M * g * N) w.r.t. g
  have hInt_char_conj : ∀ (s : ι) (M N : G),
      Integrable (fun g => repCharacter (ρ s) (g⁻¹ * M * g * N)) μ :=
    fun s M N => char_conjugation_integrable μ ι dims hDims ρ hU hIrr s M N
  -- Integrability of each (s,t) term w.r.t. g₁
  have hInt_char : ∀ (g₀ : G) (s t : ι),
      Integrable (fun g₁ =>
        repCharacter (ρ s) (g₀ * V₀ * g₁⁻¹ * W₀⁻¹) *
        repCharacter (ρ t) (g₁ * V₁ * g₀⁻¹ * W₁⁻¹)) μ := by
    intro g₀ s t
    have h := char_product_integrable μ ι dims hDims ρ hU hIrr s t
      (W₀⁻¹ * g₀ * V₀) (V₁ * g₀⁻¹ * W₁⁻¹)
    refine h.congr (Filter.Eventually.of_forall (fun g₁ => by
      have heq := (hmul_comm s (W₀⁻¹ * g₀ * V₀) g₁⁻¹).trans (hcyc₁ s g₀ g₁).symm
      simp only [heq]
      simp only [mul_assoc]))
  -- Integrability of each (s,t) term with F coefficient w.r.t. g₁
  have hInt_term_st : ∀ (g₀ : G) (s t : ι),
      Integrable (fun g₁ =>
        (F s t : ℂ) *
        (repCharacter (ρ s) (g₀ * V₀ * g₁⁻¹ * W₀⁻¹) *
         repCharacter (ρ t) (g₁ * V₁ * g₀⁻¹ * W₁⁻¹))) μ := by
    intro g₀ s t
    exact ((hInt_char g₀ s t).smul (F s t : ℂ)).congr
      (Filter.Eventually.of_forall (fun g₁ => by
        simp only [Pi.smul_def, smul_eq_mul]))
  have hInt_t : ∀ (g₀ : G) (s : ι),
      Integrable (fun g₁ =>
        ∑ t : ι, (F s t : ℂ) *
        (repCharacter (ρ s) (g₀ * V₀ * g₁⁻¹ * W₀⁻¹) *
         repCharacter (ρ t) (g₁ * V₁ * g₀⁻¹ * W₁⁻¹))) μ :=
    fun g₀ s => integrable_finsetSum Finset.univ (fun t _ => hInt_term_st g₀ s t)
  -- Inner integral via luscher_key_identity
  have hInner : ∀ (g₀ : G) (s t : ι),
      ∫ g₁, repCharacter (ρ s) (g₀ * V₀ * g₁⁻¹ * W₀⁻¹) *
        repCharacter (ρ t) (g₁ * V₁ * g₀⁻¹ * W₁⁻¹) ∂μ =
      if t = s then (1 / dims t : ℂ) * repCharacter (ρ t) ((V₁ * g₀⁻¹ * W₁⁻¹) * (W₀⁻¹ * g₀ * V₀)) else 0 := by
    intro g₀ s t
    rw [show (∫ g₁, repCharacter (ρ s) (g₀ * V₀ * g₁⁻¹ * W₀⁻¹) *
          repCharacter (ρ t) (g₁ * V₁ * g₀⁻¹ * W₁⁻¹) ∂μ) =
        ∫ g₁, repCharacter (ρ t) (g₁ * (V₁ * g₀⁻¹ * W₁⁻¹)) *
          repCharacter (ρ s) (g₁⁻¹ * (W₀⁻¹ * g₀ * V₀)) ∂μ from by
      congr 1 with g₁
      rw [hcyc₁ s g₀ g₁]
      simp only [mul_assoc]
      ring]
    rw [luscher_key_identity μ ι dims hDims ρ hU hIrr t s (V₁ * g₀⁻¹ * W₁⁻¹) (W₀⁻¹ * g₀ * V₀)]
  -- Inner integral with constants pulled out
  have hInner_full : ∀ (g₀ : G) (s t : ι),
      ∫ g₁, (F s t : ℂ) *
        (repCharacter (ρ s) (g₀ * V₀ * g₁⁻¹ * W₀⁻¹) *
         repCharacter (ρ t) (g₁ * V₁ * g₀⁻¹ * W₁⁻¹)) ∂μ =
      (F s t : ℂ) *
        (if t = s then (1 / dims t : ℂ) * repCharacter (ρ t) ((V₁ * g₀⁻¹ * W₁⁻¹) * (W₀⁻¹ * g₀ * V₀)) else 0) := by
    intro g₀ s t
    rw [integral_const_mul, hInner g₀ s t]
  -- Exchange s sum with g₁ integral
  rw [show (∫ g₀, ∫ g₁,
        (∑ s : ι, ∑ t : ι, (F s t : ℂ) *
          (repCharacter (ρ s) (g₀ * V₀ * g₁⁻¹ * W₀⁻¹) *
           repCharacter (ρ t) (g₁ * V₁ * g₀⁻¹ * W₁⁻¹))) ∂μ ∂μ) =
      ∫ g₀, ∑ s : ι, ∫ g₁,
        (∑ t : ι, (F s t : ℂ) *
          (repCharacter (ρ s) (g₀ * V₀ * g₁⁻¹ * W₀⁻¹) *
           repCharacter (ρ t) (g₁ * V₁ * g₀⁻¹ * W₁⁻¹))) ∂μ ∂μ from by
    congr 1 with g₀
    rw [integral_finsetSum Finset.univ (fun s _ => hInt_t g₀ s)]]
  -- Exchange t sum with g₁ integral
  rw [show (∫ g₀, ∑ s : ι, ∫ g₁,
        (∑ t : ι, (F s t : ℂ) *
          (repCharacter (ρ s) (g₀ * V₀ * g₁⁻¹ * W₀⁻¹) *
           repCharacter (ρ t) (g₁ * V₁ * g₀⁻¹ * W₁⁻¹))) ∂μ ∂μ) =
      ∫ g₀, ∑ s : ι, ∑ t : ι, ∫ g₁,
        ((F s t : ℂ) *
          (repCharacter (ρ s) (g₀ * V₀ * g₁⁻¹ * W₀⁻¹) *
           repCharacter (ρ t) (g₁ * V₁ * g₀⁻¹ * W₁⁻¹))) ∂μ ∂μ from by
    congr 1 with g₀
    apply Finset.sum_congr rfl
    intro s _
    rw [integral_finsetSum Finset.univ (fun t _ => hInt_term_st g₀ s t)]]
  -- Apply hInner_full to each inner integral
  rw [show (∫ g₀, ∑ s : ι, ∑ t : ι, ∫ g₁,
        ((F s t : ℂ) *
          (repCharacter (ρ s) (g₀ * V₀ * g₁⁻¹ * W₀⁻¹) *
           repCharacter (ρ t) (g₁ * V₁ * g₀⁻¹ * W₁⁻¹))) ∂μ ∂μ) =
      ∫ g₀, ∑ s : ι, ∑ t : ι,
        (F s t : ℂ) *
        (if t = s then (1 / dims t : ℂ) * repCharacter (ρ t) ((V₁ * g₀⁻¹ * W₁⁻¹) * (W₀⁻¹ * g₀ * V₀)) else 0) ∂μ from by
    congr 1 with g₀
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    exact hInner_full g₀ s t]
  -- Collapse the if and simplify
  rw [show (∫ g₀, ∑ s : ι, ∑ t : ι,
        (F s t : ℂ) *
        (if t = s then (1 / dims t : ℂ) * repCharacter (ρ t) ((V₁ * g₀⁻¹ * W₁⁻¹) * (W₀⁻¹ * g₀ * V₀)) else 0) ∂μ) =
      ∫ g₀, ∑ s : ι, (F s s : ℂ) *
        ((1 / dims s : ℂ) * repCharacter (ρ s) ((V₁ * g₀⁻¹ * W₁⁻¹) * (W₀⁻¹ * g₀ * V₀))) ∂μ from by
    congr 1 with g₀
    apply Finset.sum_congr rfl
    intro s _
    have key : ∑ t : ι, (F s t : ℂ) *
        (if t = s then (1 / dims t : ℂ) * repCharacter (ρ t) ((V₁ * g₀⁻¹ * W₁⁻¹) * (W₀⁻¹ * g₀ * V₀)) else 0) =
      (F s s : ℂ) *
        (if s = s then (1 / dims s : ℂ) * repCharacter (ρ s) ((V₁ * g₀⁻¹ * W₁⁻¹) * (W₀⁻¹ * g₀ * V₀)) else 0) := by
      refine Finset.sum_eq_single s ?_ ?_
      · intro t _ hne
        rw [if_neg (fun h => hne h)]
        ring
      · intro h; exact absurd (Finset.mem_univ s) h
    rw [key, if_pos rfl]]
  -- Rewrite character using hcyc₂
  rw [show (∫ g₀, ∑ s : ι, (F s s : ℂ) *
        ((1 / dims s : ℂ) * repCharacter (ρ s) ((V₁ * g₀⁻¹ * W₁⁻¹) * (W₀⁻¹ * g₀ * V₀))) ∂μ) =
      ∫ g₀, ∑ s : ι, (F s s : ℂ) *
        ((1 / dims s : ℂ) * repCharacter (ρ s) (g₀⁻¹ * (W₁⁻¹ * W₀⁻¹) * g₀ * (V₀ * V₁))) ∂μ from by
    congr 1 with g₀
    apply Finset.sum_congr rfl
    intro s _
    rw [hcyc₂ s g₀]]
  -- Integrability for g₀ integral exchange
  have hInt_g0 : ∀ (s : ι),
      Integrable (fun g₀ => (F s s : ℂ) * ((1 / dims s : ℂ) *
        repCharacter (ρ s) (g₀⁻¹ * (W₁⁻¹ * W₀⁻¹) * g₀ * (V₀ * V₁)))) μ := by
    intro s
    have h := hInt_char_conj s (W₁⁻¹ * W₀⁻¹) (V₀ * V₁)
    exact ((h.smul (1 / dims s : ℂ)).smul (F s s : ℂ)).congr
      (Filter.Eventually.of_forall (fun g₀ => by
        simp only [Pi.smul_def, smul_eq_mul]))
  -- Exchange sum with g₀ integral
  rw [integral_finsetSum Finset.univ (fun s _ => hInt_g0 s)]
  -- Apply conjugation_integral to each term
  apply Finset.sum_congr rfl
  intro s _
  rw [show (∫ g₀, (F s s : ℂ) * ((1 / dims s : ℂ) *
        repCharacter (ρ s) (g₀⁻¹ * (W₁⁻¹ * W₀⁻¹) * g₀ * (V₀ * V₁))) ∂μ) =
      (F s s : ℂ) * ((1 / dims s : ℂ) *
        ((1 / dims s : ℂ) * repCharacter (ρ s) (W₁⁻¹ * W₀⁻¹) * repCharacter (ρ s) (V₀ * V₁))) from by
    rw [integral_const_mul, integral_const_mul,
        conjugation_integral μ ι dims hDims ρ hU hIrr s (W₁⁻¹ * W₀⁻¹) (V₀ * V₁)]]
  push_cast
  ring

#print axioms luscher_2site_cascade_separable

