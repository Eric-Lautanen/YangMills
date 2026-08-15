/-
# Peter-Weyl: Triple Product Character Matrix Integrals
-/

import YangMills.Proofs.PeterWeyl.Separable

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open Finset
open Matrix
open MeasureTheory
open scoped ComplexConjugate

namespace YangMills

set_option maxHeartbeats 1000000 in
/-- **Triple product integral evaluation.** For irreducible unitary representations
`ρ_s, ρ_t, ρ_u` of a compact group with normalized Haar measure μ, the integral
`∫ χ_s(g) · (ρ_t g)_{ij} · conj((ρ_u g)_{kl}) dμ(g)` equals
`(1/dims u) · ∑_a cgME(s,t,u,a,i,k) · conj(cgME(s,t,u,a,j,l))`.

This is a positive-semidefinite Gram matrix in the coefficients (key for reflection
positivity). Proof: expand χ_s = ∑_a (ρ_s)_{aa} (trace), apply CG decomposition
`hcgME_decomp` to each `(ρ_s)_{aa} · (ρ_t)_{ij}`, exchange sums with integral
(Fubini), apply Schur orthogonality (`characterOrthogonality`), simplify.
0 sorries, 0 custom axioms. -/
lemma triple_product_character_matrix_integral
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (cgME : ∀ (s t ν : ι), Fin (dims s) → Fin (dims t) → Fin (dims ν) → ℂ)
    (hcgME_decomp : ∀ (s t : ι) (g : G) (a b : Fin (dims s)) (i j : Fin (dims t)),
        (ρ s g) a b * (ρ t g) i j =
        ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
          cgME s t ν a i p * (ρ ν g) p q * conj (cgME s t ν b j q))
    (s t u : ι) (i j : Fin (dims t)) (k l : Fin (dims u)) :
    ∫ g, repCharacter (ρ s) g * (ρ t g) i j * conj ((ρ u g) k l) ∂μ =
      (1 / dims u : ℂ) * ∑ a : Fin (dims s),
        cgME s t u a i k * conj (cgME s t u a j l) := by
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  have hchar : ∀ (g : G),
      repCharacter (ρ s) g = ∑ a : Fin (dims s), (ρ s g) a a := by
    intro g; simp [repCharacter, Matrix.trace]
  have hpt : ∀ (g : G),
      repCharacter (ρ s) g * (ρ t g) i j * conj ((ρ u g) k l) =
        ∑ a : Fin (dims s), ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
          (cgME s t ν a i p * conj (cgME s t ν a j q)) * ((ρ ν g) p q * conj ((ρ u g) k l)) := by
    intro g
    rw [hchar g, mul_assoc, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [← mul_assoc, hcgME_decomp s t g a a i j, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ν _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [show (∫ g, repCharacter (ρ s) g * (ρ t g) i j * conj ((ρ u g) k l) ∂μ) =
        ∫ g, (∑ a : Fin (dims s), ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
          (cgME s t ν a i p * conj (cgME s t ν a j q)) * ((ρ ν g) p q * conj ((ρ u g) k l))) ∂μ from by
    congr 1 with g; exact hpt g]
  -- Per-term integrability
  have hInt_term : ∀ (a : Fin (dims s)) (ν : ι) (p : Fin (dims ν)) (q : Fin (dims ν)),
      Integrable (fun g => (cgME s t ν a i p * conj (cgME s t ν a j q)) *
        ((ρ ν g) p q * conj ((ρ u g) k l))) μ := by
    intro a ν p q
    exact Integrable.smul (cgME s t ν a i p * conj (cgME s t ν a j q)) (hInt ν u p q k l)
  have hInt_q : ∀ (a : Fin (dims s)) (ν : ι) (p : Fin (dims ν)),
      Integrable (fun g => ∑ q : Fin (dims ν),
        (cgME s t ν a i p * conj (cgME s t ν a j q)) *
        ((ρ ν g) p q * conj ((ρ u g) k l))) μ := by
    intro a ν p; exact integrable_finsetSum Finset.univ (fun q _ => hInt_term a ν p q)
  have hInt_p : ∀ (a : Fin (dims s)) (ν : ι),
      Integrable (fun g => ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
        (cgME s t ν a i p * conj (cgME s t ν a j q)) *
        ((ρ ν g) p q * conj ((ρ u g) k l))) μ := by
    intro a ν; exact integrable_finsetSum Finset.univ (fun p _ => hInt_q a ν p)
  have hInt_ν : ∀ (a : Fin (dims s)),
      Integrable (fun g => ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
        (cgME s t ν a i p * conj (cgME s t ν a j q)) *
        ((ρ ν g) p q * conj ((ρ u g) k l))) μ := by
    intro a; exact integrable_finsetSum Finset.univ (fun ν _ => hInt_p a ν)
  -- Exchange sums with integral (4 levels)
  rw [integral_finsetSum Finset.univ (fun a _ => hInt_ν a)]
  rw [Finset.sum_congr rfl (fun a _ => integral_finsetSum Finset.univ (fun ν _ => hInt_p a ν))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl
      (fun ν _ => integral_finsetSum Finset.univ (fun p _ => hInt_q a ν p)))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun ν _ =>
      Finset.sum_congr rfl (fun p _ => integral_finsetSum Finset.univ
        (fun q _ => hInt_term a ν p q))))]
  -- For ν ≠ u, each integral is 0 (pull constant + Schur offdiag)
  have hν_ne_zero : ∀ (a : Fin (dims s)) (ν : ι), ν ≠ u →
      (∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
        ∫ g, (cgME s t ν a i p * conj (cgME s t ν a j q)) *
          ((ρ ν g) p q * conj ((ρ u g) k l)) ∂μ) = 0 := by
    intro a ν hν
    refine Finset.sum_eq_zero (fun p _ => ?_)
    refine Finset.sum_eq_zero (fun q _ => ?_)
    rw [integral_const_mul, hSchur_offdiag ν u p q k l hν]
    simp
  -- Collapse the ν sum: only ν = u contributes
  have hν_collapse : ∀ (a : Fin (dims s)),
      (∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
        ∫ g, (cgME s t ν a i p * conj (cgME s t ν a j q)) *
          ((ρ ν g) p q * conj ((ρ u g) k l)) ∂μ) =
      (∑ p : Fin (dims u), ∑ q : Fin (dims u),
        ∫ g, (cgME s t u a i p * conj (cgME s t u a j q)) *
          ((ρ u g) p q * conj ((ρ u g) k l)) ∂μ) := by
    intro a
    exact Finset.sum_eq_single u (fun ν _ hν => hν_ne_zero a ν hν)
        (fun h => (h (Finset.mem_univ _)).elim)
  rw [Finset.sum_congr rfl (fun a _ => hν_collapse a)]
  -- Evaluate each integral (ν = u case: pull constant + Schur diag)
  have hInt_eval_u : ∀ (a : Fin (dims s)) (p : Fin (dims u)) (q : Fin (dims u)),
      ∫ g, (cgME s t u a i p * conj (cgME s t u a j q)) *
        ((ρ u g) p q * conj ((ρ u g) k l)) ∂μ =
        (cgME s t u a i p * conj (cgME s t u a j q)) *
        (if p = k ∧ q = l then (1 / dims u : ℂ) else 0) := by
    intro a p q
    rw [integral_const_mul, hSchur_diag]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun q _ => hInt_eval_u a p q)))]
  -- Collapse p, q sums for each a
  have hpq_collapse : ∀ (a : Fin (dims s)),
      (∑ p : Fin (dims u), ∑ q : Fin (dims u),
        (cgME s t u a i p * conj (cgME s t u a j q)) *
        (if p = k ∧ q = l then (1 / dims u : ℂ) else 0)) =
      (cgME s t u a i k * conj (cgME s t u a j l)) * (1 / dims u : ℂ) := by
    intro a
    rw [Finset.sum_eq_single k (fun p _ hp => Finset.sum_eq_zero (fun q _ => by
        simp [hp])) (fun h => (h (Finset.mem_univ _)).elim)]
    simp only [eq_self_iff_true, true_and]
    rw [Finset.sum_eq_single l (fun q _ hq => by simp [hq])
        (fun h => (h (Finset.mem_univ _)).elim)]
    simp only [eq_self_iff_true, if_true]
  rw [Finset.sum_congr rfl (fun a _ => hpq_collapse a)]
  -- Factor out 1/dims u
  rw [← Finset.sum_mul, mul_comm]

#print axioms triple_product_character_matrix_integral

set_option maxHeartbeats 1000000 in
/-- **Generalized triple-product integral for ι × Λ.** For `s ∈ ι` (finite, from
the character expansion) and `t, u ∈ Λ` (countable, from the L² expansion of the
arbitrary test function `A_w`), the integral
`∫ χ_s(g) · (ρΛ_t g)_{ij} · conj((ρΛ_u g)_{kl}) dμ(g)` equals
`(1/dimsΛ u) · ∑_a cgMEΛ s t u a i k · conj(cgMEΛ s t u a j l)`.

This is a PSD Gram matrix in the CG coefficients (key for reflection positivity
step 3).  Proof: expand χ_s = trace, apply CG decomposition `hcgMEΛ_decomp` for
ι × Λ (finite support), exchange sums with integral (Fubini for finite sums),
apply Schur orthogonality for Λ (`hSchurΛ_diag`/`hSchurΛ_offdiag`), simplify.
Uses the extended `peterWeyl_clebschGordan_plaquette` axiom (Parts 3–4). -/
lemma triple_product_character_matrix_integral_Λ
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (Λ : Type) [Encodable Λ]
    (dimsΛ : Λ → ℕ) (hDimsΛ : ∀ ℓ, 0 < dimsΛ ℓ)
    (ρΛ : ∀ ℓ, G →* Matrix (Fin (dimsΛ ℓ)) (Fin (dimsΛ ℓ)) ℂ)
    (cgMEΛ : ∀ (s : ι) (t ν : Λ), Fin (dims s) → Fin (dimsΛ t) → Fin (dimsΛ ν) → ℂ)
    (hcgMEΛ_support : ∀ (s : ι) (t : Λ), Finset Λ)
    (hcgMEΛ_decomp : ∀ (s : ι) (t : Λ) (g : G) (a b : Fin (dims s)) (i j : Fin (dimsΛ t)),
        (ρ s g) a b * (ρΛ t g) i j =
        ∑ ν ∈ hcgMEΛ_support s t, ∑ p : Fin (dimsΛ ν), ∑ q : Fin (dimsΛ ν),
          cgMEΛ s t ν a i p * (ρΛ ν g) p q * conj (cgMEΛ s t ν b j q))
    (hcgMEΛ_support_zero : ∀ (s : ι) (t ν : Λ), ν ∉ hcgMEΛ_support s t →
        ∀ (a : Fin (dims s)) (i : Fin (dimsΛ t)) (p : Fin (dimsΛ ν)),
          cgMEΛ s t ν a i p = 0)
    (hSchurΛ_int : ∀ (ν μ₂ : Λ) (p : Fin (dimsΛ ν)) (q : Fin (dimsΛ ν))
        (k : Fin (dimsΛ μ₂)) (l : Fin (dimsΛ μ₂)),
      Integrable (fun g => (ρΛ ν g) p q * conj ((ρΛ μ₂ g) k l)) μ)
    (hSchurΛ_diag : ∀ (ν : Λ) (p q k l : Fin (dimsΛ ν)),
      ∫ g, (ρΛ ν g) p q * conj ((ρΛ ν g) k l) ∂μ =
        if p = k ∧ q = l then (1 / dimsΛ ν : ℂ) else 0)
    (hSchurΛ_offdiag : ∀ (ν μ₂ : Λ) (p q : Fin (dimsΛ ν)) (k l : Fin (dimsΛ μ₂)),
      ν ≠ μ₂ → ∫ g, (ρΛ ν g) p q * conj ((ρΛ μ₂ g) k l) ∂μ = 0)
    (s : ι) (t u : Λ) (i j : Fin (dimsΛ t)) (k l : Fin (dimsΛ u)) :
    ∫ g, repCharacter (ρ s) g * (ρΛ t g) i j * conj ((ρΛ u g) k l) ∂μ =
      (1 / dimsΛ u : ℂ) * ∑ a : Fin (dims s),
        cgMEΛ s t u a i k * conj (cgMEΛ s t u a j l) := by
  classical
  have hchar : ∀ (g : G),
      repCharacter (ρ s) g = ∑ a : Fin (dims s), (ρ s g) a a := by
    intro g; simp [repCharacter, Matrix.trace]
  have hpt : ∀ (g : G),
      repCharacter (ρ s) g * (ρΛ t g) i j * conj ((ρΛ u g) k l) =
        ∑ a : Fin (dims s), ∑ ν ∈ hcgMEΛ_support s t,
          ∑ p : Fin (dimsΛ ν), ∑ q : Fin (dimsΛ ν),
            (cgMEΛ s t ν a i p * conj (cgMEΛ s t ν a j q)) *
            ((ρΛ ν g) p q * conj ((ρΛ u g) k l)) := by
    intro g
    rw [hchar g, mul_assoc, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [← mul_assoc, hcgMEΛ_decomp s t g a a i j, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ν _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [show (∫ g, repCharacter (ρ s) g * (ρΛ t g) i j * conj ((ρΛ u g) k l) ∂μ) =
        ∫ g, (∑ a : Fin (dims s), ∑ ν ∈ hcgMEΛ_support s t,
          ∑ p : Fin (dimsΛ ν), ∑ q : Fin (dimsΛ ν),
            (cgMEΛ s t ν a i p * conj (cgMEΛ s t ν a j q)) *
            ((ρΛ ν g) p q * conj ((ρΛ u g) k l))) ∂μ from by
    congr 1 with g; exact hpt g]
  -- Per-term integrability
  have hInt_term : ∀ (a : Fin (dims s)) (ν : Λ) (p : Fin (dimsΛ ν)) (q : Fin (dimsΛ ν)),
      Integrable (fun g => (cgMEΛ s t ν a i p * conj (cgMEΛ s t ν a j q)) *
        ((ρΛ ν g) p q * conj ((ρΛ u g) k l))) μ := by
    intro a ν p q
    exact Integrable.smul (cgMEΛ s t ν a i p * conj (cgMEΛ s t ν a j q)) (hSchurΛ_int ν u p q k l)
  have hInt_q : ∀ (a : Fin (dims s)) (ν : Λ) (p : Fin (dimsΛ ν)),
      Integrable (fun g => ∑ q : Fin (dimsΛ ν),
        (cgMEΛ s t ν a i p * conj (cgMEΛ s t ν a j q)) *
        ((ρΛ ν g) p q * conj ((ρΛ u g) k l))) μ := by
    intro a ν p; exact integrable_finsetSum Finset.univ (fun q _ => hInt_term a ν p q)
  have hInt_p : ∀ (a : Fin (dims s)) (ν : Λ),
      Integrable (fun g => ∑ p : Fin (dimsΛ ν), ∑ q : Fin (dimsΛ ν),
        (cgMEΛ s t ν a i p * conj (cgMEΛ s t ν a j q)) *
        ((ρΛ ν g) p q * conj ((ρΛ u g) k l))) μ := by
    intro a ν; exact integrable_finsetSum Finset.univ (fun p _ => hInt_q a ν p)
  have hInt_ν : ∀ (a : Fin (dims s)),
      Integrable (fun g => ∑ ν ∈ hcgMEΛ_support s t, ∑ p : Fin (dimsΛ ν), ∑ q : Fin (dimsΛ ν),
        (cgMEΛ s t ν a i p * conj (cgMEΛ s t ν a j q)) *
        ((ρΛ ν g) p q * conj ((ρΛ u g) k l))) μ := by
    intro a; exact integrable_finsetSum (hcgMEΛ_support s t) (fun ν _ => hInt_p a ν)
  -- Exchange sums with integral
  rw [integral_finsetSum Finset.univ (fun a _ => hInt_ν a)]
  rw [Finset.sum_congr rfl (fun a _ => integral_finsetSum (hcgMEΛ_support s t) (fun ν _ => hInt_p a ν))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun ν _ =>
      integral_finsetSum Finset.univ (fun p _ => hInt_q a ν p)))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun ν _ =>
      Finset.sum_congr rfl (fun p _ => integral_finsetSum Finset.univ
        (fun q _ => hInt_term a ν p q))))]
  -- For ν ≠ u, each integral is 0
  have hν_ne_zero : ∀ (a : Fin (dims s)) (ν : Λ), ν ≠ u →
      (∑ p : Fin (dimsΛ ν), ∑ q : Fin (dimsΛ ν),
        ∫ g, (cgMEΛ s t ν a i p * conj (cgMEΛ s t ν a j q)) *
          ((ρΛ ν g) p q * conj ((ρΛ u g) k l)) ∂μ) = 0 := by
    intro a ν hν
    refine Finset.sum_eq_zero (fun p _ => ?_)
    refine Finset.sum_eq_zero (fun q _ => ?_)
    rw [integral_const_mul, hSchurΛ_offdiag ν u p q k l hν]
    simp
  by_cases hu : u ∈ hcgMEΛ_support s t
  · -- Case: u ∈ support — collapse ν sum to u
    have hν_collapse : ∀ (a : Fin (dims s)),
        (∑ ν ∈ hcgMEΛ_support s t, ∑ p : Fin (dimsΛ ν), ∑ q : Fin (dimsΛ ν),
          ∫ g, (cgMEΛ s t ν a i p * conj (cgMEΛ s t ν a j q)) *
            ((ρΛ ν g) p q * conj ((ρΛ u g) k l)) ∂μ) =
        (∑ p : Fin (dimsΛ u), ∑ q : Fin (dimsΛ u),
          ∫ g, (cgMEΛ s t u a i p * conj (cgMEΛ s t u a j q)) *
            ((ρΛ u g) p q * conj ((ρΛ u g) k l)) ∂μ) := by
      intro a
      exact Finset.sum_eq_single u (fun ν _ hν => hν_ne_zero a ν hν) (fun h => (h hu).elim)
    rw [Finset.sum_congr rfl (fun a _ => hν_collapse a)]
    -- Evaluate each integral (ν = u: pull constant + Schur diag)
    have hInt_eval : ∀ (a : Fin (dims s)) (p : Fin (dimsΛ u)) (q : Fin (dimsΛ u)),
        ∫ g, (cgMEΛ s t u a i p * conj (cgMEΛ s t u a j q)) *
          ((ρΛ u g) p q * conj ((ρΛ u g) k l)) ∂μ =
          (cgMEΛ s t u a i p * conj (cgMEΛ s t u a j q)) *
          (if p = k ∧ q = l then (1 / dimsΛ u : ℂ) else 0) := by
      intro a p q
      rw [integral_const_mul, hSchurΛ_diag]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun p _ =>
        Finset.sum_congr rfl (fun q _ => hInt_eval a p q)))]
    -- Collapse p, q sums
    have hpq_collapse : ∀ (a : Fin (dims s)),
        (∑ p : Fin (dimsΛ u), ∑ q : Fin (dimsΛ u),
          (cgMEΛ s t u a i p * conj (cgMEΛ s t u a j q)) *
          (if p = k ∧ q = l then (1 / dimsΛ u : ℂ) else 0)) =
          (cgMEΛ s t u a i k * conj (cgMEΛ s t u a j l)) * (1 / dimsΛ u : ℂ) := by
      intro a
      rw [Finset.sum_eq_single k (fun p _ hp => Finset.sum_eq_zero (fun q _ => by
          simp [hp])) (fun h => (h (Finset.mem_univ _)).elim)]
      simp only [eq_self_iff_true, true_and]
      rw [Finset.sum_eq_single l (fun q _ hq => by simp [hq])
          (fun h => (h (Finset.mem_univ _)).elim)]
      simp only [eq_self_iff_true, if_true]
    rw [Finset.sum_congr rfl (fun a _ => hpq_collapse a)]
    rw [← Finset.sum_mul, mul_comm]
  · -- Case: u ∉ support — all terms 0, RHS 0 by support_zero
    have hLHS_zero : ∀ (a : Fin (dims s)),
        (∑ ν ∈ hcgMEΛ_support s t, ∑ p : Fin (dimsΛ ν), ∑ q : Fin (dimsΛ ν),
          ∫ g, (cgMEΛ s t ν a i p * conj (cgMEΛ s t ν a j q)) *
            ((ρΛ ν g) p q * conj ((ρΛ u g) k l)) ∂μ) = 0 := by
      intro a
      refine Finset.sum_eq_zero (fun ν hν => ?_)
      have hν_ne : ν ≠ u := fun heq => hu (heq ▸ hν)
      exact hν_ne_zero a ν hν_ne
    rw [Finset.sum_congr rfl (fun a _ => hLHS_zero a)]
    simp
    -- RHS: all cgMEΛ s t u coefficients are 0
    have hRHS : (∑ a : Fin (dims s), cgMEΛ s t u a i k * conj (cgMEΛ s t u a j l) : ℂ) = 0 := by
      refine Finset.sum_eq_zero (fun a _ => ?_)
      rw [hcgMEΛ_support_zero s t u hu a i k, hcgMEΛ_support_zero s t u hu a j l]
      simp
    rw [hRHS]
    simp

#print axioms triple_product_character_matrix_integral_Λ

set_option maxHeartbeats 1000000 in
/-- **Iterated (3-fold) matrix-element Clebsch–Gordan decomposition.**

A product of three matrix elements of the *same* group element `g` (in possibly
different representations `s₁, s₂, s₃`) decomposes as a single sum over one
representation `α`, by applying `hcgME_decomp` twice (first combine `s₁, s₂ → ν`,
then `ν, s₃ → α`):

    (ρ_{s₁} g)_{a₁b₁} · (ρ_{s₂} g)_{a₂b₂} · (ρ_{s₃} g)_{a₃b₃}
      = ∑_ν ∑_{r,s} ∑_α ∑_{p,q}
          cgME s₁ s₂ ν a₁ a₂ r · conj(cgME s₁ s₂ ν b₁ b₂ s) ·
          cgME ν s₃ α r a₃ p · (ρ_α g)_{pq} · conj(cgME ν s₃ α s b₃ q)

The sums are in **natural decomposition order** (intermediate representation `ν`
outermost, final representation `α` innermost), matching the order in which the
two `hcgME_decomp` applications produce them. The intermediate representation `ν`
is **shared** between the row (a-index) and column (b-index) CG coefficients —
the coefficient of `(ρ_α g)_{pq}` is
`∑_ν ∑_{r,s} cgME s₁ s₂ ν a₁ a₂ r · cgME ν s₃ α r a₃ p · conj(cgME s₁ s₂ ν b₁ b₂ s · cgME ν s₃ α s b₃ q)`,
an inner product over the shared `ν` (NOT a product of two independent sums).

This is the matrix-element analogue of `charProduct_finset_decomp` and the key
building block for the **3D single-site Lüscher integral** (Step 2 of the Lüscher
roadmap, §8.11.41–42): in 3D each temporal link `u_t(x)` appears in 3 forward
plaquettes, producing 3 unbarred matrix elements that must be combined into one
before Schur orthogonality can be applied to the single-site integral. 0 sorries,
0 custom axioms (pure algebra from `hcgME_decomp`). -/
lemma cgME_decomp_3fold
    {G : Type*} [Group G]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (cgME : ∀ (s t ν : ι), Fin (dims s) → Fin (dims t) → Fin (dims ν) → ℂ)
    (hcgME_decomp : ∀ (s t : ι) (g : G) (a b : Fin (dims s)) (i j : Fin (dims t)),
        (ρ s g) a b * (ρ t g) i j =
        ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
          cgME s t ν a i p * (ρ ν g) p q * conj (cgME s t ν b j q))
    (s1 s2 s3 : ι) (g : G)
    (a1 b1 : Fin (dims s1)) (a2 b2 : Fin (dims s2)) (a3 b3 : Fin (dims s3)) :
    (ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 * (ρ s3 g) a3 b3 =
    ∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν),
      ∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
        cgME ν s3 α r a3 p * (ρ α g) p q * conj (cgME ν s3 α s b3 q) := by
  -- First CG decomposition: (ρ s1 g)_{a1 b1} * (ρ s2 g)_{a2 b2}, then distribute
  -- the remaining (ρ s3 g)_{a3 b3} into the ν, r, s sums.
  rw [hcgME_decomp s1 s2 g a1 b1 a2 b2]
  simp only [Finset.sum_mul]
  -- Descend into the ν, r, s sums (RHS is in the same ν-outermost order).
  apply Finset.sum_congr rfl
  intro ν _
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  -- Leaf: regroup so (ρ ν g)_{rs} * (ρ s3 g)_{a3 b3} are adjacent, then apply
  -- the second CG decomposition (ν, s₃ → α).
  have hrearr : cgME s1 s2 ν a1 a2 r * (ρ ν g) r s * conj (cgME s1 s2 ν b1 b2 s) *
      (ρ s3 g) a3 b3 =
      cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
      ((ρ ν g) r s * (ρ s3 g) a3 b3) := by ring
  rw [hrearr, hcgME_decomp ν s3 g r s a3 b3]
  -- Distribute the constant (CG coefficients for s₁,s₂) into the α, p, q sums.
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun α _ =>
    Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun q _ => by ring)))

#print axioms cgME_decomp_3fold

set_option maxHeartbeats 1000000 in
/-- **Conjugate of the iterated 3-fold matrix-element CG decomposition.**

The complex conjugate of `cgME_decomp_3fold`: a product of three *conjugated* matrix
elements of the same group element `g` decomposes as a single sum over `α`, with the
intermediate `ν` shared between row and column CG coefficients. This is the barred
(3 backward plaquettes) counterpart needed for the single-site 3D Lüscher integral.

    conj((ρ_{s₁} g)_{a₁b₁}) · conj((ρ_{s₂} g)_{a₂b₂}) · conj((ρ_{s₃} g)_{a₃b₃})
      = ∑_ν ∑_{r,s} ∑_α ∑_{p,q}
          conj(cgME s₁ s₂ ν a₁ a₂ r) · cgME s₁ s₂ ν b₁ b₂ s ·
          conj(cgME ν s₃ α r a₃ p) · conj((ρ_α g)_{pq}) · cgME ν s₃ α s b₃ q

0 sorries, 0 custom axioms (pure algebra: conjugate of `cgME_decomp_3fold`). -/
lemma cgME_decomp_3fold_conj
    {G : Type*} [Group G]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (cgME : ∀ (s t ν : ι), Fin (dims s) → Fin (dims t) → Fin (dims ν) → ℂ)
    (hcgME_decomp : ∀ (s t : ι) (g : G) (a b : Fin (dims s)) (i j : Fin (dims t)),
        (ρ s g) a b * (ρ t g) i j =
        ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
          cgME s t ν a i p * (ρ ν g) p q * conj (cgME s t ν b j q))
    (s1 s2 s3 : ι) (g : G)
    (a1 b1 : Fin (dims s1)) (a2 b2 : Fin (dims s2)) (a3 b3 : Fin (dims s3)) :
    conj ((ρ s1 g) a1 b1) * conj ((ρ s2 g) a2 b2) * conj ((ρ s3 g) a3 b3) =
    ∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν),
      ∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        conj (cgME s1 s2 ν a1 a2 r) * cgME s1 s2 ν b1 b2 s *
        conj (cgME ν s3 α r a3 p) * conj ((ρ α g) p q) * cgME ν s3 α s b3 q := by
  have h := cgME_decomp_3fold ι dims ρ cgME hcgME_decomp s1 s2 s3 g a1 b1 a2 b2 a3 b3
  have hconj_mul : ∀ (a b : ℂ), conj (a * b) = conj a * conj b :=
    fun a b => map_mul (starRingEnd ℂ) a b
  have h := cgME_decomp_3fold ι dims ρ cgME hcgME_decomp s1 s2 s3 g a1 b1 a2 b2 a3 b3
  have hconj_mul : ∀ (a b : ℂ), conj (a * b) = conj a * conj b :=
    fun a b => map_mul (starRingEnd ℂ) a b
  -- Take conj of both sides of h, then normalize with simp.
  have hconj : conj ((ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 * (ρ s3 g) a3 b3) =
      conj (∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν),
        ∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
          cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
          cgME ν s3 α r a3 p * (ρ α g) p q * conj (cgME ν s3 α s b3 q)) := by
    rw [h]
  -- simp pushes conj through products (conj_mul) and sums (map_sum), and
  -- simplifies conj(conj x) = x (conj_conj), normalizing both sides.
  simp at hconj
  exact hconj
#print axioms cgME_decomp_3fold_conj

set_option maxHeartbeats 1000000 in
/-- **Integral of a single matrix element = projection onto trivial representation.**
For a compact group with normalized Haar measure, irreducible unitary representations
`ρ_i`, and a trivial representation `σ_0` (1-dimensional, `ρ_{σ_0}(g) = 1`), the integral
of a single matrix element `∫ (ρ_σ(g))_{rs} dμ` equals `1` if `σ = σ_0` (and `r = s = 0`,
the only index for a 1-dimensional representation) and `0` otherwise (by Schur orthogonality:
the integral of a matrix element of a nontrivial irrep against the trivial character is 0).

This is the key building block for evaluating the time-like triple product integral
`∫ χ_s · (ρ_t)_{ij} · (ρ_u)_{kl} dμ` (triple product WITHOUT conjugation), which arises
in the L² expansion approach to reflection positivity (Lemma 5, Step 4a). -/
lemma integral_matrix_element_trivial_projection
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (σ_0 : ι) (hσ_0_dims : dims σ_0 = 1) (hσ_0_trivial : ∀ g, (ρ σ_0 g) = 1)
    (σ : ι) (r : Fin (dims σ)) (s : Fin (dims σ)) :
    ∫ g, (ρ σ g) r s ∂μ = if σ = σ_0 then (1 : ℂ) else 0 := by
  haveI : NeZero (dims σ_0) := ⟨Nat.ne_of_gt (hDims σ_0)⟩
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  -- Extract (ρ_{σ_0})_{00} = 1 from ρ_{σ_0} = 1 (identity matrix)
  have h00 : ∀ g, (ρ σ_0 g) 0 0 = 1 := by
    intro g; rw [hσ_0_trivial g]; simp [Matrix.one_apply]
  -- Rewrite: ∫ (ρ_σ)_{rs} = ∫ (ρ_σ)_{rs} * conj((ρ_{σ_0})_{00}) (since conj((ρ_{σ_0})_{00}) = 1)
  have hconj : ∀ g, conj ((ρ σ_0 g) 0 0) = 1 := by
    intro g; rw [h00 g]; simp
  rw [show ∫ g, (ρ σ g) r s ∂μ = ∫ g, (ρ σ g) r s * conj ((ρ σ_0 g) 0 0) ∂μ from by
    congr 1 with g; rw [hconj g, mul_one]]
  by_cases h : σ = σ_0
  · -- σ = σ_0: diagonal Schur orthogonality
    subst h
    rw [if_pos rfl]
    rw [hSchur_diag σ r s 0 0]
    -- r, s : Fin (dims σ) with dims σ = 1, so r = s = 0 (only element of Fin 1)
    haveI hsub : Subsingleton (Fin (dims σ)) :=
      hσ_0_dims.symm ▸ (inferInstance : Subsingleton (Fin 1))
    have hr : r = 0 := Subsingleton.elim r 0
    have hs : s = 0 := Subsingleton.elim s 0
    simp [hr, hs, hσ_0_dims]
  · -- σ ≠ σ_0: off-diagonal Schur orthogonality
    rw [if_neg h]
    exact hSchur_offdiag σ σ_0 r s 0 0 h

#print axioms integral_matrix_element_trivial_projection

/-- **Integral of a character = projection onto the trivial representation.**
For a compact group with normalized Haar measure, irreducible unitary representations
`ρ_i`, and a trivial representation `σ_0` (1-dimensional, `ρ_{σ_0}(g) = 1`), the integral
of a character `∫ χ_s(g) dμ(g)` equals `1` if `s = σ_0` (the trivial representation) and
`0` otherwise (by Schur orthogonality: the character of a nontrivial irrep integrates to 0).

This is the key building block for step 4 of the formalization path (§8.11.53):
integrating out temporal interface links collapses the temporal characters to the trivial
representation.  Specifically, `∫ ∏_{l∈L_0_temporal} χ_{w(l)}(g_l) dμ = ∏_l δ_{w(l), σ_0}`,
which forces `w(l) = σ_0` for all temporal links l. -/
lemma integral_repCharacter_trivial
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (σ_0 : ι) (hσ_0_dims : dims σ_0 = 1) (hσ_0_trivial : ∀ g, (ρ σ_0 g) = 1)
    (s : ι) :
    ∫ g, repCharacter (ρ s) g ∂μ = if s = σ_0 then (1 : ℂ) else 0 := by
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  haveI : NeZero (dims σ_0) := ⟨Nat.ne_of_gt (hDims σ_0)⟩
  have h00 : ∀ g, (ρ σ_0 g) 0 0 = 1 := by
    intro g; rw [hσ_0_trivial g]; simp [Matrix.one_apply]
  have hconj00 : ∀ g, conj ((ρ σ_0 g) 0 0) = 1 := by
    intro g; rw [h00 g]; simp
  have hInt_single : ∀ (a : Fin (dims s)), Integrable (fun g => (ρ s g) a a) μ := by
    intro a
    have h := hInt s σ_0 a a 0 0
    have heq : (fun g => (ρ s g) a a * conj ((ρ σ_0 g) 0 0)) = (fun g => (ρ s g) a a) := by
      funext g; rw [hconj00 g, mul_one]
    rw [heq] at h
    exact h
  -- repCharacter (ρ s) g = ∑ a, (ρ s g) a a (by definition: trace = sum of diagonal)
  show ∫ g, (∑ a : Fin (dims s), (ρ s g) a a) ∂μ = if s = σ_0 then (1 : ℂ) else 0
  rw [integral_finsetSum Finset.univ (fun a _ => hInt_single a)]
  have hInt_eval : ∀ (a : Fin (dims s)),
      ∫ g, (ρ s g) a a ∂μ = if s = σ_0 then (1 : ℂ) else 0 := by
    intro a
    exact integral_matrix_element_trivial_projection μ ι dims hDims ρ hU hIrr
      σ_0 hσ_0_dims hσ_0_trivial s a a
  rw [Finset.sum_congr rfl (fun a _ => hInt_eval a)]
  by_cases h : s = σ_0
  · subst h; simp [hσ_0_dims]
  · simp [h]

#print axioms integral_repCharacter_trivial

/-- **Multi-link character integral = product of single-link integrals (Step 4).**
For a compact group `G` with normalized Haar measure `μ`, a finite type `L` of links,
irreducible unitary representations `ρ_i`, and a trivial representation `σ_0`
(1-dimensional, `ρ_{σ_0}(g) = 1`), the integral of a product of characters over the
product measure on `L → G` factors as a product of single-link integrals:

    ∫ ∏_{l ∈ L} χ_{w(l)}(g_l) dμ = ∏_{l ∈ L} (if w(l) = σ_0 then 1 else 0)

This is the multi-link temporal collapse (Step 4 of §8.11.53): integrating out the
temporal interface links forces each temporal character to be the trivial character.
Uses `integral_fintype_prod_eq_prod` (Fubini for finite products) to factor the
integral, then `integral_repCharacter_trivial` for each single-link factor. -/
lemma integral_prod_repCharacter_trivial
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (L : Type) [Fintype L] [DecidableEq L]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (σ_0 : ι) (hσ_0_dims : dims σ_0 = 1) (hσ_0_trivial : ∀ g, (ρ σ_0 g) = 1)
    (w : L → ι) :
    ∫ x : L → G, ∏ l : L, repCharacter (ρ (w l)) (x l) ∂(Measure.pi (fun _ => μ)) =
      ∏ l : L, (if w l = σ_0 then (1 : ℂ) else 0) := by
  -- Factor the integral using Fubini for finite products:
  -- ∫ ∏_l f_l(g_l) d(∏ μ) = ∏_l ∫ f_l(g) dμ
  rw [integral_fintype_prod_eq_prod (fun (l : L) (g : G) => repCharacter (ρ (w l)) g)]
  -- Each single-link integral: ∫ χ_{w(l)}(g) dμ = if w(l) = σ_0 then 1 else 0
  refine Finset.prod_congr rfl (fun l _ => ?_)
  exact integral_repCharacter_trivial μ ι dims hDims ρ hU hIrr σ_0 hσ_0_dims hσ_0_trivial (w l)

#print axioms integral_prod_repCharacter_trivial

set_option maxHeartbeats 1000000 in
/-- **Character times matrix element integral (helper for time-like triple product).**
For irreducible unitary representations `ρ_s, ρ_ν` of a compact group with normalized Haar
measure μ, and a trivial representation `σ_0` (1-dimensional, `ρ_{σ_0}(g) = 1`), the integral
`∫ χ_s(g) · (ρ_ν g)_{pq} dμ(g)` equals
`∑_a ∑_r ∑_{s'} cgME(s,ν,σ_0,a,p,r) · conj(cgME(s,ν,σ_0,a,q,s'))`.

Proof: expand `χ_s = ∑_a (ρ_s)_{aa}` (trace), apply CG decomposition `hcgME_decomp` to each
`(ρ_s)_{aa} · (ρ_ν)_{pq}`, exchange sums with integral (Fubini), evaluate
`∫ (ρ_σ)_{rs'} = if σ = σ_0 then 1 else 0` (by `integral_matrix_element_trivial_projection`),
collapse σ sum (only σ = σ_0 contributes). -/
lemma character_times_matrix_element_integral
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (cgME : ∀ (s t ν : ι), Fin (dims s) → Fin (dims t) → Fin (dims ν) → ℂ)
    (hcgME_decomp : ∀ (s t : ι) (g : G) (a b : Fin (dims s)) (i j : Fin (dims t)),
        (ρ s g) a b * (ρ t g) i j =
        ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
          cgME s t ν a i p * (ρ ν g) p q * conj (cgME s t ν b j q))
    (σ_0 : ι) (hσ_0_dims : dims σ_0 = 1) (hσ_0_trivial : ∀ g, (ρ σ_0 g) = 1)
    (s ν : ι) (p : Fin (dims ν)) (q : Fin (dims ν)) :
    ∫ g, repCharacter (ρ s) g * (ρ ν g) p q ∂μ =
      ∑ a : Fin (dims s), ∑ r : Fin (dims σ_0), ∑ s' : Fin (dims σ_0),
        cgME s ν σ_0 a p r * conj (cgME s ν σ_0 a q s') := by
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  haveI : NeZero (dims σ_0) := ⟨Nat.ne_of_gt (hDims σ_0)⟩
  -- (ρ_{σ_0})_{00} = 1 and conj((ρ_{σ_0})_{00}) = 1
  have h00 : ∀ g, (ρ σ_0 g) 0 0 = 1 := by
    intro g; rw [hσ_0_trivial g]; simp [Matrix.one_apply]
  have hconj00 : ∀ g, conj ((ρ σ_0 g) 0 0) = 1 := by
    intro g; rw [h00 g]; simp
  -- Integrability of single matrix elements via hInt with σ_0
  have hInt_single : ∀ (σ : ι) (r : Fin (dims σ)) (s' : Fin (dims σ)),
      Integrable (fun g => (ρ σ g) r s') μ := by
    intro σ r s'
    have h := hInt σ σ_0 r s' 0 0
    have heq : (fun g => (ρ σ g) r s' * conj ((ρ σ_0 g) 0 0)) = (fun g => (ρ σ g) r s') := by
      funext g; rw [hconj00 g, mul_one]
    rw [heq] at h
    exact h
  -- Pointwise identity: χ_s(g) · (ρ_ν g)_{pq} = ∑_a ∑_σ ∑_r ∑_{s'} (coeff) · (ρ_σ g)_{r,s'}
  have hchar : ∀ g, repCharacter (ρ s) g = ∑ a : Fin (dims s), (ρ s g) a a := by
    intro g; simp [repCharacter, Matrix.trace]
  have hpt : ∀ g, repCharacter (ρ s) g * (ρ ν g) p q =
      ∑ a : Fin (dims s), ∑ σ : ι, ∑ r : Fin (dims σ), ∑ s' : Fin (dims σ),
        (cgME s ν σ a p r * conj (cgME s ν σ a q s')) * (ρ σ g) r s' := by
    intro g
    rw [hchar g, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [hcgME_decomp s ν g a a p q]
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s' _
    ring
  -- Rewrite the integral
  rw [show (∫ g, repCharacter (ρ s) g * (ρ ν g) p q ∂μ) =
        ∫ g, (∑ a : Fin (dims s), ∑ σ : ι, ∑ r : Fin (dims σ), ∑ s' : Fin (dims σ),
          (cgME s ν σ a p r * conj (cgME s ν σ a q s')) * (ρ σ g) r s') ∂μ from by
    congr 1 with g; exact hpt g]
  -- Per-term integrability
  have hInt_term : ∀ (a : Fin (dims s)) (σ : ι) (r : Fin (dims σ)) (s' : Fin (dims σ)),
      Integrable (fun g => (cgME s ν σ a p r * conj (cgME s ν σ a q s')) * (ρ σ g) r s') μ := by
    intro a σ r s'
    exact Integrable.smul (cgME s ν σ a p r * conj (cgME s ν σ a q s')) (hInt_single σ r s')
  have hInt_s' : ∀ (a : Fin (dims s)) (σ : ι) (r : Fin (dims σ)),
      Integrable (fun g => ∑ s' : Fin (dims σ),
        (cgME s ν σ a p r * conj (cgME s ν σ a q s')) * (ρ σ g) r s') μ := by
    intro a σ r; exact integrable_finsetSum Finset.univ (fun s' _ => hInt_term a σ r s')
  have hInt_r : ∀ (a : Fin (dims s)) (σ : ι),
      Integrable (fun g => ∑ r : Fin (dims σ), ∑ s' : Fin (dims σ),
        (cgME s ν σ a p r * conj (cgME s ν σ a q s')) * (ρ σ g) r s') μ := by
    intro a σ; exact integrable_finsetSum Finset.univ (fun r _ => hInt_s' a σ r)
  have hInt_σ : ∀ (a : Fin (dims s)),
      Integrable (fun g => ∑ σ : ι, ∑ r : Fin (dims σ), ∑ s' : Fin (dims σ),
        (cgME s ν σ a p r * conj (cgME s ν σ a q s')) * (ρ σ g) r s') μ := by
    intro a; exact integrable_finsetSum Finset.univ (fun σ _ => hInt_r a σ)
  -- Exchange sums with integral (4 levels)
  rw [integral_finsetSum Finset.univ (fun a _ => hInt_σ a)]
  rw [Finset.sum_congr rfl (fun a _ => integral_finsetSum Finset.univ (fun σ _ => hInt_r a σ))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun σ _ =>
      integral_finsetSum Finset.univ (fun r _ => hInt_s' a σ r)))]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun σ _ =>
      Finset.sum_congr rfl (fun r _ => integral_finsetSum Finset.univ
        (fun s' _ => hInt_term a σ r s'))))]
  -- Evaluate ∫ (ρ_σ)_{r,s'} = if σ = σ_0 then 1 else 0
  have hInt_eval : ∀ (a : Fin (dims s)) (σ : ι) (r : Fin (dims σ)) (s' : Fin (dims σ)),
      ∫ g, (cgME s ν σ a p r * conj (cgME s ν σ a q s')) * (ρ σ g) r s' ∂μ =
        (cgME s ν σ a p r * conj (cgME s ν σ a q s')) * (if σ = σ_0 then (1 : ℂ) else 0) := by
    intro a σ r s'
    rw [integral_const_mul, integral_matrix_element_trivial_projection μ ι dims hDims ρ hU hIrr
      σ_0 hσ_0_dims hσ_0_trivial σ r s']
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun σ _ =>
      Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun s' _ => hInt_eval a σ r s'))))]
  -- Collapse σ sum: only σ = σ_0 contributes
  have hσ_ne_zero : ∀ (a : Fin (dims s)) (σ : ι), σ ≠ σ_0 →
      (∑ r : Fin (dims σ), ∑ s' : Fin (dims σ),
        (cgME s ν σ a p r * conj (cgME s ν σ a q s')) * (if σ = σ_0 then (1 : ℂ) else 0)) = 0 := by
    intro a σ hσ
    refine Finset.sum_eq_zero (fun r _ => ?_)
    refine Finset.sum_eq_zero (fun s' _ => ?_)
    rw [if_neg hσ, mul_zero]
  have hσ_collapse : ∀ (a : Fin (dims s)),
      (∑ σ : ι, ∑ r : Fin (dims σ), ∑ s' : Fin (dims σ),
        (cgME s ν σ a p r * conj (cgME s ν σ a q s')) * (if σ = σ_0 then (1 : ℂ) else 0)) =
      (∑ r : Fin (dims σ_0), ∑ s' : Fin (dims σ_0),
        cgME s ν σ_0 a p r * conj (cgME s ν σ_0 a q s')) := by
    intro a
    rw [Finset.sum_eq_single σ_0 (fun σ _ hσ => hσ_ne_zero a σ hσ)
        (fun h => (h (Finset.mem_univ _)).elim)]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s' _
    rw [if_pos rfl, mul_one]
  rw [Finset.sum_congr rfl (fun a _ => hσ_collapse a)]

#print axioms character_times_matrix_element_integral

set_option maxHeartbeats 1000000 in
/-- **Time-like triple product integral evaluation (Lemma 5, Step 4a key component).**
For irreducible unitary representations `ρ_s, ρ_t, ρ_u` of a compact group with normalized
Haar measure μ, and a trivial representation `σ_0` (1-dimensional, `ρ_{σ_0}(g) = 1`), the
integral `∫ χ_s(g) · (ρ_t g)_{ij} · (ρ_u g)_{kl} dμ(g)` (triple product WITHOUT conjugation,
as arises in the time-like link case of reflection positivity) equals a sum of CG coefficient
products forming a PSD Gram matrix:

    ∑_ν ∑_p ∑_q (cgME(t,u,ν,i,k,p) · conj(cgME(t,u,ν,j,l,q))) ·
      (∑_a ∑_r ∑_{s'} cgME(s,ν,σ_0,a,p,r) · conj(cgME(s,ν,σ_0,a,q,s')))

Proof: apply CG decomposition `hcgME_decomp` to `(ρ_t)_{ij} · (ρ_u)_{kl}`, exchange sums with
integral (Fubini), then evaluate `∫ χ_s · (ρ_ν)_{pq} dμ` using
`character_times_matrix_element_integral` (which uses the double CG decomposition +
`integral_matrix_element_trivial_projection`). The result is a PSD Gram matrix in the
`(i,k)` vs `(j,l)` indices. 0 sorries, 0 new custom axioms. -/
lemma triple_product_character_matrix_integral_timelike
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (cgME : ∀ (s t ν : ι), Fin (dims s) → Fin (dims t) → Fin (dims ν) → ℂ)
    (hcgME_decomp : ∀ (s t : ι) (g : G) (a b : Fin (dims s)) (i j : Fin (dims t)),
        (ρ s g) a b * (ρ t g) i j =
        ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
          cgME s t ν a i p * (ρ ν g) p q * conj (cgME s t ν b j q))
    (σ_0 : ι) (hσ_0_dims : dims σ_0 = 1) (hσ_0_trivial : ∀ g, (ρ σ_0 g) = 1)
    (s t u : ι) (i j : Fin (dims t)) (k l : Fin (dims u)) :
    ∫ g, repCharacter (ρ s) g * (ρ t g) i j * (ρ u g) k l ∂μ =
      ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
        (cgME t u ν i k p * conj (cgME t u ν j l q)) *
        (∑ a : Fin (dims s), ∑ r : Fin (dims σ_0), ∑ s' : Fin (dims σ_0),
          cgME s ν σ_0 a p r * conj (cgME s ν σ_0 a q s')) := by
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  haveI : NeZero (dims σ_0) := ⟨Nat.ne_of_gt (hDims σ_0)⟩
  -- (ρ_{σ_0})_{00} = 1 and conj((ρ_{σ_0})_{00}) = 1
  have h00 : ∀ g, (ρ σ_0 g) 0 0 = 1 := by
    intro g; rw [hσ_0_trivial g]; simp [Matrix.one_apply]
  have hconj00 : ∀ g, conj ((ρ σ_0 g) 0 0) = 1 := by
    intro g; rw [h00 g]; simp
  -- Integrability of single matrix elements via hInt with σ_0
  have hInt_single : ∀ (σ : ι) (r : Fin (dims σ)) (s' : Fin (dims σ)),
      Integrable (fun g => (ρ σ g) r s') μ := by
    intro σ r s'
    have h := hInt σ σ_0 r s' 0 0
    have heq : (fun g => (ρ σ g) r s' * conj ((ρ σ_0 g) 0 0)) = (fun g => (ρ σ g) r s') := by
      funext g; rw [hconj00 g, mul_one]
    rw [heq] at h
    exact h
  -- Character expansion
  have hchar : ∀ g, repCharacter (ρ s) g = ∑ a : Fin (dims s), (ρ s g) a a := by
    intro g; simp [repCharacter, Matrix.trace]
  -- Inner pointwise identity (same as character_times_matrix_element_integral's hpt)
  have hpt_inner : ∀ (ν : ι) (p : Fin (dims ν)) (q : Fin (dims ν)) (g : G),
      repCharacter (ρ s) g * (ρ ν g) p q =
      ∑ a : Fin (dims s), ∑ σ : ι, ∑ r : Fin (dims σ), ∑ s' : Fin (dims σ),
        (cgME s ν σ a p r * conj (cgME s ν σ a q s')) * (ρ σ g) r s' := by
    intro ν p q g
    rw [hchar g, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [hcgME_decomp s ν g a a p q]
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s' _
    ring
  -- Integrability of χ_s(g) · (ρ_ν g)_{pq}
  have hInt_char_me : ∀ (ν : ι) (p : Fin (dims ν)) (q : Fin (dims ν)),
      Integrable (fun g => repCharacter (ρ s) g * (ρ ν g) p q) μ := by
    intro ν p q
    have heq : (fun g => repCharacter (ρ s) g * (ρ ν g) p q) =
        (fun g => ∑ a : Fin (dims s), ∑ σ : ι, ∑ r : Fin (dims σ), ∑ s' : Fin (dims σ),
          (cgME s ν σ a p r * conj (cgME s ν σ a q s')) * (ρ σ g) r s') := by
      funext g; exact hpt_inner ν p q g
    rw [heq]
    apply integrable_finsetSum Finset.univ
    intro a _
    apply integrable_finsetSum Finset.univ
    intro σ _
    apply integrable_finsetSum Finset.univ
    intro r _
    apply integrable_finsetSum Finset.univ
    intro s' _
    exact Integrable.smul (cgME s ν σ a p r * conj (cgME s ν σ a q s')) (hInt_single σ r s')
  -- Outer pointwise identity: first CG decomp
  have hpt_outer : ∀ g, repCharacter (ρ s) g * (ρ t g) i j * (ρ u g) k l =
      ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
        (cgME t u ν i k p * conj (cgME t u ν j l q)) * (repCharacter (ρ s) g * (ρ ν g) p q) := by
    intro g
    rw [mul_assoc, hcgME_decomp t u g i j k l, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ν _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  -- Rewrite the integral
  rw [show (∫ g, repCharacter (ρ s) g * (ρ t g) i j * (ρ u g) k l ∂μ) =
        ∫ g, (∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
          (cgME t u ν i k p * conj (cgME t u ν j l q)) *
            (repCharacter (ρ s) g * (ρ ν g) p q)) ∂μ from by
    congr 1 with g; exact hpt_outer g]
  -- Per-term integrability
  have hInt_term : ∀ (ν : ι) (p : Fin (dims ν)) (q : Fin (dims ν)),
      Integrable (fun g => (cgME t u ν i k p * conj (cgME t u ν j l q)) *
        (repCharacter (ρ s) g * (ρ ν g) p q)) μ := by
    intro ν p q
    exact Integrable.smul (cgME t u ν i k p * conj (cgME t u ν j l q)) (hInt_char_me ν p q)
  have hInt_q : ∀ (ν : ι) (p : Fin (dims ν)),
      Integrable (fun g => ∑ q : Fin (dims ν),
        (cgME t u ν i k p * conj (cgME t u ν j l q)) *
          (repCharacter (ρ s) g * (ρ ν g) p q)) μ := by
    intro ν p; exact integrable_finsetSum Finset.univ (fun q _ => hInt_term ν p q)
  have hInt_p : ∀ (ν : ι),
      Integrable (fun g => ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
        (cgME t u ν i k p * conj (cgME t u ν j l q)) *
          (repCharacter (ρ s) g * (ρ ν g) p q)) μ := by
    intro ν; exact integrable_finsetSum Finset.univ (fun p _ => hInt_q ν p)
  have hInt_ν : Integrable (fun g => ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
        (cgME t u ν i k p * conj (cgME t u ν j l q)) *
          (repCharacter (ρ s) g * (ρ ν g) p q)) μ := by
    exact integrable_finsetSum Finset.univ (fun ν _ => hInt_p ν)
  -- Exchange sums with integral (3 levels)
  rw [integral_finsetSum Finset.univ (fun ν _ => hInt_p ν)]
  rw [Finset.sum_congr rfl (fun ν _ => integral_finsetSum Finset.univ (fun p _ => hInt_q ν p))]
  rw [Finset.sum_congr rfl (fun ν _ => Finset.sum_congr rfl (fun p _ =>
      integral_finsetSum Finset.univ (fun q _ => hInt_term ν p q)))]
  -- Evaluate each integral using integral_const_mul + helper
  have hInt_eval : ∀ (ν : ι) (p : Fin (dims ν)) (q : Fin (dims ν)),
      ∫ g, (cgME t u ν i k p * conj (cgME t u ν j l q)) *
          (repCharacter (ρ s) g * (ρ ν g) p q) ∂μ =
        (cgME t u ν i k p * conj (cgME t u ν j l q)) *
        (∑ a : Fin (dims s), ∑ r : Fin (dims σ_0), ∑ s' : Fin (dims σ_0),
          cgME s ν σ_0 a p r * conj (cgME s ν σ_0 a q s')) := by
    intro ν p q
    rw [integral_const_mul, character_times_matrix_element_integral μ ι dims hDims ρ hU hIrr
      cgME hcgME_decomp σ_0 hσ_0_dims hσ_0_trivial s ν p q]
  rw [Finset.sum_congr rfl (fun ν _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun q _ => hInt_eval ν p q)))]

#print axioms triple_product_character_matrix_integral_timelike

set_option maxHeartbeats 1000000 in
/-- **Integral of one matrix element times three conjugated matrix elements.**
For irreducible unitary representations of a compact group with normalized Haar measure,
the integral `∫ (ρ_σ g)_{pq} · conj((ρ_{t₁} g)_{c₁d₁}) · conj((ρ_{t₂} g)_{c₂d₂}) · conj((ρ_{t₃} g)_{c₃d₃}) dμ(g)`
equals `(1/dims σ) · ∑_{ν',r',s'} CG_barred(ν',r',s',σ,p,q)`.

Proof: apply `cgME_decomp_3fold_conj` to the 3 barred MEs, exchange sums with integral
(Fubini), apply Schur orthogonality (`characterOrthogonality`): the combined representation
`β` from the barred side is forced to equal `σ` (the unbarred representation), and the
matrix indices `p'=p, q'=q` are forced by the diagonal Kronecker deltas. 0 sorries, 0 new axioms.
This is the key helper for `single_site_3D_luscher_integral` (Step 2 of the Lüscher roadmap). -/
lemma integral_ME_times_3barred_MEs
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (cgME : ∀ (s t ν : ι), Fin (dims s) → Fin (dims t) → Fin (dims ν) → ℂ)
    (hcgME_decomp : ∀ (s t : ι) (g : G) (a b : Fin (dims s)) (i j : Fin (dims t)),
        (ρ s g) a b * (ρ t g) i j =
        ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
          cgME s t ν a i p * (ρ ν g) p q * conj (cgME s t ν b j q))
    (σ : ι) (p : Fin (dims σ)) (q : Fin (dims σ))
    (t1 t2 t3 : ι) (c1 d1 : Fin (dims t1)) (c2 d2 : Fin (dims t2)) (c3 d3 : Fin (dims t3)) :
    ∫ g, (ρ σ g) p q * conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3) ∂μ =
      (1 / dims σ : ℂ) * ∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
        conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
        conj (cgME ν' t3 σ r' c3 p) * cgME ν' t3 σ s' d3 q := by
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  -- Pointwise identity: apply cgME_decomp_3fold_conj to the 3 barred MEs, distribute (ρ σ g) p q
  have hpt : ∀ (g : G),
      (ρ σ g) p q * conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3) =
      ∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
        ∑ β : ι, ∑ p' : Fin (dims β), ∑ q' : Fin (dims β),
          conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
          conj (cgME ν' t3 β r' c3 p') * cgME ν' t3 β s' d3 q' *
          ((ρ σ g) p q * conj ((ρ β g) p' q')) := by
    intro g
    have hreassoc : (ρ σ g) p q * conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
        conj ((ρ t3 g) c3 d3) =
        (ρ σ g) p q *
        (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3)) := by ring
    rw [hreassoc, cgME_decomp_3fold_conj ι dims ρ cgME hcgME_decomp t1 t2 t3 g c1 d1 c2 d2 c3 d3]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ν' _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r' _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s' _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro β _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p' _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q' _
    ring
  -- Rewrite the integral using the pointwise identity
  rw [show (∫ g, (ρ σ g) p q * conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
        conj ((ρ t3 g) c3 d3) ∂μ) =
        ∫ g, (∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
          ∑ β : ι, ∑ p' : Fin (dims β), ∑ q' : Fin (dims β),
            conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
            conj (cgME ν' t3 β r' c3 p') * cgME ν' t3 β s' d3 q' *
            ((ρ σ g) p q * conj ((ρ β g) p' q'))) ∂μ from by
    congr 1 with g; exact hpt g]
  -- Per-term integrability (6 levels, innermost to outermost)
  have hInt_term : ∀ (ν' : ι) (r' : Fin (dims ν')) (s' : Fin (dims ν')) (β : ι)
      (p' : Fin (dims β)) (q' : Fin (dims β)),
      Integrable (fun g =>
        conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
        conj (cgME ν' t3 β r' c3 p') * cgME ν' t3 β s' d3 q' *
        ((ρ σ g) p q * conj ((ρ β g) p' q'))) μ := by
    intro ν' r' s' β p' q'
    exact Integrable.smul
      (conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
       conj (cgME ν' t3 β r' c3 p') * cgME ν' t3 β s' d3 q')
      (hInt σ β p q p' q')
  have hInt_q' : ∀ (ν' : ι) (r' : Fin (dims ν')) (s' : Fin (dims ν')) (β : ι) (p' : Fin (dims β)),
      Integrable (fun g => ∑ q' : Fin (dims β),
        conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
        conj (cgME ν' t3 β r' c3 p') * cgME ν' t3 β s' d3 q' *
        ((ρ σ g) p q * conj ((ρ β g) p' q'))) μ := by
    intro ν' r' s' β p'
    exact integrable_finsetSum Finset.univ (fun q' _ => hInt_term ν' r' s' β p' q')
  have hInt_p' : ∀ (ν' : ι) (r' : Fin (dims ν')) (s' : Fin (dims ν')) (β : ι),
      Integrable (fun g => ∑ p' : Fin (dims β), ∑ q' : Fin (dims β),
        conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
        conj (cgME ν' t3 β r' c3 p') * cgME ν' t3 β s' d3 q' *
        ((ρ σ g) p q * conj ((ρ β g) p' q'))) μ := by
    intro ν' r' s' β
    exact integrable_finsetSum Finset.univ (fun p' _ => hInt_q' ν' r' s' β p')
  have hInt_β : ∀ (ν' : ι) (r' : Fin (dims ν')) (s' : Fin (dims ν')),
      Integrable (fun g => ∑ β : ι, ∑ p' : Fin (dims β), ∑ q' : Fin (dims β),
        conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
        conj (cgME ν' t3 β r' c3 p') * cgME ν' t3 β s' d3 q' *
        ((ρ σ g) p q * conj ((ρ β g) p' q'))) μ := by
    intro ν' r' s'
    exact integrable_finsetSum Finset.univ (fun β _ => hInt_p' ν' r' s' β)
  have hInt_s' : ∀ (ν' : ι) (r' : Fin (dims ν')),
      Integrable (fun g => ∑ s' : Fin (dims ν'), ∑ β : ι, ∑ p' : Fin (dims β), ∑ q' : Fin (dims β),
        conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
        conj (cgME ν' t3 β r' c3 p') * cgME ν' t3 β s' d3 q' *
        ((ρ σ g) p q * conj ((ρ β g) p' q'))) μ := by
    intro ν' r'
    exact integrable_finsetSum Finset.univ (fun s' _ => hInt_β ν' r' s')
  have hInt_r' : ∀ (ν' : ι),
      Integrable (fun g => ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'), ∑ β : ι,
        ∑ p' : Fin (dims β), ∑ q' : Fin (dims β),
        conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
        conj (cgME ν' t3 β r' c3 p') * cgME ν' t3 β s' d3 q' *
        ((ρ σ g) p q * conj ((ρ β g) p' q'))) μ := by
    intro ν'
    exact integrable_finsetSum Finset.univ (fun r' _ => hInt_s' ν' r')
  have hInt_ν' : Integrable (fun g => ∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
        ∑ β : ι, ∑ p' : Fin (dims β), ∑ q' : Fin (dims β),
        conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
        conj (cgME ν' t3 β r' c3 p') * cgME ν' t3 β s' d3 q' *
        ((ρ σ g) p q * conj ((ρ β g) p' q'))) μ := by
    exact integrable_finsetSum Finset.univ (fun ν' _ => hInt_r' ν')
  -- Exchange sums with integral (6 levels)
  rw [integral_finsetSum Finset.univ (fun ν' _ => hInt_r' ν')]
  rw [Finset.sum_congr rfl (fun ν' _ => integral_finsetSum Finset.univ (fun r' _ => hInt_s' ν' r'))]
  rw [Finset.sum_congr rfl (fun ν' _ => Finset.sum_congr rfl (fun r' _ =>
      integral_finsetSum Finset.univ (fun s' _ => hInt_β ν' r' s')))]
  rw [Finset.sum_congr rfl (fun ν' _ => Finset.sum_congr rfl (fun r' _ => Finset.sum_congr rfl
      (fun s' _ => integral_finsetSum Finset.univ (fun β _ => hInt_p' ν' r' s' β))))]
  rw [Finset.sum_congr rfl (fun ν' _ => Finset.sum_congr rfl (fun r' _ => Finset.sum_congr rfl
      (fun s' _ => Finset.sum_congr rfl (fun β _ => integral_finsetSum Finset.univ
        (fun p' _ => hInt_q' ν' r' s' β p')))))]
  rw [Finset.sum_congr rfl (fun ν' _ => Finset.sum_congr rfl (fun r' _ => Finset.sum_congr rfl
      (fun s' _ => Finset.sum_congr rfl (fun β _ => Finset.sum_congr rfl (fun p' _ =>
        integral_finsetSum Finset.univ (fun q' _ => hInt_term ν' r' s' β p' q'))))))]
  -- For β ≠ σ, each integral is 0 (pull constant + Schur offdiag)
  have hβ_ne_zero : ∀ (ν' : ι) (r' : Fin (dims ν')) (s' : Fin (dims ν')) (β : ι),
      β ≠ σ → (∑ p' : Fin (dims β), ∑ q' : Fin (dims β),
        ∫ g,
          conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
          conj (cgME ν' t3 β r' c3 p') * cgME ν' t3 β s' d3 q' *
          ((ρ σ g) p q * conj ((ρ β g) p' q')) ∂μ) = 0 := by
    intro ν' r' s' β hβ
    refine Finset.sum_eq_zero (fun p' _ => ?_)
    refine Finset.sum_eq_zero (fun q' _ => ?_)
    rw [integral_const_mul, hSchur_offdiag σ β p q p' q' (Ne.symm hβ)]
    simp
  -- Collapse β sum: only β = σ contributes
  have hβ_collapse : ∀ (ν' : ι) (r' : Fin (dims ν')) (s' : Fin (dims ν')),
      (∑ β : ι, ∑ p' : Fin (dims β), ∑ q' : Fin (dims β),
        ∫ g,
          conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
          conj (cgME ν' t3 β r' c3 p') * cgME ν' t3 β s' d3 q' *
          ((ρ σ g) p q * conj ((ρ β g) p' q')) ∂μ) =
      (∑ p' : Fin (dims σ), ∑ q' : Fin (dims σ),
        ∫ g,
          conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
          conj (cgME ν' t3 σ r' c3 p') * cgME ν' t3 σ s' d3 q' *
          ((ρ σ g) p q * conj ((ρ σ g) p' q')) ∂μ) := by
    intro ν' r' s'
    exact Finset.sum_eq_single σ (fun β _ hβ => hβ_ne_zero ν' r' s' β hβ)
        (fun h => (h (Finset.mem_univ _)).elim)
  rw [Finset.sum_congr rfl (fun ν' _ => Finset.sum_congr rfl (fun r' _ =>
      Finset.sum_congr rfl (fun s' _ => hβ_collapse ν' r' s')))]
  -- Evaluate each integral (β = σ case: pull constant + Schur diag)
  have hInt_eval : ∀ (ν' : ι) (r' : Fin (dims ν')) (s' : Fin (dims ν'))
      (p' : Fin (dims σ)) (q' : Fin (dims σ)),
      ∫ g,
        conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
        conj (cgME ν' t3 σ r' c3 p') * cgME ν' t3 σ s' d3 q' *
        ((ρ σ g) p q * conj ((ρ σ g) p' q')) ∂μ =
        conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
        conj (cgME ν' t3 σ r' c3 p') * cgME ν' t3 σ s' d3 q' *
        (if p = p' ∧ q = q' then (1 / dims σ : ℂ) else 0) := by
    intro ν' r' s' p' q'
    rw [integral_const_mul, hSchur_diag]
  rw [Finset.sum_congr rfl (fun ν' _ => Finset.sum_congr rfl (fun r' _ =>
      Finset.sum_congr rfl (fun s' _ => Finset.sum_congr rfl (fun p' _ =>
        Finset.sum_congr rfl (fun q' _ => hInt_eval ν' r' s' p' q')))))]
  -- Collapse p', q' sums
  have hpq'_collapse : ∀ (ν' : ι) (r' : Fin (dims ν')) (s' : Fin (dims ν')),
      (∑ p' : Fin (dims σ), ∑ q' : Fin (dims σ),
        conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
        conj (cgME ν' t3 σ r' c3 p') * cgME ν' t3 σ s' d3 q' *
        (if p = p' ∧ q = q' then (1 / dims σ : ℂ) else 0)) =
      conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
      conj (cgME ν' t3 σ r' c3 p) * cgME ν' t3 σ s' d3 q * (1 / dims σ : ℂ) := by
    intro ν' r' s'
    rw [Finset.sum_eq_single p (fun p' _ hp => Finset.sum_eq_zero (fun q' _ => by
        simp [Ne.symm hp])) (fun h => (h (Finset.mem_univ _)).elim)]
    simp only [eq_self_iff_true, true_and]
    rw [Finset.sum_eq_single q (fun q' _ hq => by simp [Ne.symm hq])
        (fun h => (h (Finset.mem_univ _)).elim)]
    simp only [eq_self_iff_true, if_true]
  rw [Finset.sum_congr rfl (fun ν' _ => Finset.sum_congr rfl (fun r' _ =>
      Finset.sum_congr rfl (fun s' _ => hpq'_collapse ν' r' s')))]
  -- Factor out 1/dims σ: push constant inside the sums on the RHS, then match term-by-term
  conv_rhs => simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ν' _
  apply Finset.sum_congr rfl
  intro r' _
  apply Finset.sum_congr rfl
  intro s' _
  ring

#print axioms integral_ME_times_3barred_MEs
