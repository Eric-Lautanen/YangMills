/-
# Positive Definite: Luscher Cascade
-/

import YangMills.Proofs.PositiveDefinite.CharacterOrthogonality

open Finset
open Complex
open Filter
open Matrix
open MeasureTheory
open scoped ComplexConjugate
open scoped ComplexOrder

namespace YangMills
variable {G : Type*} [Group G] {n : Nat}

/-! ## The full 1D L-site Lüscher cascade (Step 3b of the Lüscher roadmap)

The 2-site and 3-site cascades above demonstrate the Lüscher mechanism for fixed small site
counts. Here we generalize to an arbitrary number of sites via an open-chain integral defined
recursively, and prove the cascade by induction on the chain length. -/

/-- The open-chain Lüscher cascade integral. For endpoints `a, b` and a non-empty list of
(representation, Wilson-line) pairs `links = [(γ₀,W₀), (γ₁,W₁), ...]`, this is the iterated
integral `∫∫... χ_{γ₀}(a·W₀·g₁⁻¹)·χ_{γ₁}(g₁·W₁·g₂⁻¹)·...·χ_{γₙ}(gₙ·Wₙ·b⁻¹)` where the
interior variables `g₁, ..., gₙ` are integrated out one at a time (each application of
`luscher_key_identity`). The base case (single link) has no integration. -/
noncomputable def chainIntegral
    {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (a b : G) : List (ι × G) → ℂ
  | [] => 0
  | [x] => repCharacter (ρ x.1) (a * x.2 * b⁻¹)
  | x :: y :: rest => ∫ g, repCharacter (ρ x.1) (a * x.2 * g⁻¹) * chainIntegral μ ι dims ρ g b (y :: rest) ∂μ

/-- Helper: all representations in a list of (rep, Wilson-line) pairs equal a given `γ₀`. -/
def allSameRep (γ₀ : ι) : List (ι × G) → Prop
  | [] => True
  | (γ, _) :: rest => γ = γ₀ ∧ allSameRep γ₀ rest

instance instDecidableAllSameRep [DecidableEq ι] (γ₀ : ι) :
    ∀ (l : List (ι × G)), Decidable (allSameRep γ₀ l)
  | [] => isTrue True.intro
  | (γ, _) :: rest => @instDecidableAnd (γ = γ₀) (allSameRep γ₀ rest)
      (inferInstance) (instDecidableAllSameRep γ₀ rest)

/-- **Full 1D L-site Lüscher cascade (Step 3b of the Lüscher roadmap, §8.11.41).**

For irreducible unitary representations of a compact group with normalized Haar measure, the
open-chain L-site Lüscher cascade evaluates to:

    chainIntegral a b [(γ₀,W₀),...,(γₙ,Wₙ)] = δ_{all γ=γ₀} · (1/d_γ)^n · χ_γ(a · (∏ W) · b⁻¹)

where `n = links.length - 1` is the number of interior integrations. The Schur orthogonality
forces all representations to match (δ conditions), and the surviving coefficient is
`(1/d_γ)^n > 0`. This generalizes `luscher_2site_cascade` and `luscher_3site_cascade` to
arbitrary chain length via Fubini iteration of `luscher_key_identity`. 0 sorries, 0 new axioms. -/
lemma chainIntegral_eq
    {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (a b : G) (γ₀ : ι) (W₀ : G) (rest : List (ι × G)) :
    chainIntegral μ ι dims ρ a b ((γ₀, W₀) :: rest) =
      if allSameRep γ₀ rest then
        (1 / dims γ₀ : ℂ)^rest.length * repCharacter (ρ γ₀) (a * (W₀ :: rest.map Prod.snd).prod * b⁻¹)
      else 0 := by
  classical
  revert a γ₀ W₀
  induction rest with
  | nil =>
    intro a γ₀ W₀
    have hUnfold : chainIntegral μ ι dims ρ a b [(γ₀, W₀)] = repCharacter (ρ γ₀) (a * W₀ * b⁻¹) := rfl
    rw [hUnfold]
    simp only [allSameRep, List.length_nil, List.map_nil, List.prod_cons, List.prod_nil,
      pow_zero, one_mul, mul_one, if_true]
  | cons x rest' ih =>
    obtain ⟨γ₁, W₁⟩ := x
    intro a γ₀ W₀
    have hUnfold : chainIntegral μ ι dims ρ a b ((γ₀, W₀) :: (γ₁, W₁) :: rest') =
        ∫ g, repCharacter (ρ γ₀) (a * W₀ * g⁻¹) * chainIntegral μ ι dims ρ g b ((γ₁, W₁) :: rest') ∂μ := rfl
    rw [hUnfold]
    by_cases h : allSameRep γ₁ rest'
    · -- True case: inner chainIntegral = (1/d_γ₁)^rest'.length * χ_γ₁(...)
      have hIH : ∀ (g : G), chainIntegral μ ι dims ρ g b ((γ₁, W₁) :: rest') =
          (1 / dims γ₁ : ℂ)^rest'.length *
          repCharacter (ρ γ₁) (g * (W₁ :: rest'.map Prod.snd).prod * b⁻¹) := by
        intro g; rw [ih g γ₁ W₁]; simp only [if_pos h]
      simp only [hIH]
      -- Pull constant out of integral
      have hcong : ∫ g, repCharacter (ρ γ₀) (a * W₀ * g⁻¹) *
            ((1 / dims γ₁ : ℂ)^rest'.length * repCharacter (ρ γ₁)
              (g * (W₁ :: rest'.map Prod.snd).prod * b⁻¹)) ∂μ =
          ∫ g, (1 / dims γ₁ : ℂ)^rest'.length *
            (repCharacter (ρ γ₀) (a * W₀ * g⁻¹) *
             repCharacter (ρ γ₁) (g * (W₁ :: rest'.map Prod.snd).prod * b⁻¹)) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun g => by ring)
      rw [hcong, integral_const_mul]
      -- Cyclic rewrite + rearrange to match luscher_key_identity
      have hcyc : ∀ (g : G),
          repCharacter (ρ γ₀) (a * W₀ * g⁻¹) = repCharacter (ρ γ₀) (g⁻¹ * (a * W₀)) := by
        intro g; rw [repCharacter_cyclic, repCharacter_cyclic, mul_assoc]
      have h2 : ∫ g, repCharacter (ρ γ₀) (a * W₀ * g⁻¹) *
            repCharacter (ρ γ₁) (g * (W₁ :: rest'.map Prod.snd).prod * b⁻¹) ∂μ =
          ∫ g, repCharacter (ρ γ₁) (g * ((W₁ :: rest'.map Prod.snd).prod * b⁻¹)) *
            repCharacter (ρ γ₀) (g⁻¹ * (a * W₀)) ∂μ := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro g
        change repCharacter (ρ γ₀) (a * W₀ * g⁻¹) * repCharacter (ρ γ₁) (g * (W₁ :: rest'.map Prod.snd).prod * b⁻¹) =
          repCharacter (ρ γ₁) (g * ((W₁ :: rest'.map Prod.snd).prod * b⁻¹)) * repCharacter (ρ γ₀) (g⁻¹ * (a * W₀))
        rw [hcyc g]
        have hg : g * (W₁ :: rest'.map Prod.snd).prod * b⁻¹ =
            g * ((W₁ :: rest'.map Prod.snd).prod * b⁻¹) := mul_assoc _ _ _
        rw [hg]
        ring
      rw [h2]
      rw [luscher_key_identity μ ι dims hDims ρ hU hIrr γ₁ γ₀
          ((W₁ :: rest'.map Prod.snd).prod * b⁻¹) (a * W₀)]
      by_cases hγ : γ₁ = γ₀
      · -- γ₁ = γ₀
        simp only [if_pos hγ]
        rw [show repCharacter (ρ γ₁) (((W₁ :: rest'.map Prod.snd).prod * b⁻¹) * (a * W₀)) =
            repCharacter (ρ γ₁) (a * W₀ * (W₁ :: rest'.map Prod.snd).prod * b⁻¹) from by
          rw [← mul_assoc, repCharacter_cyclic, ← mul_assoc]]
        have hRHS : allSameRep γ₀ ((γ₁, W₁) :: rest') := by
          rw [allSameRep]; refine ⟨hγ, ?_⟩; rw [← hγ]; exact h
        simp only [hRHS, if_true]
        rw [hγ]
        rw [show ((γ₀, W₁) :: rest').length = rest'.length + 1 from rfl]
        rw [show (W₀ :: ((γ₀, W₁) :: rest').map Prod.snd).prod =
            W₀ * (W₁ :: rest'.map Prod.snd).prod from by
          rw [List.map_cons, List.prod_cons]]
        rw [pow_add, pow_one]
        rw [show a * (W₀ * (W₁ :: rest'.map Prod.snd).prod) * b⁻¹ =
            a * W₀ * (W₁ :: rest'.map Prod.snd).prod * b⁻¹ from by ac_rfl]
        ring
      · -- γ₁ ≠ γ₀
        simp only [if_neg hγ, mul_zero]
        have hRHS : ¬allSameRep γ₀ ((γ₁, W₁) :: rest') := by
          rw [allSameRep]; exact fun hcond => hγ hcond.1
        simp only [if_neg hRHS]
    · -- False case: inner chainIntegral = 0
      have hIH : ∀ (g : G), chainIntegral μ ι dims ρ g b ((γ₁, W₁) :: rest') = 0 := by
        intro g; rw [ih g γ₁ W₁]; simp only [if_neg h]
      simp only [hIH, mul_zero, integral_zero]
      have hRHS : ¬allSameRep γ₀ ((γ₁, W₁) :: rest') := by
        rw [allSameRep]
        intro hcond
        exact h (hcond.1 ▸ hcond.2)
      simp only [if_neg hRHS]

#print axioms chainIntegral_eq

/-! ## The full 1D L-site bipartite Lüscher cascade (Step 3b, transfer matrix)

The bipartite cascade generalizes `chainIntegral_eq` to plaquettes with BOTH
a V-link and a W-link (the structure needed for the transfer matrix). Each
plaquette product is `g_i · V_i · g_{i+1}⁻¹ · W_i⁻¹`, and the cascade
integrates out the interior temporal links, forcing all representations to
match and producing `(1/d_γ)^n · χ_γ(a · V-product · b⁻¹ · W-product⁻¹)`.
This is the 1D building block for the Lüscher transfer matrix cascade. -/

/-- Helper: all representations in a list of (rep, V-link, W-link) triples equal `γ₀`. -/
def allSameRep3 {ι : Type*} [DecidableEq ι] (γ₀ : ι) : List (ι × G × G) → Prop
  | [] => True
  | (γ, _, _) :: rest => γ = γ₀ ∧ allSameRep3 γ₀ rest

instance instDecidableAllSameRep3 {ι : Type*} [DecidableEq ι] (γ₀ : ι) :
    ∀ (l : List (ι × G × G)), Decidable (allSameRep3 γ₀ l)
  | [] => isTrue True.intro
  | (γ, _, _) :: rest => @instDecidableAnd (γ = γ₀) (allSameRep3 γ₀ rest)
      (inferInstance) (instDecidableAllSameRep3 γ₀ rest)

/-- The bipartite open-chain Lüscher cascade integral. For endpoints `a, b` and a
non-empty list of (representation, V-link, W-link) triples, this is the iterated
integral `∫∫... χ_{γ₀}(a·V₀·g₁⁻¹·W₀⁻¹)·χ_{γ₁}(g₁·V₁·g₂⁻¹·W₁⁻¹)·...` where the
interior variables `g₁, ..., gₙ` are integrated out one at a time. Each plaquette
has both a V-link and a W-link (the bipartite structure needed for the transfer
matrix kernel `Σ_s c_s · χ_s(W-product) · χ_s(V-product)`). -/
noncomputable def bipartiteChainIntegral
    {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (a b : G) : List (ι × G × G) → ℂ
  | [] => 0
  | [x] => repCharacter (ρ x.1) (a * x.2.1 * b⁻¹ * x.2.2⁻¹)
  | x :: y :: rest => ∫ g, repCharacter (ρ x.1) (a * x.2.1 * g⁻¹ * x.2.2⁻¹) *
      bipartiteChainIntegral μ ι dims ρ g b (y :: rest) ∂μ

/-- **Full 1D L-site bipartite Lüscher cascade.**

For irreducible unitary representations of a compact group with normalized Haar
measure, the open-chain L-site bipartite cascade evaluates to:

    bipartiteChainIntegral a b [(γ₀,V₀,W₀),...,(γₙ,Vₙ,Wₙ)] =
      δ_{all γ=γ₀} · (1/d_γ)^n · χ_γ(a · V-product · b⁻¹ · W-product⁻¹)

where `n = links.length - 1` is the number of interior integrations,
`V-product = V₀·...·Vₙ`, `W-product = W₀·...·Wₙ`. The Schur orthogonality
forces all representations to match, and the surviving coefficient is
`(1/d_γ)^n > 0`. This generalizes `luscher_2site_cascade_separable` to
arbitrary chain length via Fubini iteration of `luscher_key_identity`. -/
lemma bipartiteChainIntegral_eq
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (a b : G) (γ₀ : ι) (V₀ W₀ : G) (rest : List (ι × G × G)) :
    bipartiteChainIntegral μ ι dims ρ a b ((γ₀, V₀, W₀) :: rest) =
      if allSameRep3 γ₀ rest then
        (1 / dims γ₀ : ℂ)^rest.length *
        repCharacter (ρ γ₀) (a * (V₀ :: rest.map (fun x => x.2.1)).prod * b⁻¹ *
          ((W₀ :: rest.map (fun x => x.2.2)).prod)⁻¹)
      else 0 := by
  classical
  revert a γ₀ V₀ W₀
  induction rest with
  | nil =>
    intro a γ₀ V₀ W₀
    have hUnfold : bipartiteChainIntegral μ ι dims ρ a b [(γ₀, V₀, W₀)] =
        repCharacter (ρ γ₀) (a * V₀ * b⁻¹ * W₀⁻¹) := rfl
    rw [hUnfold]
    simp only [allSameRep3, List.length_nil, List.map_nil, List.prod_cons, List.prod_nil,
      pow_zero, one_mul, mul_one, if_true]
  | cons x rest' ih =>
    obtain ⟨γ₁, V₁, W₁⟩ := x
    intro a γ₀ V₀ W₀
    have hUnfold : bipartiteChainIntegral μ ι dims ρ a b ((γ₀, V₀, W₀) :: (γ₁, V₁, W₁) :: rest') =
        ∫ g, repCharacter (ρ γ₀) (a * V₀ * g⁻¹ * W₀⁻¹) *
          bipartiteChainIntegral μ ι dims ρ g b ((γ₁, V₁, W₁) :: rest') ∂μ := rfl
    rw [hUnfold]
    by_cases h : allSameRep3 γ₁ rest'
    · -- True case: inner = (1/d_γ₁)^n · χ_γ₁(g · V-product · b⁻¹ · W-product⁻¹)
      have hIH : ∀ (g : G), bipartiteChainIntegral μ ι dims ρ g b ((γ₁, V₁, W₁) :: rest') =
          (1 / dims γ₁ : ℂ)^rest'.length *
          repCharacter (ρ γ₁) (g * (V₁ :: rest'.map (fun x => x.2.1)).prod * b⁻¹ *
            ((W₁ :: rest'.map (fun x => x.2.2)).prod)⁻¹) := by
        intro g; rw [ih g γ₁ V₁ W₁]; simp only [if_pos h]
      simp only [hIH]
      -- Pull constant out of integral
      have hcong : ∫ g, repCharacter (ρ γ₀) (a * V₀ * g⁻¹ * W₀⁻¹) *
            ((1 / dims γ₁ : ℂ)^rest'.length *
             repCharacter (ρ γ₁) (g * (V₁ :: rest'.map (fun x => x.2.1)).prod * b⁻¹ *
               ((W₁ :: rest'.map (fun x => x.2.2)).prod)⁻¹)) ∂μ =
          ∫ g, (1 / dims γ₁ : ℂ)^rest'.length *
            (repCharacter (ρ γ₀) (a * V₀ * g⁻¹ * W₀⁻¹) *
             repCharacter (ρ γ₁) (g * (V₁ :: rest'.map (fun x => x.2.1)).prod * b⁻¹ *
               ((W₁ :: rest'.map (fun x => x.2.2)).prod)⁻¹)) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun g => by ring)
      rw [hcong, integral_const_mul]
      -- Cyclic rewrite: χ_γ₀(a·V₀·g⁻¹·W₀⁻¹) = χ_γ₀(g⁻¹·(W₀⁻¹·a·V₀))
      have hcyc : ∀ (g : G),
          repCharacter (ρ γ₀) (a * V₀ * g⁻¹ * W₀⁻¹) =
          repCharacter (ρ γ₀) (g⁻¹ * (W₀⁻¹ * a * V₀)) := by
        intro g; rw [repCharacter_cyclic (ρ γ₀) (a * V₀) g⁻¹ W₀⁻¹]
        simp only [mul_assoc]
      -- Rearrange to match luscher_key_identity
      have h2 : ∫ g, repCharacter (ρ γ₀) (a * V₀ * g⁻¹ * W₀⁻¹) *
            repCharacter (ρ γ₁) (g * (V₁ :: rest'.map (fun x => x.2.1)).prod * b⁻¹ *
              ((W₁ :: rest'.map (fun x => x.2.2)).prod)⁻¹) ∂μ =
          ∫ g, repCharacter (ρ γ₁) (g * ((V₁ :: rest'.map (fun x => x.2.1)).prod * b⁻¹ *
            ((W₁ :: rest'.map (fun x => x.2.2)).prod)⁻¹)) *
            repCharacter (ρ γ₀) (g⁻¹ * (W₀⁻¹ * a * V₀)) ∂μ := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro g
        change repCharacter (ρ γ₀) (a * V₀ * g⁻¹ * W₀⁻¹) *
            repCharacter (ρ γ₁) (g * (V₁ :: rest'.map (fun x => x.2.1)).prod * b⁻¹ *
              ((W₁ :: rest'.map (fun x => x.2.2)).prod)⁻¹) =
          repCharacter (ρ γ₁) (g * ((V₁ :: rest'.map (fun x => x.2.1)).prod * b⁻¹ *
            ((W₁ :: rest'.map (fun x => x.2.2)).prod)⁻¹)) *
          repCharacter (ρ γ₀) (g⁻¹ * (W₀⁻¹ * a * V₀))
        rw [hcyc g]
        have hg : g * (V₁ :: rest'.map (fun x => x.2.1)).prod * b⁻¹ *
            ((W₁ :: rest'.map (fun x => x.2.2)).prod)⁻¹ =
            g * ((V₁ :: rest'.map (fun x => x.2.1)).prod * b⁻¹ *
              ((W₁ :: rest'.map (fun x => x.2.2)).prod)⁻¹) := by ac_rfl
        rw [hg]
        ring
      rw [h2]
      -- Apply luscher_key_identity
      rw [luscher_key_identity μ ι dims hDims ρ hU hIrr γ₁ γ₀
          ((V₁ :: rest'.map (fun x => x.2.1)).prod * b⁻¹ *
           ((W₁ :: rest'.map (fun x => x.2.2)).prod)⁻¹)
          (W₀⁻¹ * a * V₀)]
      by_cases hγ : γ₁ = γ₀
      · -- γ₁ = γ₀ case
        simp only [if_pos hγ]
        have hRHS : allSameRep3 γ₀ ((γ₁, V₁, W₁) :: rest') := by
          rw [allSameRep3]; refine ⟨hγ, ?_⟩; rw [← hγ]; exact h
        simp only [hRHS, if_true]
        rw [hγ]
        -- Unfold RHS list products
        rw [show (V₀ :: ((γ₀, V₁, W₁) :: rest').map (fun x => x.2.1)).prod =
            V₀ * (V₁ :: rest'.map (fun x => x.2.1)).prod from by
          rw [List.map_cons, List.prod_cons]]
        rw [show (W₀ :: ((γ₀, V₁, W₁) :: rest').map (fun x => x.2.2)).prod =
            W₀ * (W₁ :: rest'.map (fun x => x.2.2)).prod from by
          rw [List.map_cons, List.prod_cons]]
        rw [show ((W₀ * (W₁ :: rest'.map (fun x => x.2.2)).prod)⁻¹) =
            ((W₁ :: rest'.map (fun x => x.2.2)).prod)⁻¹ * W₀⁻¹ from by
          rw [_root_.mul_inv_rev]]
        -- Cyclic rewrite of LHS character to match RHS character
        rw [show repCharacter (ρ γ₀)
            ((V₁ :: rest'.map (fun x => x.2.1)).prod * b⁻¹ *
              ((W₁ :: rest'.map (fun x => x.2.2)).prod)⁻¹ * (W₀⁻¹ * a * V₀)) =
            repCharacter (ρ γ₀)
            (a * (V₀ * (V₁ :: rest'.map (fun x => x.2.1)).prod) * b⁻¹ *
              ((W₁ :: rest'.map (fun x => x.2.2)).prod)⁻¹ * W₀⁻¹) from by
          rw [repCharacter_cyclic2 _
              ((V₁ :: rest'.map (fun x => x.2.1)).prod * b⁻¹ *
                ((W₁ :: rest'.map (fun x => x.2.2)).prod)⁻¹)
              (W₀⁻¹ * a * V₀)]
          rw [show (W₀⁻¹ * a * V₀) *
              ((V₁ :: rest'.map (fun x => x.2.1)).prod * b⁻¹ *
                ((W₁ :: rest'.map (fun x => x.2.2)).prod)⁻¹) =
              W₀⁻¹ * (a * V₀ * (V₁ :: rest'.map (fun x => x.2.1)).prod * b⁻¹ *
                ((W₁ :: rest'.map (fun x => x.2.2)).prod)⁻¹) from by ac_rfl]
          rw [repCharacter_cyclic2 _ W₀⁻¹
              (a * V₀ * (V₁ :: rest'.map (fun x => x.2.1)).prod * b⁻¹ *
                ((W₁ :: rest'.map (fun x => x.2.2)).prod)⁻¹)]
          rw [show (a * V₀ * (V₁ :: rest'.map (fun x => x.2.1)).prod * b⁻¹ *
              ((W₁ :: rest'.map (fun x => x.2.2)).prod)⁻¹) * W₀⁻¹ =
              a * (V₀ * (V₁ :: rest'.map (fun x => x.2.1)).prod) * b⁻¹ *
              ((W₁ :: rest'.map (fun x => x.2.2)).prod)⁻¹ * W₀⁻¹ from by ac_rfl]]
        -- Handle powers
        rw [show ((γ₀, V₁, W₁) :: rest').length = rest'.length + 1 from rfl]
        rw [pow_add, pow_one]
        -- Align character args (differ only by associativity of last two factors)
        rw [show repCharacter (ρ γ₀)
            (a * (V₀ * (V₁ :: rest'.map (fun x => x.2.1)).prod) * b⁻¹ *
              ((W₁ :: rest'.map (fun x => x.2.2)).prod)⁻¹ * W₀⁻¹) =
            repCharacter (ρ γ₀)
            (a * (V₀ * (V₁ :: rest'.map (fun x => x.2.1)).prod) * b⁻¹ *
              (((W₁ :: rest'.map (fun x => x.2.2)).prod)⁻¹ * W₀⁻¹)) from by
          rw [show a * (V₀ * (V₁ :: rest'.map (fun x => x.2.1)).prod) * b⁻¹ *
              ((W₁ :: rest'.map (fun x => x.2.2)).prod)⁻¹ * W₀⁻¹ =
              a * (V₀ * (V₁ :: rest'.map (fun x => x.2.1)).prod) * b⁻¹ *
              (((W₁ :: rest'.map (fun x => x.2.2)).prod)⁻¹ * W₀⁻¹) from by ac_rfl]]
        ring
      · -- γ₁ ≠ γ₀ case
        simp only [if_neg hγ, mul_zero]
        have hRHS : ¬allSameRep3 γ₀ ((γ₁, V₁, W₁) :: rest') := by
          rw [allSameRep3]; exact fun hcond => hγ hcond.1
        simp only [if_neg hRHS]
    · -- False case: inner = 0
      have hIH : ∀ (g : G), bipartiteChainIntegral μ ι dims ρ g b ((γ₁, V₁, W₁) :: rest') = 0 := by
        intro g; rw [ih g γ₁ V₁ W₁]; simp only [if_neg h]
      simp only [hIH, mul_zero, integral_zero]
      have hRHS : ¬allSameRep3 γ₀ ((γ₁, V₁, W₁) :: rest') := by
        rw [allSameRep3]
        intro hcond
        exact h (hcond.1 ▸ hcond.2)
      simp only [if_neg hRHS]

#print axioms bipartiteChainIntegral_eq


/-- **2-site 2D Lüscher cascade at the character level (Step 3c of the Lüscher roadmap,
§8.11.42).**

For irreducible unitary representations of a compact group with normalized Haar
measure, the 2-site 2D cascade integral — where the two plaquettes at each site
share the same `W` factor (simplification) — evaluates to:

    ∫∫ [χ_{s₁}(g₀·W·g₁⁻¹) · χ_{s₂}(g₀·W·g₁⁻¹)] ·
        [χ_{t₁}(g₁·V·g₀⁻¹) · χ_{t₂}(g₁·V·g₀⁻¹)] dμ(g₁) dμ(g₀)
      = ∑_ν cg s₁ s₂ ν · cg t₁ t₂ ν · (1/d_ν) · χ_ν(W·V)

The proof uses the Clebsch-Gordan character decomposition `hcg_decomp` to rewrite
each product of two characters as a sum over irreps, then exchanges the finite sums
with the inner `g₁` integral (justified by integrability from Schur orthogonality
of matrix elements), and applies `luscher_key_identity` to each inner integral.
The Schur orthogonality forces `ν' = ν`, and the surviving coefficient is
`cg s₁ s₂ ν · cg t₁ t₂ ν · (1/d_ν)`. The `χ_ν(V·W)` from `luscher_key_identity`
is converted to `χ_ν(W·V)` by `trace_mul_comm`.

This is the character-level 2-site 2D cascade: it uses the CG decomposition
`hcg_decomp` (which gives non-negative CG coefficients `cg s t ν ≥ 0` in the
Peter-Weyl axiom) combined with `luscher_key_identity`. The result is a sum of
terms `cg s₁ s₂ ν · cg t₁ t₂ ν · (1/d_ν) · χ_ν(W·V)`, each with a non-negative
coefficient `cg s₁ s₂ ν · cg t₁ t₂ ν ≥ 0` (product of non-negative CG coefficients)
times the positive-definite character `χ_ν`. 0 sorries, 0 new axioms. -/
lemma luscher_2site_2D_cascade_charlevel
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (cg : ι → ι → ι → ℝ)
    (hcg_decomp : ∀ s t (g : G),
      repCharacter (ρ s) g * repCharacter (ρ t) g =
      ∑ ν : ι, (cg s t ν : ℂ) * repCharacter (ρ ν) g)
    (s₁ s₂ t₁ t₂ : ι) (W V : G) :
    ∫ g₀, ∫ g₁,
      (repCharacter (ρ s₁) (g₀ * W * g₁⁻¹) * repCharacter (ρ s₂) (g₀ * W * g₁⁻¹)) *
      (repCharacter (ρ t₁) (g₁ * V * g₀⁻¹) * repCharacter (ρ t₂) (g₁ * V * g₀⁻¹)) ∂μ ∂μ =
    ∑ ν : ι, (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν : ℂ) *
      ((1 / dims ν : ℂ) * repCharacter (ρ ν) (W * V)) := by
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  have htrace_mul : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ),
      Matrix.trace (A * B) = ∑ i : Fin n, ∑ j : Fin n, A i j * B j i := by
    intro n A B; simp [Matrix.trace, Matrix.mul_apply]
  -- Integrability of character product w.r.t. g₁ (for fixed g₀, ν, ν')
  have hInt_char : ∀ (g₀ : G) (ν ν' : ι),
      Integrable (fun g₁ =>
        repCharacter (ρ ν) (g₀ * W * g₁⁻¹) * repCharacter (ρ ν') (g₁ * V * g₀⁻¹)) μ := by
    intro g₀ ν ν'
    have hchar_ν : ∀ (g₁ : G),
        repCharacter (ρ ν) (g₀ * W * g₁⁻¹) =
        ∑ a : Fin (dims ν), ∑ b : Fin (dims ν),
          (ρ ν (g₀ * W)) a b * conj ((ρ ν g₁) a b) := by
      intro g₁
      rw [repCharacter, MonoidHom.map_mul, htrace_mul]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [repMatrixElement_inv (ρ ν) (hU ν) g₁ b a]
    have hchar_ν' : ∀ (g₁ : G),
        repCharacter (ρ ν') (g₁ * V * g₀⁻¹) =
        ∑ c : Fin (dims ν'), ∑ d : Fin (dims ν'),
          (ρ ν' g₁) c d * (ρ ν' (V * g₀⁻¹)) d c := by
      intro g₁
      rw [show g₁ * V * g₀⁻¹ = g₁ * (V * g₀⁻¹) from mul_assoc _ _ _,
          repCharacter, MonoidHom.map_mul, htrace_mul]
    have hprod_expand : ∀ (g₁ : G),
        repCharacter (ρ ν) (g₀ * W * g₁⁻¹) * repCharacter (ρ ν') (g₁ * V * g₀⁻¹) =
        ∑ a : Fin (dims ν), ∑ c : Fin (dims ν'),
          ∑ b : Fin (dims ν), ∑ d : Fin (dims ν'),
            (ρ ν (g₀ * W)) a b * (ρ ν' (V * g₀⁻¹)) d c *
            ((ρ ν' g₁) c d * conj ((ρ ν g₁) a b)) := by
      intro g₁
      rw [hchar_ν, hchar_ν']
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
    have hInt_term : ∀ (a : Fin (dims ν)) (b : Fin (dims ν))
        (c : Fin (dims ν')) (d : Fin (dims ν')),
        Integrable (fun g₁ =>
          (ρ ν (g₀ * W)) a b * (ρ ν' (V * g₀⁻¹)) d c *
          ((ρ ν' g₁) c d * conj ((ρ ν g₁) a b))) μ := by
      intro a b c d
      have h_gdep : Integrable (fun g₁ => (ρ ν' g₁) c d * conj ((ρ ν g₁) a b)) μ :=
        hInt ν' ν c d a b
      exact (h_gdep.smul ((ρ ν (g₀ * W)) a b * (ρ ν' (V * g₀⁻¹)) d c)).congr
        (Filter.Eventually.of_forall (fun g₁ => by
          simp only [Pi.smul_def, smul_eq_mul]))
    have hInt_d : ∀ (a : Fin (dims ν)) (c : Fin (dims ν')) (b : Fin (dims ν)),
        Integrable (fun g₁ => ∑ d : Fin (dims ν'),
          (ρ ν (g₀ * W)) a b * (ρ ν' (V * g₀⁻¹)) d c *
          ((ρ ν' g₁) c d * conj ((ρ ν g₁) a b))) μ :=
      fun a c b => integrable_finsetSum Finset.univ (fun d _ => hInt_term a b c d)
    have hInt_b : ∀ (a : Fin (dims ν)) (c : Fin (dims ν')),
        Integrable (fun g₁ => ∑ b : Fin (dims ν), ∑ d : Fin (dims ν'),
          (ρ ν (g₀ * W)) a b * (ρ ν' (V * g₀⁻¹)) d c *
          ((ρ ν' g₁) c d * conj ((ρ ν g₁) a b))) μ :=
      fun a c => integrable_finsetSum Finset.univ (fun b _ => hInt_d a c b)
    have hInt_c : ∀ (a : Fin (dims ν)),
        Integrable (fun g₁ => ∑ c : Fin (dims ν'), ∑ b : Fin (dims ν), ∑ d : Fin (dims ν'),
          (ρ ν (g₀ * W)) a b * (ρ ν' (V * g₀⁻¹)) d c *
          ((ρ ν' g₁) c d * conj ((ρ ν g₁) a b))) μ :=
      fun a => integrable_finsetSum Finset.univ (fun c _ => hInt_b a c)
    have hInt_sum : Integrable (fun g₁ =>
        ∑ a : Fin (dims ν), ∑ c : Fin (dims ν'),
          ∑ b : Fin (dims ν), ∑ d : Fin (dims ν'),
            (ρ ν (g₀ * W)) a b * (ρ ν' (V * g₀⁻¹)) d c *
            ((ρ ν' g₁) c d * conj ((ρ ν g₁) a b))) μ :=
      integrable_finsetSum Finset.univ (fun a _ => hInt_c a)
    exact hInt_sum.congr (Filter.Eventually.of_forall (fun g₁ => (hprod_expand g₁).symm))
  -- Integrability of each (ν, ν') term w.r.t. g₁
  have hInt_term_νν' : ∀ (g₀ : G) (ν ν' : ι),
      Integrable (fun g₁ =>
        (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ) *
        (repCharacter (ρ ν) (g₀ * W * g₁⁻¹) * repCharacter (ρ ν') (g₁ * V * g₀⁻¹))) μ := by
    intro g₀ ν ν'
    exact ((hInt_char g₀ ν ν').smul ((cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ))).congr
      (Filter.Eventually.of_forall (fun g₁ => by
        simp only [Pi.smul_def, smul_eq_mul]))
  have hInt_ν' : ∀ (g₀ : G) (ν : ι),
      Integrable (fun g₁ =>
        ∑ ν' : ι, (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ) *
        (repCharacter (ρ ν) (g₀ * W * g₁⁻¹) * repCharacter (ρ ν') (g₁ * V * g₀⁻¹))) μ :=
    fun g₀ ν => integrable_finsetSum Finset.univ (fun ν' _ => hInt_term_νν' g₀ ν ν')
  -- Pointwise identity: integrand = ∑ ν ∑ ν', cg·cg'·χ_ν·χ_{ν'}
  have hprod : ∀ (g₀ g₁ : G),
      (repCharacter (ρ s₁) (g₀ * W * g₁⁻¹) * repCharacter (ρ s₂) (g₀ * W * g₁⁻¹)) *
      (repCharacter (ρ t₁) (g₁ * V * g₀⁻¹) * repCharacter (ρ t₂) (g₁ * V * g₀⁻¹)) =
      ∑ ν : ι, ∑ ν' : ι,
        (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ) *
        (repCharacter (ρ ν) (g₀ * W * g₁⁻¹) * repCharacter (ρ ν') (g₁ * V * g₀⁻¹)) := by
    intro g₀ g₁
    rw [hcg_decomp s₁ s₂ (g₀ * W * g₁⁻¹), hcg_decomp t₁ t₂ (g₁ * V * g₀⁻¹)]
    simp only [Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro ν _
    apply Finset.sum_congr rfl
    intro ν' _
    ring
  -- Inner integral via luscher_key_identity
  have hInner : ∀ (g₀ : G) (ν ν' : ι),
      ∫ g₁, repCharacter (ρ ν) (g₀ * W * g₁⁻¹) * repCharacter (ρ ν') (g₁ * V * g₀⁻¹) ∂μ =
      if ν' = ν then (1 / dims ν' : ℂ) * repCharacter (ρ ν') (V * W) else 0 := by
    intro g₀ ν ν'
    rw [show (∫ g₁, repCharacter (ρ ν) (g₀ * W * g₁⁻¹) *
          repCharacter (ρ ν') (g₁ * V * g₀⁻¹) ∂μ) =
        ∫ g₁, repCharacter (ρ ν') (g₁ * (V * g₀⁻¹)) *
          repCharacter (ρ ν) (g₁⁻¹ * (g₀ * W)) ∂μ from by
      congr 1 with g₁
      rw [show repCharacter (ρ ν) (g₀ * W * g₁⁻¹) = repCharacter (ρ ν) (g₁⁻¹ * (g₀ * W)) from by
        rw [repCharacter_cyclic, repCharacter_cyclic, mul_assoc]]
      rw [show repCharacter (ρ ν') (g₁ * V * g₀⁻¹) = repCharacter (ρ ν') (g₁ * (V * g₀⁻¹)) from by
        rw [mul_assoc]]
      ring]
    rw [luscher_key_identity μ ι dims hDims ρ hU hIrr ν' ν (V * g₀⁻¹) (g₀ * W)]
    by_cases h : ν' = ν
    · rw [if_pos h, if_pos h]
      rw [show (V * g₀⁻¹) * (g₀ * W) = V * W from by
        have hinv : g₀⁻¹ * g₀ = 1 := inv_mul_cancel _
        calc (V * g₀⁻¹) * (g₀ * W) = V * (g₀⁻¹ * (g₀ * W)) := by rw [mul_assoc]
          _ = V * ((g₀⁻¹ * g₀) * W) := by rw [← mul_assoc g₀⁻¹ g₀ W]
          _ = V * (1 * W) := by rw [hinv]
          _ = V * W := by rw [one_mul]]
    · rw [if_neg h, if_neg h]
  -- Inner integral with constants pulled out
  have hInner_full : ∀ (g₀ : G) (ν ν' : ι),
      ∫ g₁, (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ) *
        (repCharacter (ρ ν) (g₀ * W * g₁⁻¹) * repCharacter (ρ ν') (g₁ * V * g₀⁻¹)) ∂μ =
      (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ) *
      (if ν' = ν then (1 / dims ν' : ℂ) * repCharacter (ρ ν') (V * W) else 0) := by
    intro g₀ ν ν'
    rw [integral_const_mul, hInner g₀ ν ν']
  -- Rewrite integrand using hprod
  rw [show (∫ g₀, ∫ g₁,
        (repCharacter (ρ s₁) (g₀ * W * g₁⁻¹) * repCharacter (ρ s₂) (g₀ * W * g₁⁻¹)) *
        (repCharacter (ρ t₁) (g₁ * V * g₀⁻¹) * repCharacter (ρ t₂) (g₁ * V * g₀⁻¹)) ∂μ ∂μ) =
      ∫ g₀, ∫ g₁,
        (∑ ν : ι, ∑ ν' : ι,
          (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ) *
          (repCharacter (ρ ν) (g₀ * W * g₁⁻¹) * repCharacter (ρ ν') (g₁ * V * g₀⁻¹))) ∂μ ∂μ from by
    congr 1 with g₀; congr 1 with g₁; exact hprod g₀ g₁]
  -- Exchange ν sum with g₁ integral
  rw [show (∫ g₀, ∫ g₁,
        (∑ ν : ι, ∑ ν' : ι,
          (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ) *
          (repCharacter (ρ ν) (g₀ * W * g₁⁻¹) * repCharacter (ρ ν') (g₁ * V * g₀⁻¹))) ∂μ ∂μ) =
      ∫ g₀, ∑ ν : ι, ∫ g₁,
        (∑ ν' : ι,
          (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ) *
          (repCharacter (ρ ν) (g₀ * W * g₁⁻¹) * repCharacter (ρ ν') (g₁ * V * g₀⁻¹))) ∂μ ∂μ from by
    congr 1 with g₀
    rw [integral_finsetSum Finset.univ (fun ν _ => hInt_ν' g₀ ν)]]
  -- Exchange ν' sum with g₁ integral
  rw [show (∫ g₀, ∑ ν : ι, ∫ g₁,
        (∑ ν' : ι,
          (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ) *
          (repCharacter (ρ ν) (g₀ * W * g₁⁻¹) * repCharacter (ρ ν') (g₁ * V * g₀⁻¹))) ∂μ ∂μ) =
      ∫ g₀, ∑ ν : ι, ∑ ν' : ι, ∫ g₁,
        ((cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ) *
          (repCharacter (ρ ν) (g₀ * W * g₁⁻¹) * repCharacter (ρ ν') (g₁ * V * g₀⁻¹))) ∂μ ∂μ from by
    congr 1 with g₀
    apply Finset.sum_congr rfl
    intro ν _
    rw [integral_finsetSum Finset.univ (fun ν' _ => hInt_term_νν' g₀ ν ν')]]
  -- Apply hInner_full to each inner integral
  rw [show (∫ g₀, ∑ ν : ι, ∑ ν' : ι, ∫ g₁,
        ((cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ) *
          (repCharacter (ρ ν) (g₀ * W * g₁⁻¹) * repCharacter (ρ ν') (g₁ * V * g₀⁻¹))) ∂μ ∂μ) =
      ∫ g₀, ∑ ν : ι, ∑ ν' : ι,
        (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ) *
        (if ν' = ν then (1 / dims ν' : ℂ) * repCharacter (ρ ν') (V * W) else 0) ∂μ from by
    congr 1 with g₀
    apply Finset.sum_congr rfl
    intro ν _
    apply Finset.sum_congr rfl
    intro ν' _
    exact hInner_full g₀ ν ν']
  -- Pull constant out of g₀ integral (integrand is independent of g₀)
  rw [show (∫ g₀, ∑ ν : ι, ∑ ν' : ι,
        (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ) *
        (if ν' = ν then (1 / dims ν' : ℂ) * repCharacter (ρ ν') (V * W) else 0) ∂μ) =
      ∑ ν : ι, ∑ ν' : ι,
        (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ) *
        (if ν' = ν then (1 / dims ν' : ℂ) * repCharacter (ρ ν') (V * W) else 0) from by
    haveI : IsFiniteMeasure μ := inferInstance
    simp [integral_const, IsProbabilityMeasure.measure_univ]]
  -- Collapse the if and simplify
  rw [show (∑ ν : ι, ∑ ν' : ι,
        (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ) *
        (if ν' = ν then (1 / dims ν' : ℂ) * repCharacter (ρ ν') (V * W) else 0)) =
      ∑ ν : ι, (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν : ℂ) *
        ((1 / dims ν : ℂ) * repCharacter (ρ ν) (V * W)) from by
    apply Finset.sum_congr rfl
    intro ν _
    have key : ∑ ν' : ι, (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν' : ℂ) *
        (if ν' = ν then (1 / dims ν' : ℂ) * repCharacter (ρ ν') (V * W) else 0) =
      (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν : ℂ) *
        (if ν = ν then (1 / dims ν : ℂ) * repCharacter (ρ ν) (V * W) else 0) := by
      refine Finset.sum_eq_single ν ?_ ?_
      · intro ν' _ hne
        rw [if_neg (fun h => hne h)]
        ring
      · intro h; exact absurd (Finset.mem_univ ν) h
    rw [key, if_pos rfl]]
  -- χ_ν(V*W) = χ_ν(W*V) by trace_mul_comm
  apply Finset.sum_congr rfl
  intro ν _
  rw [show repCharacter (ρ ν) (V * W) = repCharacter (ρ ν) (W * V) from by
    show Matrix.trace (ρ ν (V * W)) = Matrix.trace (ρ ν (W * V))
    rw [show ρ ν (V * W) = ρ ν V * ρ ν W from MonoidHom.map_mul _ _ _,
        show ρ ν (W * V) = ρ ν W * ρ ν V from MonoidHom.map_mul _ _ _,
        Matrix.trace_mul_comm]]

#print axioms luscher_2site_2D_cascade_charlevel

/-- **Integrability of a character product** `χ_s(A · g⁻¹) · χ_t(g · B)` w.r.t. `g`.

For irreducible unitary representations of a compact group with normalized Haar
measure, the product of two characters `χ_s(A · g⁻¹) · χ_t(g · B)` is integrable
w.r.t. `g` for any fixed `A, B ∈ G` and representations `s, t`. This follows by
expanding both characters into matrix elements (using unitarity `ρ(g⁻¹) = ρ(g)†`
via `repMatrixElement_inv`), distributing the product via `Fintype.sum_mul_sum`,
and applying the matrix-element integrability from `characterOrthogonality`.

This is the standalone generalization of the local `hInt_char` hypothesis in
`luscher_2site_cascade_coeff`, extracted for reuse in the 3-site cascade. -/
lemma char_product_integrable
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (s t : ι) (A B : G) :
    Integrable (fun g =>
      repCharacter (ρ s) (A * g⁻¹) * repCharacter (ρ t) (g * B)) μ := by
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  have htrace_mul : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ),
      Matrix.trace (A * B) = ∑ i : Fin n, ∑ j : Fin n, A i j * B j i := by
    intro n A B; simp [Matrix.trace, Matrix.mul_apply]
  have hchar_s : ∀ (g : G),
      repCharacter (ρ s) (A * g⁻¹) =
      ∑ a : Fin (dims s), ∑ b : Fin (dims s),
        (ρ s A) a b * conj ((ρ s g) a b) := by
    intro g
    rw [repCharacter, MonoidHom.map_mul, htrace_mul]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [repMatrixElement_inv (ρ s) (hU s) g b a]
  have hchar_t : ∀ (g : G),
      repCharacter (ρ t) (g * B) =
      ∑ c : Fin (dims t), ∑ d : Fin (dims t),
        (ρ t g) c d * (ρ t B) d c := by
    intro g
    rw [repCharacter, MonoidHom.map_mul, htrace_mul]
  have hprod_expand : ∀ (g : G),
      repCharacter (ρ s) (A * g⁻¹) * repCharacter (ρ t) (g * B) =
      ∑ a : Fin (dims s), ∑ c : Fin (dims t),
        ∑ b : Fin (dims s), ∑ d : Fin (dims t),
          (ρ s A) a b * (ρ t B) d c *
          ((ρ t g) c d * conj ((ρ s g) a b)) := by
    intro g
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
      Integrable (fun g =>
        (ρ s A) a b * (ρ t B) d c *
        ((ρ t g) c d * conj ((ρ s g) a b))) μ := by
    intro a b c d
    have h_gdep : Integrable (fun g => (ρ t g) c d * conj ((ρ s g) a b)) μ :=
      hInt t s c d a b
    exact (h_gdep.smul ((ρ s A) a b * (ρ t B) d c)).congr
      (Filter.Eventually.of_forall (fun g => by
        simp only [Pi.smul_def, smul_eq_mul]))
  have hInt_d : ∀ (a : Fin (dims s)) (c : Fin (dims t)) (b : Fin (dims s)),
      Integrable (fun g => ∑ d : Fin (dims t),
        (ρ s A) a b * (ρ t B) d c *
        ((ρ t g) c d * conj ((ρ s g) a b))) μ :=
    fun a c b => integrable_finsetSum Finset.univ (fun d _ => hInt_term a b c d)
  have hInt_b : ∀ (a : Fin (dims s)) (c : Fin (dims t)),
      Integrable (fun g => ∑ b : Fin (dims s), ∑ d : Fin (dims t),
        (ρ s A) a b * (ρ t B) d c *
        ((ρ t g) c d * conj ((ρ s g) a b))) μ :=
    fun a c => integrable_finsetSum Finset.univ (fun b _ => hInt_d a c b)
  have hInt_c : ∀ (a : Fin (dims s)),
      Integrable (fun g => ∑ c : Fin (dims t), ∑ b : Fin (dims s), ∑ d : Fin (dims t),
        (ρ s A) a b * (ρ t B) d c *
        ((ρ t g) c d * conj ((ρ s g) a b))) μ :=
    fun a => integrable_finsetSum Finset.univ (fun c _ => hInt_b a c)
  have hInt_sum : Integrable (fun g =>
      ∑ a : Fin (dims s), ∑ c : Fin (dims t),
        ∑ b : Fin (dims s), ∑ d : Fin (dims t),
          (ρ s A) a b * (ρ t B) d c *
          ((ρ t g) c d * conj ((ρ s g) a b))) μ :=
    integrable_finsetSum Finset.univ (fun a _ => hInt_c a)
  exact hInt_sum.congr (Filter.Eventually.of_forall (fun g => (hprod_expand g).symm))

#print axioms char_product_integrable
