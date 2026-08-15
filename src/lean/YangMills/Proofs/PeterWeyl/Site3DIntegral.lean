/-
# Peter-Weyl: Single-Site 3D Luscher Integral
-/

import YangMills.Proofs.PeterWeyl.TripleProduct

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open Finset
open Matrix
open MeasureTheory
open scoped ComplexConjugate

namespace YangMills

/-- **Integrability of a 4-ME product (1 unbarred × 3 barred).** General version of the
`hInt_4ME` step from `single_site_3D_luscher_integral`: for any representations `σ, t₁, t₂, t₃`
and any indices, the product `(ρ_σ g)_{pq} · conj((ρ_{t₁} g)_{c₁d₁}) · conj((ρ_{t₂} g)_{c₂d₂}) · conj((ρ_{t₃} g)_{c₃d₃})`
is integrable w.r.t. the Haar probability measure.

Proof: expand the 3 barred MEs via `cgME_decomp_3fold_conj` (pointwise identity), then each
leaf is `(ρ_σ g)_{pq} · conj((ρ_β g)_{p'q'})` times a CG coefficient, which is integrable by
`characterOrthogonality` (`hInt`). The finite sum is integrable by `integrable_finsetSum`.
0 sorries, 0 new axioms. -/
lemma integrable_ME_times_3barred_MEs
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
    Integrable (fun g => (ρ σ g) p q *
        (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3))) μ := by
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  -- Pointwise identity: expand 3 barred MEs via cgME_decomp_3fold_conj
  have hpt_barred : ∀ (g : G),
      conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3) =
      ∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
        ∑ β : ι, ∑ p' : Fin (dims β), ∑ q' : Fin (dims β),
          conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
          conj (cgME ν' t3 β r' c3 p') * conj ((ρ β g) p' q') * cgME ν' t3 β s' d3 q' := by
    intro g
    exact cgME_decomp_3fold_conj ι dims ρ cgME hcgME_decomp t1 t2 t3 g c1 d1 c2 d2 c3 d3
  -- Rewrite the function using the expansion
  rw [show (fun g => (ρ σ g) p q *
        (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3))) =
      (fun g => ∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
        ∑ β : ι, ∑ p' : Fin (dims β), ∑ q' : Fin (dims β),
          conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
          conj (cgME ν' t3 β r' c3 p') * cgME ν' t3 β s' d3 q' *
          ((ρ σ g) p q * conj ((ρ β g) p' q'))) from by
    funext g
    rw [hpt_barred g, Finset.mul_sum]
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
    ring]
  -- Integrability of each leaf: (CG coeff) * ((ρ σ g) p q * conj ((ρ β g) p' q'))
  apply integrable_finsetSum Finset.univ
  intro ν' _
  apply integrable_finsetSum Finset.univ
  intro r' _
  apply integrable_finsetSum Finset.univ
  intro s' _
  apply integrable_finsetSum Finset.univ
  intro β _
  apply integrable_finsetSum Finset.univ
  intro p' _
  apply integrable_finsetSum Finset.univ
  intro q' _
  exact Integrable.smul
    (conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
     conj (cgME ν' t3 β r' c3 p') * cgME ν' t3 β s' d3 q')
    (hInt σ β p q p' q')

#print axioms integrable_ME_times_3barred_MEs
#print axioms integrable_ME_times_3barred_MEs

/-- **Integrability of a 6-ME product (3 unbarred × 3 barred).** For any representations
`s₁, s₂, s₃, t₁, t₂, t₃` and any indices, the product of 3 unbarred matrix elements times
3 barred matrix elements (as arises in the 3D Lüscher integral) is integrable w.r.t. the Haar
probability measure.

Proof: decompose the 3 unbarred MEs via `cgME_decomp_3fold` (pointwise identity), then each
leaf is `(ρ_α g)_{pq} · (3 barred MEs)` times a CG coefficient, which is integrable by
`integrable_ME_times_3barred_MEs`. The finite sum is integrable by `integrable_finsetSum`.
0 sorries, 0 new axioms. -/
lemma integrable_6ME_product
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
    (s1 s2 s3 : ι) (a1 b1 : Fin (dims s1)) (a2 b2 : Fin (dims s2)) (a3 b3 : Fin (dims s3))
    (t1 t2 t3 : ι) (c1 d1 : Fin (dims t1)) (c2 d2 : Fin (dims t2)) (c3 d3 : Fin (dims t3)) :
    Integrable (fun g =>
      (ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 * (ρ s3 g) a3 b3 *
      conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3)) μ := by
  -- Pointwise identity: apply cgME_decomp_3fold to the 3 unbarred MEs, distribute barred product
  have hpt : ∀ (g : G),
      (ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 * (ρ s3 g) a3 b3 *
      conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3) =
      ∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν),
        ∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        (cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
         cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q)) *
        ((ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
         conj ((ρ t3 g) c3 d3))) := by
    intro g
    have hreassoc : (ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 * (ρ s3 g) a3 b3 *
        conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3) =
        ((ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 * (ρ s3 g) a3 b3) *
        (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3)) := by ring
    rw [hreassoc, cgME_decomp_3fold ι dims ρ cgME hcgME_decomp s1 s2 s3 g a1 b1 a2 b2 a3 b3]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ν _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro α _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q _
    ring
  -- Rewrite the function using the expansion
  rw [show (fun g =>
        (ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 * (ρ s3 g) a3 b3 *
        conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3)) =
      (fun g => ∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν),
        ∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        (cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
         cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q)) *
        ((ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
         conj ((ρ t3 g) c3 d3)))) from by
    funext g; exact hpt g]
  -- Integrability of each leaf: (CG coeff) * ((ρ α g) p q * (3 barred MEs))
  apply integrable_finsetSum Finset.univ
  intro ν _
  apply integrable_finsetSum Finset.univ
  intro r _
  apply integrable_finsetSum Finset.univ
  intro s _
  apply integrable_finsetSum Finset.univ
  intro α _
  apply integrable_finsetSum Finset.univ
  intro p _
  apply integrable_finsetSum Finset.univ
  intro q _
  exact Integrable.smul
    (cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
     cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q))
    (integrable_ME_times_3barred_MEs μ ι dims hDims ρ hU hIrr cgME hcgME_decomp
      α p q t1 t2 t3 c1 d1 c2 d2 c3 d3)
#print axioms integrable_6ME_product
#print axioms integrable_6ME_product

set_option maxHeartbeats 20000000 in
/-- **Character-level single-site 3D Lüscher integral.** The integral of a product of 6
characters — 3 unbarred `χ_{sᵢ}(g·Aᵢ)` and 3 barred `χ_{tⱼ}(g⁻¹·Bⱼ)` — over the Haar measure
equals a sum over all matrix-element indices of the constant (product of `ρ(A)` and `ρ(B)`
matrix elements) times the 6-ME integral (evaluated by `single_site_3D_luscher_integral`).

This is the key building block for the 3D global cascade: it converts the character-level
integral (which arises from the plaquette-level character expansion of the interface
Boltzmann factor) into a sum of matrix-element-level integrals, each of which is evaluated
by `single_site_3D_luscher_integral`. The result is a sum of CG-coefficient products times
`(1/dims α)`, which (in the diagonal case) gives `|C|² ≥ 0` by `cg_unitarity_nonneg`.

Proof: expand each character as a trace (using `Matrix.trace` + `repMatrixElement_inv` for
the barred characters), distribute the product into a 12-fold sum, exchange the sums with the
integral (justified by `integrable_6ME_product`), and apply `single_site_3D_luscher_integral`
to each 6-ME integral. 0 sorries, 0 new axioms. -/
lemma char_level_single_site_3D_integral
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
    (s1 s2 s3 t1 t2 t3 : ι) (A1 A2 A3 B1 B2 B3 : G) :
    ∫ g, repCharacter (ρ s1) (g * A1) * repCharacter (ρ s2) (g * A2) *
        repCharacter (ρ s3) (g * A3) * repCharacter (ρ t1) (g⁻¹ * B1) *
        repCharacter (ρ t2) (g⁻¹ * B2) * repCharacter (ρ t3) (g⁻¹ * B3) ∂μ =
      ∑ a1 : Fin (dims s1), ∑ b1 : Fin (dims s1),
      ∑ a2 : Fin (dims s2), ∑ b2 : Fin (dims s2),
      ∑ a3 : Fin (dims s3), ∑ b3 : Fin (dims s3),
      ∑ c1 : Fin (dims t1), ∑ d1 : Fin (dims t1),
      ∑ c2 : Fin (dims t2), ∑ d2 : Fin (dims t2),
      ∑ c3 : Fin (dims t3), ∑ d3 : Fin (dims t3),
        (ρ s1 A1) b1 a1 * (ρ s2 A2) b2 a2 * (ρ s3 A3) b3 a3 *
        (ρ t1 B1) d1 c1 * (ρ t2 B2) d2 c2 * (ρ t3 B3) d3 c3 *
        ∫ g, (ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 * (ρ s3 g) a3 b3 *
          conj ((ρ t1 g) d1 c1) * conj ((ρ t2 g) d2 c2) * conj ((ρ t3 g) d3 c3) ∂μ := by
  -- htrace_mul helper: Matrix.trace (A * B) = ∑ i, ∑ j, A i j * B j i
  have htrace_mul : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ),
      Matrix.trace (A * B) = ∑ i : Fin n, ∑ j : Fin n, A i j * B j i := by
    intro n A B; simp [Matrix.trace, Matrix.mul_apply]
  -- Character expansions (unbarred): χ_s(g·A) = ∑ a, ∑ b, (ρ s g) a b * (ρ s A) b a
  have hchar_s1 : ∀ (g : G),
      repCharacter (ρ s1) (g * A1) =
      ∑ a1 : Fin (dims s1), ∑ b1 : Fin (dims s1), (ρ s1 g) a1 b1 * (ρ s1 A1) b1 a1 := by
    intro g; rw [repCharacter, MonoidHom.map_mul, htrace_mul]
  have hchar_s2 : ∀ (g : G),
      repCharacter (ρ s2) (g * A2) =
      ∑ a2 : Fin (dims s2), ∑ b2 : Fin (dims s2), (ρ s2 g) a2 b2 * (ρ s2 A2) b2 a2 := by
    intro g; rw [repCharacter, MonoidHom.map_mul, htrace_mul]
  have hchar_s3 : ∀ (g : G),
      repCharacter (ρ s3) (g * A3) =
      ∑ a3 : Fin (dims s3), ∑ b3 : Fin (dims s3), (ρ s3 g) a3 b3 * (ρ s3 A3) b3 a3 := by
    intro g; rw [repCharacter, MonoidHom.map_mul, htrace_mul]
  -- Character expansions (barred): χ_t(g⁻¹·B) = ∑ c, ∑ d, conj((ρ t g) d c) * (ρ t B) d c
  have hchar_t1 : ∀ (g : G),
      repCharacter (ρ t1) (g⁻¹ * B1) =
      ∑ c1 : Fin (dims t1), ∑ d1 : Fin (dims t1), conj ((ρ t1 g) d1 c1) * (ρ t1 B1) d1 c1 := by
    intro g; rw [repCharacter, MonoidHom.map_mul, htrace_mul]
    apply Finset.sum_congr rfl; intro c1 _; apply Finset.sum_congr rfl; intro d1 _
    rw [repMatrixElement_inv (ρ t1) (hU t1) g c1 d1]
  have hchar_t2 : ∀ (g : G),
      repCharacter (ρ t2) (g⁻¹ * B2) =
      ∑ c2 : Fin (dims t2), ∑ d2 : Fin (dims t2), conj ((ρ t2 g) d2 c2) * (ρ t2 B2) d2 c2 := by
    intro g; rw [repCharacter, MonoidHom.map_mul, htrace_mul]
    apply Finset.sum_congr rfl; intro c2 _; apply Finset.sum_congr rfl; intro d2 _
    rw [repMatrixElement_inv (ρ t2) (hU t2) g c2 d2]
  have hchar_t3 : ∀ (g : G),
      repCharacter (ρ t3) (g⁻¹ * B3) =
      ∑ c3 : Fin (dims t3), ∑ d3 : Fin (dims t3), conj ((ρ t3 g) d3 c3) * (ρ t3 B3) d3 c3 := by
    intro g; rw [repCharacter, MonoidHom.map_mul, htrace_mul]
    apply Finset.sum_congr rfl; intro c3 _; apply Finset.sum_congr rfl; intro d3 _
    rw [repMatrixElement_inv (ρ t3) (hU t3) g c3 d3]
  -- Pointwise identity: expand characters, distribute product into 12-level sum
  have hpt : ∀ (g : G),
      repCharacter (ρ s1) (g * A1) * repCharacter (ρ s2) (g * A2) *
      repCharacter (ρ s3) (g * A3) * repCharacter (ρ t1) (g⁻¹ * B1) *
      repCharacter (ρ t2) (g⁻¹ * B2) * repCharacter (ρ t3) (g⁻¹ * B3) =
      ∑ a1 : Fin (dims s1), ∑ b1 : Fin (dims s1),
      ∑ a2 : Fin (dims s2), ∑ b2 : Fin (dims s2),
      ∑ a3 : Fin (dims s3), ∑ b3 : Fin (dims s3),
      ∑ c1 : Fin (dims t1), ∑ d1 : Fin (dims t1),
      ∑ c2 : Fin (dims t2), ∑ d2 : Fin (dims t2),
      ∑ c3 : Fin (dims t3), ∑ d3 : Fin (dims t3),
        (ρ s1 A1) b1 a1 * (ρ s2 A2) b2 a2 * (ρ s3 A3) b3 a3 *
        (ρ t1 B1) d1 c1 * (ρ t2 B2) d2 c2 * (ρ t3 B3) d3 c3 *
        ((ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 * (ρ s3 g) a3 b3 *
         conj ((ρ t1 g) d1 c1) * conj ((ρ t2 g) d2 c2) * conj ((ρ t3 g) d3 c3)) := by
    intro g
    have hreassoc :
        repCharacter (ρ s1) (g * A1) * repCharacter (ρ s2) (g * A2) *
        repCharacter (ρ s3) (g * A3) * repCharacter (ρ t1) (g⁻¹ * B1) *
        repCharacter (ρ t2) (g⁻¹ * B2) * repCharacter (ρ t3) (g⁻¹ * B3) =
        repCharacter (ρ s1) (g * A1) * (repCharacter (ρ s2) (g * A2) *
        (repCharacter (ρ s3) (g * A3) * (repCharacter (ρ t1) (g⁻¹ * B1) *
        (repCharacter (ρ t2) (g⁻¹ * B2) * repCharacter (ρ t3) (g⁻¹ * B3))))) := by ring
    rw [hreassoc, hchar_s1, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro a1 _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro b1 _
    rw [hchar_s2, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a2 _
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro b2 _
    rw [hchar_s3, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a3 _
    rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro b3 _
    rw [hchar_t1, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro c1 _
    rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro d1 _
    rw [hchar_t2, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro c2 _
    rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro d2 _
    rw [hchar_t3, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro c3 _
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro d3 _
    ring
  -- Rewrite the integral using hpt
  rw [show (∫ g, repCharacter (ρ s1) (g * A1) * repCharacter (ρ s2) (g * A2) *
        repCharacter (ρ s3) (g * A3) * repCharacter (ρ t1) (g⁻¹ * B1) *
        repCharacter (ρ t2) (g⁻¹ * B2) * repCharacter (ρ t3) (g⁻¹ * B3) ∂μ) =
      (∫ g, ∑ a1 : Fin (dims s1), ∑ b1 : Fin (dims s1),
        ∑ a2 : Fin (dims s2), ∑ b2 : Fin (dims s2),
        ∑ a3 : Fin (dims s3), ∑ b3 : Fin (dims s3),
        ∑ c1 : Fin (dims t1), ∑ d1 : Fin (dims t1),
        ∑ c2 : Fin (dims t2), ∑ d2 : Fin (dims t2),
        ∑ c3 : Fin (dims t3), ∑ d3 : Fin (dims t3),
          (ρ s1 A1) b1 a1 * (ρ s2 A2) b2 a2 * (ρ s3 A3) b3 a3 *
          (ρ t1 B1) d1 c1 * (ρ t2 B2) d2 c2 * (ρ t3 B3) d3 c3 *
          ((ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 * (ρ s3 g) a3 b3 *
           conj ((ρ t1 g) d1 c1) * conj ((ρ t2 g) d2 c2) * conj ((ρ t3 g) d3 c3)) ∂μ) from by
    congr 1 with g; exact hpt g]
  -- Exchange the 12 sums with the integral (12 levels of integral_finsetSum)
  rw [integral_finsetSum Finset.univ (fun a1 _ => by
    apply integrable_finsetSum Finset.univ; intro b1 _; apply integrable_finsetSum Finset.univ; intro a2 _
    apply integrable_finsetSum Finset.univ; intro b2 _; apply integrable_finsetSum Finset.univ; intro a3 _
    apply integrable_finsetSum Finset.univ; intro b3 _; apply integrable_finsetSum Finset.univ; intro c1 _
    apply integrable_finsetSum Finset.univ; intro d1 _; apply integrable_finsetSum Finset.univ; intro c2 _
    apply integrable_finsetSum Finset.univ; intro d2 _; apply integrable_finsetSum Finset.univ; intro c3 _
    apply integrable_finsetSum Finset.univ; intro d3 _
    exact Integrable.smul
      ((ρ s1 A1) b1 a1 * (ρ s2 A2) b2 a2 * (ρ s3 A3) b3 a3 *
       (ρ t1 B1) d1 c1 * (ρ t2 B2) d2 c2 * (ρ t3 B3) d3 c3)
      (integrable_6ME_product μ ι dims hDims ρ hU hIrr cgME hcgME_decomp
        s1 s2 s3 a1 b1 a2 b2 a3 b3 t1 t2 t3 d1 c1 d2 c2 d3 c3))]
  apply Finset.sum_congr rfl; intro a1 _
  rw [integral_finsetSum Finset.univ (fun b1 _ => by
    apply integrable_finsetSum Finset.univ; intro a2 _; apply integrable_finsetSum Finset.univ; intro b2 _
    apply integrable_finsetSum Finset.univ; intro a3 _; apply integrable_finsetSum Finset.univ; intro b3 _
    apply integrable_finsetSum Finset.univ; intro c1 _; apply integrable_finsetSum Finset.univ; intro d1 _
    apply integrable_finsetSum Finset.univ; intro c2 _; apply integrable_finsetSum Finset.univ; intro d2 _
    apply integrable_finsetSum Finset.univ; intro c3 _; apply integrable_finsetSum Finset.univ; intro d3 _
    exact Integrable.smul
      ((ρ s1 A1) b1 a1 * (ρ s2 A2) b2 a2 * (ρ s3 A3) b3 a3 *
       (ρ t1 B1) d1 c1 * (ρ t2 B2) d2 c2 * (ρ t3 B3) d3 c3)
      (integrable_6ME_product μ ι dims hDims ρ hU hIrr cgME hcgME_decomp
        s1 s2 s3 a1 b1 a2 b2 a3 b3 t1 t2 t3 d1 c1 d2 c2 d3 c3))]
  apply Finset.sum_congr rfl; intro b1 _
  rw [integral_finsetSum Finset.univ (fun a2 _ => by
    apply integrable_finsetSum Finset.univ; intro b2 _; apply integrable_finsetSum Finset.univ; intro a3 _
    apply integrable_finsetSum Finset.univ; intro b3 _; apply integrable_finsetSum Finset.univ; intro c1 _
    apply integrable_finsetSum Finset.univ; intro d1 _; apply integrable_finsetSum Finset.univ; intro c2 _
    apply integrable_finsetSum Finset.univ; intro d2 _; apply integrable_finsetSum Finset.univ; intro c3 _
    apply integrable_finsetSum Finset.univ; intro d3 _
    exact Integrable.smul
      ((ρ s1 A1) b1 a1 * (ρ s2 A2) b2 a2 * (ρ s3 A3) b3 a3 *
       (ρ t1 B1) d1 c1 * (ρ t2 B2) d2 c2 * (ρ t3 B3) d3 c3)
      (integrable_6ME_product μ ι dims hDims ρ hU hIrr cgME hcgME_decomp
        s1 s2 s3 a1 b1 a2 b2 a3 b3 t1 t2 t3 d1 c1 d2 c2 d3 c3))]
  apply Finset.sum_congr rfl; intro a2 _
  rw [integral_finsetSum Finset.univ (fun b2 _ => by
    apply integrable_finsetSum Finset.univ; intro a3 _; apply integrable_finsetSum Finset.univ; intro b3 _
    apply integrable_finsetSum Finset.univ; intro c1 _; apply integrable_finsetSum Finset.univ; intro d1 _
    apply integrable_finsetSum Finset.univ; intro c2 _; apply integrable_finsetSum Finset.univ; intro d2 _
    apply integrable_finsetSum Finset.univ; intro c3 _; apply integrable_finsetSum Finset.univ; intro d3 _
    exact Integrable.smul
      ((ρ s1 A1) b1 a1 * (ρ s2 A2) b2 a2 * (ρ s3 A3) b3 a3 *
       (ρ t1 B1) d1 c1 * (ρ t2 B2) d2 c2 * (ρ t3 B3) d3 c3)
      (integrable_6ME_product μ ι dims hDims ρ hU hIrr cgME hcgME_decomp
        s1 s2 s3 a1 b1 a2 b2 a3 b3 t1 t2 t3 d1 c1 d2 c2 d3 c3))]
  apply Finset.sum_congr rfl; intro b2 _
  rw [integral_finsetSum Finset.univ (fun a3 _ => by
    apply integrable_finsetSum Finset.univ; intro b3 _; apply integrable_finsetSum Finset.univ; intro c1 _
    apply integrable_finsetSum Finset.univ; intro d1 _; apply integrable_finsetSum Finset.univ; intro c2 _
    apply integrable_finsetSum Finset.univ; intro d2 _; apply integrable_finsetSum Finset.univ; intro c3 _
    apply integrable_finsetSum Finset.univ; intro d3 _
    exact Integrable.smul
      ((ρ s1 A1) b1 a1 * (ρ s2 A2) b2 a2 * (ρ s3 A3) b3 a3 *
       (ρ t1 B1) d1 c1 * (ρ t2 B2) d2 c2 * (ρ t3 B3) d3 c3)
      (integrable_6ME_product μ ι dims hDims ρ hU hIrr cgME hcgME_decomp
        s1 s2 s3 a1 b1 a2 b2 a3 b3 t1 t2 t3 d1 c1 d2 c2 d3 c3))]
  apply Finset.sum_congr rfl; intro a3 _
  rw [integral_finsetSum Finset.univ (fun b3 _ => by
    apply integrable_finsetSum Finset.univ; intro c1 _; apply integrable_finsetSum Finset.univ; intro d1 _
    apply integrable_finsetSum Finset.univ; intro c2 _; apply integrable_finsetSum Finset.univ; intro d2 _
    apply integrable_finsetSum Finset.univ; intro c3 _; apply integrable_finsetSum Finset.univ; intro d3 _
    exact Integrable.smul
      ((ρ s1 A1) b1 a1 * (ρ s2 A2) b2 a2 * (ρ s3 A3) b3 a3 *
       (ρ t1 B1) d1 c1 * (ρ t2 B2) d2 c2 * (ρ t3 B3) d3 c3)
      (integrable_6ME_product μ ι dims hDims ρ hU hIrr cgME hcgME_decomp
        s1 s2 s3 a1 b1 a2 b2 a3 b3 t1 t2 t3 d1 c1 d2 c2 d3 c3))]
  apply Finset.sum_congr rfl; intro b3 _
  rw [integral_finsetSum Finset.univ (fun c1 _ => by
    apply integrable_finsetSum Finset.univ; intro d1 _; apply integrable_finsetSum Finset.univ; intro c2 _
    apply integrable_finsetSum Finset.univ; intro d2 _; apply integrable_finsetSum Finset.univ; intro c3 _
    apply integrable_finsetSum Finset.univ; intro d3 _
    exact Integrable.smul
      ((ρ s1 A1) b1 a1 * (ρ s2 A2) b2 a2 * (ρ s3 A3) b3 a3 *
       (ρ t1 B1) d1 c1 * (ρ t2 B2) d2 c2 * (ρ t3 B3) d3 c3)
      (integrable_6ME_product μ ι dims hDims ρ hU hIrr cgME hcgME_decomp
        s1 s2 s3 a1 b1 a2 b2 a3 b3 t1 t2 t3 d1 c1 d2 c2 d3 c3))]
  apply Finset.sum_congr rfl; intro c1 _
  rw [integral_finsetSum Finset.univ (fun d1 _ => by
    apply integrable_finsetSum Finset.univ; intro c2 _; apply integrable_finsetSum Finset.univ; intro d2 _
    apply integrable_finsetSum Finset.univ; intro c3 _; apply integrable_finsetSum Finset.univ; intro d3 _
    exact Integrable.smul
      ((ρ s1 A1) b1 a1 * (ρ s2 A2) b2 a2 * (ρ s3 A3) b3 a3 *
       (ρ t1 B1) d1 c1 * (ρ t2 B2) d2 c2 * (ρ t3 B3) d3 c3)
      (integrable_6ME_product μ ι dims hDims ρ hU hIrr cgME hcgME_decomp
        s1 s2 s3 a1 b1 a2 b2 a3 b3 t1 t2 t3 d1 c1 d2 c2 d3 c3))]
  apply Finset.sum_congr rfl; intro d1 _
  rw [integral_finsetSum Finset.univ (fun c2 _ => by
    apply integrable_finsetSum Finset.univ; intro d2 _; apply integrable_finsetSum Finset.univ; intro c3 _
    apply integrable_finsetSum Finset.univ; intro d3 _
    exact Integrable.smul
      ((ρ s1 A1) b1 a1 * (ρ s2 A2) b2 a2 * (ρ s3 A3) b3 a3 *
       (ρ t1 B1) d1 c1 * (ρ t2 B2) d2 c2 * (ρ t3 B3) d3 c3)
      (integrable_6ME_product μ ι dims hDims ρ hU hIrr cgME hcgME_decomp
        s1 s2 s3 a1 b1 a2 b2 a3 b3 t1 t2 t3 d1 c1 d2 c2 d3 c3))]
  apply Finset.sum_congr rfl; intro c2 _
  rw [integral_finsetSum Finset.univ (fun d2 _ => by
    apply integrable_finsetSum Finset.univ; intro c3 _; apply integrable_finsetSum Finset.univ; intro d3 _
    exact Integrable.smul
      ((ρ s1 A1) b1 a1 * (ρ s2 A2) b2 a2 * (ρ s3 A3) b3 a3 *
       (ρ t1 B1) d1 c1 * (ρ t2 B2) d2 c2 * (ρ t3 B3) d3 c3)
      (integrable_6ME_product μ ι dims hDims ρ hU hIrr cgME hcgME_decomp
        s1 s2 s3 a1 b1 a2 b2 a3 b3 t1 t2 t3 d1 c1 d2 c2 d3 c3))]
  apply Finset.sum_congr rfl; intro d2 _
  rw [integral_finsetSum Finset.univ (fun c3 _ => by
    apply integrable_finsetSum Finset.univ; intro d3 _
    exact Integrable.smul
      ((ρ s1 A1) b1 a1 * (ρ s2 A2) b2 a2 * (ρ s3 A3) b3 a3 *
       (ρ t1 B1) d1 c1 * (ρ t2 B2) d2 c2 * (ρ t3 B3) d3 c3)
      (integrable_6ME_product μ ι dims hDims ρ hU hIrr cgME hcgME_decomp
        s1 s2 s3 a1 b1 a2 b2 a3 b3 t1 t2 t3 d1 c1 d2 c2 d3 c3))]
  apply Finset.sum_congr rfl; intro c3 _
  rw [integral_finsetSum Finset.univ (fun d3 _ => by
    exact Integrable.smul
      ((ρ s1 A1) b1 a1 * (ρ s2 A2) b2 a2 * (ρ s3 A3) b3 a3 *
       (ρ t1 B1) d1 c1 * (ρ t2 B2) d2 c2 * (ρ t3 B3) d3 c3)
      (integrable_6ME_product μ ι dims hDims ρ hU hIrr cgME hcgME_decomp
        s1 s2 s3 a1 b1 a2 b2 a3 b3 t1 t2 t3 d1 c1 d2 c2 d3 c3))]
  apply Finset.sum_congr rfl; intro d3 _
  -- Pull the constant out of the integral
  rw [integral_const_mul]
#print axioms char_level_single_site_3D_integral

set_option maxHeartbeats 1000000 in
/-- **Single-site 3D Lüscher integral (Step 2 of the Lüscher roadmap, §8.11.41–42).**

For irreducible unitary representations of a compact group with normalized Haar measure, the
integral of 3 unbarred matrix elements times 3 barred matrix elements (as arises at each site
when integrating out a temporal link `u_t(x)` in 3D) equals a sum over the combined representation
`α` of `(1/dims α)` times the product of the unbarred and barred CG coefficients:

    ∫ (ρ_{s₁} g)_{a₁b₁} · (ρ_{s₂} g)_{a₂b₂} · (ρ_{s₃} g)_{a₃b₃}
        · conj((ρ_{t₁} g)_{c₁d₁}) · conj((ρ_{t₂} g)_{c₂d₂}) · conj((ρ_{t₃} g)_{c₃d₃}) dμ(g)
      = ∑_{ν,r,s,α,p,q} CG_unbarred(ν,r,s,α,p,q) · (1/dims α) · ∑_{ν',r',s'} CG_barred(ν',r',s',α,p,q)

Proof: apply `cgME_decomp_3fold` to the 3 unbarred MEs (6 sums), exchange sums with integral
(Fubini), then evaluate each inner integral `∫ (ρ_α g)_{pq} · [3 barred MEs] dμ` using
`integral_ME_times_3barred_MEs` (which applies `cgME_decomp_3fold_conj` + Schur orthogonality).
The local coefficient is `CG_unbarred(α) · CG_barred(α)` (NOT necessarily ≥ 0 locally — the
non-negativity comes from the GLOBAL cascade in Step 3). 0 sorries, 0 new axioms. -/
lemma single_site_3D_luscher_integral
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
    (s1 s2 s3 : ι) (a1 b1 : Fin (dims s1)) (a2 b2 : Fin (dims s2)) (a3 b3 : Fin (dims s3))
    (t1 t2 t3 : ι) (c1 d1 : Fin (dims t1)) (c2 d2 : Fin (dims t2)) (c3 d3 : Fin (dims t3)) :
    ∫ g, (ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 * (ρ s3 g) a3 b3 *
        conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3) ∂μ =
      ∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν),
        ∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        (cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
         cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q)) *
        ((1 / dims α : ℂ) *
         ∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
           conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
           conj (cgME ν' t3 α r' c3 p) * cgME ν' t3 α s' d3 q) := by
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  -- Integrability of the 4-ME product (1 unbarred × 3 barred) via CG decomposition of barred MEs
  have hInt_4ME : ∀ (α : ι) (p : Fin (dims α)) (q : Fin (dims α)),
      Integrable (fun g => (ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
        conj ((ρ t3 g) c3 d3))) μ := by
    intro α p q
    have hpt_barred : ∀ (g : G),
        conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3) =
        ∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
          ∑ β : ι, ∑ p' : Fin (dims β), ∑ q' : Fin (dims β),
            conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
            conj (cgME ν' t3 β r' c3 p') * conj ((ρ β g) p' q') * cgME ν' t3 β s' d3 q' := by
      intro g
      exact cgME_decomp_3fold_conj ι dims ρ cgME hcgME_decomp t1 t2 t3 g c1 d1 c2 d2 c3 d3
    rw [show (fun g => (ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
        conj ((ρ t3 g) c3 d3))) =
        (fun g => ∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
          ∑ β : ι, ∑ p' : Fin (dims β), ∑ q' : Fin (dims β),
            conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
            conj (cgME ν' t3 β r' c3 p') * cgME ν' t3 β s' d3 q' *
            ((ρ α g) p q * conj ((ρ β g) p' q'))) from by
      funext g
      rw [hpt_barred g, Finset.mul_sum]
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
      ring]
    apply integrable_finsetSum Finset.univ
    intro ν' _
    apply integrable_finsetSum Finset.univ
    intro r' _
    apply integrable_finsetSum Finset.univ
    intro s' _
    apply integrable_finsetSum Finset.univ
    intro β _
    apply integrable_finsetSum Finset.univ
    intro p' _
    apply integrable_finsetSum Finset.univ
    intro q' _
    exact Integrable.smul
      (conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
       conj (cgME ν' t3 β r' c3 p') * cgME ν' t3 β s' d3 q')
      (hInt α β p q p' q')
  -- Pointwise identity: apply cgME_decomp_3fold to the 3 unbarred MEs, distribute barred product
  have hpt : ∀ (g : G),
      (ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 * (ρ s3 g) a3 b3 *
      conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3) =
      ∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν),
        ∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        (cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
         cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q)) *
        ((ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
         conj ((ρ t3 g) c3 d3))) := by
    intro g
    have hreassoc : (ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 * (ρ s3 g) a3 b3 *
        conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3) =
        ((ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 * (ρ s3 g) a3 b3) *
        (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3)) := by ring
    rw [hreassoc, cgME_decomp_3fold ι dims ρ cgME hcgME_decomp s1 s2 s3 g a1 b1 a2 b2 a3 b3]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ν _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro α _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q _
    ring
  -- Rewrite the integral using the pointwise identity
  rw [show (∫ g, (ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 * (ρ s3 g) a3 b3 *
        conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) * conj ((ρ t3 g) c3 d3) ∂μ) =
        ∫ g, (∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν),
          ∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
          (cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
           cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q)) *
          ((ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
           conj ((ρ t3 g) c3 d3)))) ∂μ from by
    congr 1 with g; exact hpt g]
  -- Per-term integrability (6 levels, using hInt_4ME)
  have hInt_term : ∀ (ν : ι) (r : Fin (dims ν)) (s : Fin (dims ν)) (α : ι)
      (p : Fin (dims α)) (q : Fin (dims α)),
      Integrable (fun g =>
        (cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
         cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q)) *
        ((ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
         conj ((ρ t3 g) c3 d3)))) μ := by
    intro ν r s α p q
    exact Integrable.smul
      (cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
       cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q))
      (hInt_4ME α p q)
  have hInt_q : ∀ (ν : ι) (r : Fin (dims ν)) (s : Fin (dims ν)) (α : ι) (p : Fin (dims α)),
      Integrable (fun g => ∑ q : Fin (dims α),
        (cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
         cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q)) *
        ((ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
         conj ((ρ t3 g) c3 d3)))) μ := by
    intro ν r s α p
    exact integrable_finsetSum Finset.univ (fun q _ => hInt_term ν r s α p q)
  have hInt_p : ∀ (ν : ι) (r : Fin (dims ν)) (s : Fin (dims ν)) (α : ι),
      Integrable (fun g => ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        (cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
         cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q)) *
        ((ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
         conj ((ρ t3 g) c3 d3)))) μ := by
    intro ν r s α
    exact integrable_finsetSum Finset.univ (fun p _ => hInt_q ν r s α p)
  have hInt_α : ∀ (ν : ι) (r : Fin (dims ν)) (s : Fin (dims ν)),
      Integrable (fun g => ∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        (cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
         cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q)) *
        ((ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
         conj ((ρ t3 g) c3 d3)))) μ := by
    intro ν r s
    exact integrable_finsetSum Finset.univ (fun α _ => hInt_p ν r s α)
  have hInt_s : ∀ (ν : ι) (r : Fin (dims ν)),
      Integrable (fun g => ∑ s : Fin (dims ν), ∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        (cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
         cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q)) *
        ((ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
         conj ((ρ t3 g) c3 d3)))) μ := by
    intro ν r
    exact integrable_finsetSum Finset.univ (fun s _ => hInt_α ν r s)
  have hInt_r : ∀ (ν : ι),
      Integrable (fun g => ∑ r : Fin (dims ν), ∑ s : Fin (dims ν), ∑ α : ι,
        ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        (cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
         cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q)) *
        ((ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
         conj ((ρ t3 g) c3 d3)))) μ := by
    intro ν
    exact integrable_finsetSum Finset.univ (fun r _ => hInt_s ν r)
  have hInt_ν : Integrable (fun g => ∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν),
        ∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        (cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
         cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q)) *
        ((ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
         conj ((ρ t3 g) c3 d3)))) μ := by
    exact integrable_finsetSum Finset.univ (fun ν _ => hInt_r ν)
  -- Exchange sums with integral (6 levels)
  rw [integral_finsetSum Finset.univ (fun ν _ => hInt_r ν)]
  rw [Finset.sum_congr rfl (fun ν _ => integral_finsetSum Finset.univ (fun r _ => hInt_s ν r))]
  rw [Finset.sum_congr rfl (fun ν _ => Finset.sum_congr rfl (fun r _ =>
      integral_finsetSum Finset.univ (fun s _ => hInt_α ν r s)))]
  rw [Finset.sum_congr rfl (fun ν _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl
      (fun s _ => integral_finsetSum Finset.univ (fun α _ => hInt_p ν r s α))))]
  rw [Finset.sum_congr rfl (fun ν _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl
      (fun s _ => Finset.sum_congr rfl (fun α _ => integral_finsetSum Finset.univ
        (fun p _ => hInt_q ν r s α p)))))]
  rw [Finset.sum_congr rfl (fun ν _ => Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl
      (fun s _ => Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun p _ =>
        integral_finsetSum Finset.univ (fun q _ => hInt_term ν r s α p q))))))]
  -- Evaluate each inner integral using the helper
  have hInt_eval : ∀ (ν : ι) (r : Fin (dims ν)) (s : Fin (dims ν)) (α : ι)
      (p : Fin (dims α)) (q : Fin (dims α)),
      ∫ g,
        (cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
         cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q)) *
        ((ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
         conj ((ρ t3 g) c3 d3))) ∂μ =
        (cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
         cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q)) *
        ((1 / dims α : ℂ) *
         ∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
           conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
           conj (cgME ν' t3 α r' c3 p) * cgME ν' t3 α s' d3 q) := by
    intro ν r s α p q
    rw [integral_const_mul,
        show ∫ g, (ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
            conj ((ρ t3 g) c3 d3)) ∂μ =
            ∫ g, (ρ α g) p q * conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) *
              conj ((ρ t3 g) c3 d3) ∂μ from by
          congr 1 with g; ring,
        integral_ME_times_3barred_MEs μ ι dims hDims ρ hU hIrr
      cgME hcgME_decomp α p q t1 t2 t3 c1 d1 c2 d2 c3 d3]
  rw [Finset.sum_congr rfl (fun ν _ => Finset.sum_congr rfl (fun r _ =>
      Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun α _ =>
        Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ =>
          hInt_eval ν r s α p q))))))]

#print axioms single_site_3D_luscher_integral

open scoped ComplexOrder in
/-- **CG unitarity non-negativity (Step 3a of Lüscher roadmap).** In the diagonal case
(barred indices = unbarred indices), the single-site 3D Lüscher integral gives
`∑_{α,p,q} (1/dims α) · |C(α,p,q)|² ≥ 0`, where `C(α,p,q) = ∑_{ν,r,s} CG_unbarred(ν,r,s,α,p,q)`.

This demonstrates the |C|² structure from CG unitarity: the diagonal case of
`single_site_3D_luscher_integral` gives a sum of `|C|²` terms with non-negative coefficients
`(1/dims α) > 0`, hence non-negative. 0 sorries, 0 new axioms. -/
lemma cg_unitarity_nonneg
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
    (s1 s2 s3 : ι) (a1 b1 : Fin (dims s1)) (a2 b2 : Fin (dims s2)) (a3 b3 : Fin (dims s3)) :
    0 ≤ ∫ g, (ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 * (ρ s3 g) a3 b3 *
        conj ((ρ s1 g) a1 b1) * conj ((ρ s2 g) a2 b2) * conj ((ρ s3 g) a3 b3) ∂μ := by
  -- Step 1: Apply single_site_3D_luscher_integral with diagonal args
  rw [single_site_3D_luscher_integral μ ι dims hDims ρ hU hIrr cgME hcgME_decomp
    s1 s2 s3 a1 b1 a2 b2 a3 b3 s1 s2 s3 a1 b1 a2 b2 a3 b3]
  -- Define U (unbarred CG product) for readability
  set U := fun (ν : ι) (r : Fin (dims ν)) (s : Fin (dims ν)) (α : ι) (p : Fin (dims α)) (q : Fin (dims α)) =>
    cgME s1 s2 ν a1 a2 r * conj (cgME s1 s2 ν b1 b2 s) *
    cgME ν s3 α r a3 p * conj (cgME ν s3 α s b3 q)
  -- Define C(α,p,q) = ∑_{ν,r,s} U(ν,r,s,α,p,q)
  let C (α : ι) (p : Fin (dims α)) (q : Fin (dims α)) : ℂ :=
    ∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν), U ν r s α p q
  -- Helper: conj pushes through products
  have hconj_mul : ∀ (a b : ℂ), conj (a * b) = conj a * conj b :=
    fun a b => map_mul (starRingEnd ℂ) a b
  -- Step 2: Show barred CG product = conj(U) pointwise (conj distribution over products)
  have hBU : ∀ (ν' : ι) (r' : Fin (dims ν')) (s' : Fin (dims ν')) (α : ι) (p : Fin (dims α)) (q : Fin (dims α)),
      conj (cgME s1 s2 ν' a1 a2 r') * cgME s1 s2 ν' b1 b2 s' *
      conj (cgME ν' s3 α r' a3 p) * cgME ν' s3 α s' b3 q =
      conj (U ν' r' s' α p q) := by
    intro ν' r' s' α p q
    simp only [U, hconj_mul, Complex.conj_conj]
  -- Step 3: Substitute barred = conj(U) in the goal
  simp only [hBU]
  -- Step 4: Show ∑_{ν',r',s'} conj(U') = conj(C) (conj distribution over sums + alpha-equivalence)
  have hsumB : ∀ (α : ι) (p : Fin (dims α)) (q : Fin (dims α)),
      ∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'), conj (U ν' r' s' α p q) = conj (C α p q) := by
    intro α p q
    have h1 : ∀ (ν' : ι) (r' : Fin (dims ν')),
        ∑ s' : Fin (dims ν'), conj (U ν' r' s' α p q) = conj (∑ s' : Fin (dims ν'), U ν' r' s' α p q) := by
      intro ν' r'; rw [← map_sum (starRingEnd ℂ) (fun s' => U ν' r' s' α p q) Finset.univ]
    have h2 : ∀ (ν' : ι),
        ∑ r' : Fin (dims ν'), conj (∑ s' : Fin (dims ν'), U ν' r' s' α p q) =
        conj (∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'), U ν' r' s' α p q) := by
      intro ν'; rw [← map_sum (starRingEnd ℂ) (fun r' => ∑ s' : Fin (dims ν'), U ν' r' s' α p q) Finset.univ]
    rw [Finset.sum_congr rfl (fun ν' _ => Finset.sum_congr rfl (fun r' _ => h1 ν' r'))]
    rw [Finset.sum_congr rfl (fun ν' _ => h2 ν')]
    rw [← map_sum (starRingEnd ℂ)
          (fun ν' => ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'), U ν' r' s' α p q) Finset.univ]
  -- Step 5: Substitute ∑ conj(U') = conj(C) in the goal
  simp only [hsumB]
  -- Step 6: Reorder ∑_{ν,r,s,α,p,q} → ∑_{α,p,q,ν,r,s} (9 swaps)
  rw [show (∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν), ∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) =
      (∑ ν : ι, ∑ r : Fin (dims ν), ∑ α : ι, ∑ s : Fin (dims ν), ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) from by
    exact Finset.sum_congr rfl (fun ν _ => Finset.sum_congr rfl (fun r _ => by rw [Finset.sum_comm]))]
  rw [show (∑ ν : ι, ∑ r : Fin (dims ν), ∑ α : ι, ∑ s : Fin (dims ν), ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) =
      (∑ ν : ι, ∑ α : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν), ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) from by
    exact Finset.sum_congr rfl (fun ν _ => by rw [Finset.sum_comm])]
  rw [Finset.sum_comm]
  rw [show (∑ α : ι, ∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν), ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) =
      (∑ α : ι, ∑ ν : ι, ∑ r : Fin (dims ν), ∑ p : Fin (dims α), ∑ s : Fin (dims ν), ∑ q : Fin (dims α),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) from by
    exact Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun ν _ =>
      Finset.sum_congr rfl (fun r _ => by rw [Finset.sum_comm])))]
  rw [show (∑ α : ι, ∑ ν : ι, ∑ r : Fin (dims ν), ∑ p : Fin (dims α), ∑ s : Fin (dims ν), ∑ q : Fin (dims α),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) =
      (∑ α : ι, ∑ ν : ι, ∑ p : Fin (dims α), ∑ r : Fin (dims ν), ∑ s : Fin (dims ν), ∑ q : Fin (dims α),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) from by
    exact Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun ν _ => by rw [Finset.sum_comm]))]
  rw [show (∑ α : ι, ∑ ν : ι, ∑ p : Fin (dims α), ∑ r : Fin (dims ν), ∑ s : Fin (dims ν), ∑ q : Fin (dims α),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) =
      (∑ α : ι, ∑ p : Fin (dims α), ∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν), ∑ q : Fin (dims α),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) from by
    exact Finset.sum_congr rfl (fun α _ => by rw [Finset.sum_comm])]
  rw [show (∑ α : ι, ∑ p : Fin (dims α), ∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν), ∑ q : Fin (dims α),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) =
      (∑ α : ι, ∑ p : Fin (dims α), ∑ ν : ι, ∑ r : Fin (dims ν), ∑ q : Fin (dims α), ∑ s : Fin (dims ν),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) from by
    exact Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun ν _ => Finset.sum_congr rfl (fun r _ => by rw [Finset.sum_comm]))))]
  rw [show (∑ α : ι, ∑ p : Fin (dims α), ∑ ν : ι, ∑ r : Fin (dims ν), ∑ q : Fin (dims α), ∑ s : Fin (dims ν),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) =
      (∑ α : ι, ∑ p : Fin (dims α), ∑ ν : ι, ∑ q : Fin (dims α), ∑ r : Fin (dims ν), ∑ s : Fin (dims ν),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) from by
    exact Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun ν _ => by rw [Finset.sum_comm])))]
  rw [show (∑ α : ι, ∑ p : Fin (dims α), ∑ ν : ι, ∑ q : Fin (dims α), ∑ r : Fin (dims ν), ∑ s : Fin (dims ν),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) =
      (∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α), ∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) from by
    exact Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun p _ => by rw [Finset.sum_comm]))]
  -- Step 7: Factor (1/dims α) * conj(C α p q) out of ∑_{ν,r,s} (3 Finset.sum_mul)
  rw [show (∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α), ∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν),
        U ν r s α p q * ((1 / dims α : ℂ) * conj (C α p q))) =
      (∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α), ∑ ν : ι, ∑ r : Fin (dims ν),
        (∑ s : Fin (dims ν), U ν r s α p q) * ((1 / dims α : ℂ) * conj (C α p q))) from by
    exact Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun ν _ =>
        Finset.sum_congr rfl (fun r _ => by rw [Finset.sum_mul])))))]
  rw [show (∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α), ∑ ν : ι, ∑ r : Fin (dims ν),
        (∑ s : Fin (dims ν), U ν r s α p q) * ((1 / dims α : ℂ) * conj (C α p q))) =
      (∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α), ∑ ν : ι,
        (∑ r : Fin (dims ν), ∑ s : Fin (dims ν), U ν r s α p q) * ((1 / dims α : ℂ) * conj (C α p q))) from by
    exact Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun ν _ => by rw [Finset.sum_mul]))))]
  rw [show (∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α), ∑ ν : ι,
        (∑ r : Fin (dims ν), ∑ s : Fin (dims ν), U ν r s α p q) * ((1 / dims α : ℂ) * conj (C α p q))) =
      (∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        (∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν), U ν r s α p q) * ((1 / dims α : ℂ) * conj (C α p q))) from by
    exact Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun q _ => by rw [Finset.sum_mul])))]
  -- Step 8: Substitute ∑_{ν,r,s} U = C
  rw [show (∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        (∑ ν : ι, ∑ r : Fin (dims ν), ∑ s : Fin (dims ν), U ν r s α p q) * ((1 / dims α : ℂ) * conj (C α p q))) =
      (∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        C α p q * ((1 / dims α : ℂ) * conj (C α p q))) from by
    exact Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun q _ => by rfl)))]
  -- Step 9: Rewrite C * ((1/dims α) * conj(C)) = (1/dims α) * |C|²
  rw [show (∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        C α p q * ((1 / dims α : ℂ) * conj (C α p q))) =
      (∑ α : ι, ∑ p : Fin (dims α), ∑ q : Fin (dims α),
        (1 / dims α : ℂ) * (Complex.normSq (C α p q) : ℂ)) from by
    exact Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun q _ => by rw [Complex.normSq_eq_conj_mul_self]; ring)))]
  -- Step 10: Conclude ∑ (1/dims α) * |C|² ≥ 0
  exact Finset.sum_nonneg (fun α _ => Finset.sum_nonneg (fun p _ =>
    Finset.sum_nonneg (fun q _ => by
      have h1 : 0 ≤ (1 / dims α : ℝ) := by positivity
      have h2 : 0 ≤ Complex.normSq (C α p q) := Complex.normSq_nonneg _
      have h3 : 0 ≤ (1 / dims α : ℝ) * Complex.normSq (C α p q) := mul_nonneg h1 h2
      convert Complex.zero_le_real.mpr h3 using 2
      simp [Complex.ofReal_mul, Complex.ofReal_div])))

#print axioms cg_unitarity_nonneg

