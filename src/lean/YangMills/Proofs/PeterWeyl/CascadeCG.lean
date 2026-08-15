/-
# Peter-Weyl: Step 3(c) 2-fold CG Decomposition for 3D Cascade
-/

import YangMills.Proofs.PeterWeyl.Site3DIntegral

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open Finset
open Matrix
open MeasureTheory
open scoped ComplexConjugate

namespace YangMills
/-! ## Step 3(c): 2-fold CG decomposition building blocks for the 3D global cascade

The 3-fold lemmas above (`single_site_3D_luscher_integral`, `cg_unitarity_nonneg`)
handle the case where each site has 3 unbarred + 3 barred matrix elements (3 spatial
directions, all non-local). The 2-fold lemmas below handle the case where each site
has 2 unbarred + 2 barred matrix elements (2 non-local directions), which is the
simplest setting exhibiting the CG decomposition mechanism in a multi-site cascade.
These are the 2D analogues, proved by the same technique (CG decomposition + Schur
orthogonality) but with 3 nesting levels instead of 6. 0 sorries, 0 new axioms. -/

/-- **2-fold CG conjugate decomposition.** Conjugate of `hcgME_decomp`:
`conj((ρ_s g)_{ab}) · conj((ρ_t g)_{ij}) = ∑_ν ∑_{p,q} conj(cgME s t ν a i p) · conj((ρ_ν g)_{pq}) · cgME s t ν b j q`.

Pure algebra from `hcgME_decomp` (take conjugate, push `conj` through products and sums). -/
lemma cgME_decomp_conj
    {G : Type*} [Group G]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (cgME : ∀ (s t ν : ι), Fin (dims s) → Fin (dims t) → Fin (dims ν) → ℂ)
    (hcgME_decomp : ∀ (s t : ι) (g : G) (a b : Fin (dims s)) (i j : Fin (dims t)),
        (ρ s g) a b * (ρ t g) i j =
        ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
          cgME s t ν a i p * (ρ ν g) p q * conj (cgME s t ν b j q))
    (s t : ι) (g : G) (a b : Fin (dims s)) (i j : Fin (dims t)) :
    conj ((ρ s g) a b) * conj ((ρ t g) i j) =
    ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
      conj (cgME s t ν a i p) * conj ((ρ ν g) p q) * cgME s t ν b j q := by
  have h := hcgME_decomp s t g a b i j
  have hconj : conj ((ρ s g) a b * (ρ t g) i j) =
      conj (∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
        cgME s t ν a i p * (ρ ν g) p q * conj (cgME s t ν b j q)) := by
    rw [h]
  simp at hconj
  exact hconj

#print axioms cgME_decomp_conj

/-- **Integral of 1 unbarred × 2 barred matrix elements (2D helper).**

`∫ (ρ_σ g)_{pq} · conj((ρ_{t1} g)_{c1d1}) · conj((ρ_{t2} g)_{c2d2}) dμ(g)
  = (1/dims σ) · conj(cgME t1 t2 σ c1 c2 p) · cgME t1 t2 σ d1 d2 q`

Applies `cgME_decomp_conj` to the 2 barred MEs, exchanges sums with the integral
(Fubini, 3 levels), collapses the combined-rep sum to `σ` (Schur off-diagonal),
collapses the index sums to `p, q` (Schur diagonal), and factors out `1/dims σ`.
0 sorries, 0 new axioms. -/
lemma integral_ME_times_2barred_MEs
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
    (t1 t2 : ι) (c1 d1 : Fin (dims t1)) (c2 d2 : Fin (dims t2)) :
    ∫ g, (ρ σ g) p q * conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) ∂μ =
      (1 / dims σ : ℂ) * (conj (cgME t1 t2 σ c1 c2 p) * cgME t1 t2 σ d1 d2 q) := by
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  -- Pointwise identity: apply cgME_decomp_conj to the 2 barred MEs, distribute (ρ σ g) p q
  have hpt : ∀ (g : G),
      (ρ σ g) p q * conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) =
      ∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
        conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
        ((ρ σ g) p q * conj ((ρ ν' g) r' s')) := by
    intro g
    have hreassoc : (ρ σ g) p q * conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) =
        (ρ σ g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2)) := by ring
    rw [hreassoc, cgME_decomp_conj ι dims ρ cgME hcgME_decomp t1 t2 g c1 d1 c2 d2]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ν' _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r' _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s' _
    ring
  -- Rewrite the integral using the pointwise identity
  rw [show (∫ g, (ρ σ g) p q * conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) ∂μ) =
        ∫ g, (∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
          conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
          ((ρ σ g) p q * conj ((ρ ν' g) r' s'))) ∂μ from by
    congr 1 with g; exact hpt g]
  -- Per-term integrability (3 levels)
  have hInt_term : ∀ (ν' : ι) (r' : Fin (dims ν')) (s' : Fin (dims ν')),
      Integrable (fun g =>
        conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
        ((ρ σ g) p q * conj ((ρ ν' g) r' s'))) μ := by
    intro ν' r' s'
    exact Integrable.smul
      (conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s')
      (hInt σ ν' p q r' s')
  have hInt_s' : ∀ (ν' : ι) (r' : Fin (dims ν')),
      Integrable (fun g => ∑ s' : Fin (dims ν'),
        conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
        ((ρ σ g) p q * conj ((ρ ν' g) r' s'))) μ := by
    intro ν' r'
    exact integrable_finsetSum Finset.univ (fun s' _ => hInt_term ν' r' s')
  have hInt_r' : ∀ (ν' : ι),
      Integrable (fun g => ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
        conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
        ((ρ σ g) p q * conj ((ρ ν' g) r' s'))) μ := by
    intro ν'
    exact integrable_finsetSum Finset.univ (fun r' _ => hInt_s' ν' r')
  have hInt_ν' : Integrable (fun g => ∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
        conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
        ((ρ σ g) p q * conj ((ρ ν' g) r' s'))) μ := by
    exact integrable_finsetSum Finset.univ (fun ν' _ => hInt_r' ν')
  -- Exchange sums with integral (3 levels)
  rw [integral_finsetSum Finset.univ (fun ν' _ => hInt_r' ν')]
  rw [Finset.sum_congr rfl (fun ν' _ => integral_finsetSum Finset.univ (fun r' _ => hInt_s' ν' r'))]
  rw [Finset.sum_congr rfl (fun ν' _ => Finset.sum_congr rfl (fun r' _ =>
      integral_finsetSum Finset.univ (fun s' _ => hInt_term ν' r' s')))]
  -- For ν' ≠ σ, each integral is 0 (pull constant + Schur offdiag)
  have hν'_ne_zero : ∀ (ν' : ι), ν' ≠ σ →
      (∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
        ∫ g,
          conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
          ((ρ σ g) p q * conj ((ρ ν' g) r' s')) ∂μ) = 0 := by
    intro ν' hν'
    refine Finset.sum_eq_zero (fun r' _ => ?_)
    refine Finset.sum_eq_zero (fun s' _ => ?_)
    rw [integral_const_mul, hSchur_offdiag σ ν' p q r' s' (Ne.symm hν')]
    simp
  -- Collapse ν' sum: only ν' = σ contributes
  have hν'_collapse :
      (∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
        ∫ g,
          conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
          ((ρ σ g) p q * conj ((ρ ν' g) r' s')) ∂μ) =
      (∑ r' : Fin (dims σ), ∑ s' : Fin (dims σ),
        ∫ g,
          conj (cgME t1 t2 σ c1 c2 r') * cgME t1 t2 σ d1 d2 s' *
          ((ρ σ g) p q * conj ((ρ σ g) r' s')) ∂μ) := by
    exact Finset.sum_eq_single σ (fun ν' _ hν' => hν'_ne_zero ν' hν')
        (fun h => (h (Finset.mem_univ _)).elim)
  rw [hν'_collapse]
  -- Evaluate each integral (ν' = σ case: pull constant + Schur diag)
  have hInt_eval : ∀ (r' : Fin (dims σ)) (s' : Fin (dims σ)),
      ∫ g,
        conj (cgME t1 t2 σ c1 c2 r') * cgME t1 t2 σ d1 d2 s' *
        ((ρ σ g) p q * conj ((ρ σ g) r' s')) ∂μ =
        conj (cgME t1 t2 σ c1 c2 r') * cgME t1 t2 σ d1 d2 s' *
        (if p = r' ∧ q = s' then (1 / dims σ : ℂ) else 0) := by
    intro r' s'
    rw [integral_const_mul, hSchur_diag]
  rw [Finset.sum_congr rfl (fun r' _ => Finset.sum_congr rfl (fun s' _ => hInt_eval r' s'))]
  -- Collapse r', s' sums
  have hrs'_collapse :
      (∑ r' : Fin (dims σ), ∑ s' : Fin (dims σ),
        conj (cgME t1 t2 σ c1 c2 r') * cgME t1 t2 σ d1 d2 s' *
        (if p = r' ∧ q = s' then (1 / dims σ : ℂ) else 0)) =
      conj (cgME t1 t2 σ c1 c2 p) * cgME t1 t2 σ d1 d2 q * (1 / dims σ : ℂ) := by
    rw [Finset.sum_eq_single p (fun r' _ hr => Finset.sum_eq_zero (fun s' _ => by
        simp [Ne.symm hr])) (fun h => (h (Finset.mem_univ _)).elim)]
    simp only [eq_self_iff_true, true_and]
    rw [Finset.sum_eq_single q (fun s' _ hs => by simp [Ne.symm hs])
        (fun h => (h (Finset.mem_univ _)).elim)]
    simp only [eq_self_iff_true, if_true]
  rw [hrs'_collapse]
  ring

#print axioms integral_ME_times_2barred_MEs

/-- **Single-site 2D Lüscher integral (Step 3c building block).**

For irreducible unitary representations of a compact group with normalized Haar measure, the
integral of 2 unbarred matrix elements times 2 barred matrix elements (as arises at each site
when integrating out a temporal link `u_t(x)` in 2D, with 2 non-local directions) equals a sum
over the combined representation `ν` of `(1/dims ν)` times the product of the unbarred and
barred CG coefficients:

    ∫ (ρ_{s₁} g)_{a₁b₁} · (ρ_{s₂} g)_{a₂b₂}
        · conj((ρ_{t₁} g)_{c₁d₁}) · conj((ρ_{t₂} g)_{c₂d₂}) dμ(g)
      = ∑_{ν,p,q} CG_unbarred(ν,p,q) · (1/dims ν) · CG_barred(ν,p,q)

Proof: apply `hcgME_decomp` to the 2 unbarred MEs (3 sums), exchange sums with integral
(Fubini), then evaluate each inner integral `∫ (ρ_ν g)_{pq} · [2 barred MEs] dμ` using
`integral_ME_times_2barred_MEs`. 0 sorries, 0 new axioms. -/
lemma single_site_2D_luscher_integral
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
    (s1 s2 : ι) (a1 b1 : Fin (dims s1)) (a2 b2 : Fin (dims s2))
    (t1 t2 : ι) (c1 d1 : Fin (dims t1)) (c2 d2 : Fin (dims t2)) :
    ∫ g, (ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 *
        conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) ∂μ =
      ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
        (cgME s1 s2 ν a1 a2 p * conj (cgME s1 s2 ν b1 b2 q)) *
        ((1 / dims ν : ℂ) *
         (conj (cgME t1 t2 ν c1 c2 p) * cgME t1 t2 ν d1 d2 q)) := by
  obtain ⟨hInt, hSchur_diag, hSchur_offdiag⟩ :=
    characterOrthogonality μ ι dims hDims ρ hU hIrr
  -- Integrability of the 3-ME product (1 unbarred × 2 barred) via CG decomposition of barred MEs
  have hInt_3ME : ∀ (α : ι) (p : Fin (dims α)) (q : Fin (dims α)),
      Integrable (fun g => (ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2))) μ := by
    intro α p q
    have hpt_barred : ∀ (g : G),
        conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) =
        ∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
          conj (cgME t1 t2 ν' c1 c2 r') * conj ((ρ ν' g) r' s') * cgME t1 t2 ν' d1 d2 s' := by
      intro g
      exact cgME_decomp_conj ι dims ρ cgME hcgME_decomp t1 t2 g c1 d1 c2 d2
    rw [show (fun g => (ρ α g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2))) =
        (fun g => ∑ ν' : ι, ∑ r' : Fin (dims ν'), ∑ s' : Fin (dims ν'),
          conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s' *
          ((ρ α g) p q * conj ((ρ ν' g) r' s'))) from by
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
      ring]
    apply integrable_finsetSum Finset.univ
    intro ν' _
    apply integrable_finsetSum Finset.univ
    intro r' _
    apply integrable_finsetSum Finset.univ
    intro s' _
    exact Integrable.smul
      (conj (cgME t1 t2 ν' c1 c2 r') * cgME t1 t2 ν' d1 d2 s')
      (hInt α ν' p q r' s')
  -- Pointwise identity: apply hcgME_decomp to the 2 unbarred MEs, distribute barred product
  have hpt : ∀ (g : G),
      (ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 *
      conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) =
      ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
        (cgME s1 s2 ν a1 a2 p * conj (cgME s1 s2 ν b1 b2 q)) *
        ((ρ ν g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2))) := by
    intro g
    have hreassoc : (ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 *
        conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) =
        ((ρ s1 g) a1 b1 * (ρ s2 g) a2 b2) *
        (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2)) := by ring
    rw [hreassoc, hcgME_decomp s1 s2 g a1 b1 a2 b2]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ν _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q _
    ring
  -- Rewrite the integral using the pointwise identity
  rw [show (∫ g, (ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 *
        conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) ∂μ) =
        ∫ g, (∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
          (cgME s1 s2 ν a1 a2 p * conj (cgME s1 s2 ν b1 b2 q)) *
          ((ρ ν g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2)))) ∂μ from by
    congr 1 with g; exact hpt g]
  -- Per-term integrability (3 levels, using hInt_3ME)
  have hInt_term : ∀ (ν : ι) (p : Fin (dims ν)) (q : Fin (dims ν)),
      Integrable (fun g =>
        (cgME s1 s2 ν a1 a2 p * conj (cgME s1 s2 ν b1 b2 q)) *
        ((ρ ν g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2)))) μ := by
    intro ν p q
    exact Integrable.smul
      (cgME s1 s2 ν a1 a2 p * conj (cgME s1 s2 ν b1 b2 q))
      (hInt_3ME ν p q)
  have hInt_q : ∀ (ν : ι) (p : Fin (dims ν)),
      Integrable (fun g => ∑ q : Fin (dims ν),
        (cgME s1 s2 ν a1 a2 p * conj (cgME s1 s2 ν b1 b2 q)) *
        ((ρ ν g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2)))) μ := by
    intro ν p
    exact integrable_finsetSum Finset.univ (fun q _ => hInt_term ν p q)
  have hInt_p : ∀ (ν : ι),
      Integrable (fun g => ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
        (cgME s1 s2 ν a1 a2 p * conj (cgME s1 s2 ν b1 b2 q)) *
        ((ρ ν g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2)))) μ := by
    intro ν
    exact integrable_finsetSum Finset.univ (fun p _ => hInt_q ν p)
  have hInt_ν : Integrable (fun g => ∑ ν : ι, ∑ p : Fin (dims ν), ∑ q : Fin (dims ν),
        (cgME s1 s2 ν a1 a2 p * conj (cgME s1 s2 ν b1 b2 q)) *
        ((ρ ν g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2)))) μ := by
    exact integrable_finsetSum Finset.univ (fun ν _ => hInt_p ν)
  -- Exchange sums with integral (3 levels)
  rw [integral_finsetSum Finset.univ (fun ν _ => hInt_p ν)]
  rw [Finset.sum_congr rfl (fun ν _ => integral_finsetSum Finset.univ (fun p _ => hInt_q ν p))]
  rw [Finset.sum_congr rfl (fun ν _ => Finset.sum_congr rfl (fun p _ =>
      integral_finsetSum Finset.univ (fun q _ => hInt_term ν p q)))]
  -- Evaluate each inner integral using the helper
  have hInt_eval : ∀ (ν : ι) (p : Fin (dims ν)) (q : Fin (dims ν)),
      ∫ g,
        (cgME s1 s2 ν a1 a2 p * conj (cgME s1 s2 ν b1 b2 q)) *
        ((ρ ν g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2))) ∂μ =
        (cgME s1 s2 ν a1 a2 p * conj (cgME s1 s2 ν b1 b2 q)) *
        ((1 / dims ν : ℂ) *
         (conj (cgME t1 t2 ν c1 c2 p) * cgME t1 t2 ν d1 d2 q)) := by
    intro ν p q
    rw [integral_const_mul,
        show ∫ g, (ρ ν g) p q * (conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2)) ∂μ =
            ∫ g, (ρ ν g) p q * conj ((ρ t1 g) c1 d1) * conj ((ρ t2 g) c2 d2) ∂μ from by
          congr 1 with g; ring,
        integral_ME_times_2barred_MEs μ ι dims hDims ρ hU hIrr cgME hcgME_decomp
          ν p q t1 t2 c1 d1 c2 d2]
  rw [Finset.sum_congr rfl (fun ν _ => Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun q _ => hInt_eval ν p q)))]

#print axioms single_site_2D_luscher_integral

open scoped ComplexOrder in
/-- **2-fold CG unitarity non-negativity (Step 3c building block).** In the diagonal case
(barred indices = unbarred indices), the single-site 2D Lüscher integral gives
`∑_{ν,p,q} (1/dims ν) · |cgME s1 s2 ν a1 a2 p|² · |cgME s1 s2 ν b1 b2 q|² ≥ 0`.

This is the 2D analogue of `cg_unitarity_nonneg`: the diagonal case of
`single_site_2D_luscher_integral` gives a sum of `|A|² · |B|²` terms with non-negative
coefficients `(1/dims ν) > 0`, hence non-negative. 0 sorries, 0 new axioms. -/
lemma cg2_unitarity_nonneg
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
    (s1 s2 : ι) (a1 b1 : Fin (dims s1)) (a2 b2 : Fin (dims s2)) :
    0 ≤ ∫ g, (ρ s1 g) a1 b1 * (ρ s2 g) a2 b2 *
        conj ((ρ s1 g) a1 b1) * conj ((ρ s2 g) a2 b2) ∂μ := by
  -- Step 1: Apply single_site_2D_luscher_integral with diagonal args
  rw [single_site_2D_luscher_integral μ ι dims hDims ρ hU hIrr cgME hcgME_decomp
    s1 s2 a1 b1 a2 b2 s1 s2 a1 b1 a2 b2]
  -- Step 2: In the diagonal case, the CG product simplifies to |A|² · |B|² · (1/dims ν)
  exact Finset.sum_nonneg (fun ν _ => Finset.sum_nonneg (fun p _ =>
    Finset.sum_nonneg (fun q _ => by
      set A := cgME s1 s2 ν a1 a2 p
      set B := cgME s1 s2 ν b1 b2 q
      -- The term is (A * conj B) * ((1/dims ν) * (conj A * B)) = (1/dims ν) * |A|² * |B|²
      have hnormSq : (A * conj B) * ((1 / dims ν : ℂ) * (conj A * B)) =
          (1 / dims ν : ℂ) * Complex.normSq A * Complex.normSq B := by
        rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
        ring
      rw [hnormSq]
      have h1 : 0 ≤ (1 / dims ν : ℝ) := by positivity
      have h2 : 0 ≤ Complex.normSq A := Complex.normSq_nonneg _
      have h3 : 0 ≤ Complex.normSq B := Complex.normSq_nonneg _
      have h4 : 0 ≤ (1 / dims ν : ℝ) * Complex.normSq A * Complex.normSq B :=
        mul_nonneg (mul_nonneg h1 h2) h3
      convert Complex.zero_le_real.mpr h4 using 2
      simp [Complex.ofReal_mul, Complex.ofReal_div])))
#print axioms cg2_unitarity_nonneg

