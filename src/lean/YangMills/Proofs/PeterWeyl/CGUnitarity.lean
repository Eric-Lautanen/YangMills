/-
# Peter-Weyl: CG Unitarity Applications

This file contains the first applications of `hcgME_unitary` (the CG unitarity
relation from the Peter-Weyl axiom). The key result is the CG isometry
(Parseval identity), which is the building block for the B*B non-negativity
argument in the 3D Lüscher cascade (Step B of the transfer matrix positivity).

`hcgME_unitary` has been available in the axiom since its introduction but has
never been applied in any proof. This file is the first to use it.
-/

import YangMills.Proofs.PeterWeyl.TripleProduct

open Finset
open scoped ComplexConjugate

namespace YangMills

/-- **CG isometry (Parseval identity) — first application of `hcgME_unitary`.**

The CG change-of-basis matrix `cgME s t ν` is an isometry (by `hcgME_unitary`):
it preserves the ℓ² norm. For any vector `v : Fin (dims s) → Fin (dims t) → ℂ`,

    ∑_{ν,p} |∑_{a,i} cgME s t ν a i p · v(a,i)|² = ∑_{a,i} |v(a,i)|²

This is the first application of `hcgME_unitary` (the CG unitarity relation from
the Peter-Weyl axiom, which has been available but never previously applied).
It is the key building block for the B*B non-negativity argument in the 3D
Lüscher cascade (Step B): the cascade defines a Fourier coefficient extraction
operator B, and B*B gives `⟨g, Tg⟩ = ‖Bg‖² ≥ 0` by this isometry.

Proof: expand `|w|² = conj(w) · w`, distribute the product of sums, exchange
the `(ν,p)` sum with the `(a,i,b,j)` sums, apply `hcgME_unitary` to collapse
`∑_{ν,p} conj(cgME_{a,i}) · cgME_{b,j}` to `δ_{a,b}·δ_{i,j}`, then collapse
the delta. 0 sorries, 0 new axioms. -/
lemma cgME_isometry_normSq
    {ι : Type*} [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (cgME : ∀ (s t ν : ι), Fin (dims s) → Fin (dims t) → Fin (dims ν) → ℂ)
    (hcgME_unitary : ∀ (s t : ι) (a b : Fin (dims s)) (i j : Fin (dims t)),
        ∑ ν : ι, ∑ p : Fin (dims ν),
          conj (cgME s t ν a i p) * cgME s t ν b j p =
          if a = b ∧ i = j then (1 : ℂ) else 0)
    (s t : ι) (v : Fin (dims s) → Fin (dims t) → ℂ) :
    ∑ (ν : ι), ∑ (p : Fin (dims ν)),
      Complex.normSq (∑ (a : Fin (dims s)), ∑ (i : Fin (dims t)),
        cgME s t ν a i p * v a i) =
    ∑ (a : Fin (dims s)), ∑ (i : Fin (dims t)),
      Complex.normSq (v a i) := by
  -- Step 1: Convert ℝ equality to ℂ equality, expand normSq = conj * self
  rw [← Complex.ofReal_inj]
  simp only [Complex.ofReal_sum]
  simp only [Complex.normSq_eq_conj_mul_self]
  -- Step 2: Expand conj of the inner sum on the LHS
  have hconj : ∀ (ν : ι) (p : Fin (dims ν)),
      conj (∑ a : Fin (dims s), ∑ i : Fin (dims t), cgME s t ν a i p * v a i) =
      ∑ a : Fin (dims s), ∑ i : Fin (dims t), conj (cgME s t ν a i p) * conj (v a i) := by
    intro ν p
    rw [map_sum (starRingEnd ℂ) (fun a => ∑ i : Fin (dims t), cgME s t ν a i p * v a i) Finset.univ]
    rw [show (∑ a : Fin (dims s), conj (∑ i : Fin (dims t), cgME s t ν a i p * v a i)) =
          (∑ a : Fin (dims s), ∑ i : Fin (dims t), conj (cgME s t ν a i p) * conj (v a i))
        from Finset.sum_congr rfl (fun a _ => by
          rw [map_sum (starRingEnd ℂ) (fun i => cgME s t ν a i p * v a i) Finset.univ]
          simp only [map_mul])]
  -- Step 3: Expand conj (via hconj) and distribute product of sums on the LHS
  rw [show (∑ ν : ι, ∑ p : Fin (dims ν),
      conj (∑ a : Fin (dims s), ∑ i : Fin (dims t), cgME s t ν a i p * v a i) *
      (∑ a : Fin (dims s), ∑ i : Fin (dims t), cgME s t ν a i p * v a i)) =
    (∑ ν : ι, ∑ p : Fin (dims ν),
      ∑ a : Fin (dims s), ∑ i : Fin (dims t), ∑ b : Fin (dims s), ∑ j : Fin (dims t),
        conj (cgME s t ν a i p) * conj (v a i) * (cgME s t ν b j p * v b j)) from by
    apply Finset.sum_congr rfl; intro ν _; apply Finset.sum_congr rfl; intro p _
    rw [hconj]
    simp only [Finset.sum_mul_sum]
    rw [show (∑ a : Fin (dims s), ∑ b : Fin (dims s), ∑ i : Fin (dims t), ∑ j : Fin (dims t),
          conj (cgME s t ν a i p) * conj (v a i) * (cgME s t ν b j p * v b j)) =
        (∑ a : Fin (dims s), ∑ i : Fin (dims t), ∑ b : Fin (dims s), ∑ j : Fin (dims t),
          conj (cgME s t ν a i p) * conj (v a i) * (cgME s t ν b j p * v b j)) from by
      exact Finset.sum_congr rfl (fun a _ => by rw [Finset.sum_comm])]]
  -- Step 4: Exchange (ν,p) sum to inside
  rw [show (∑ ν : ι, ∑ p : Fin (dims ν),
      ∑ a : Fin (dims s), ∑ i : Fin (dims t), ∑ b : Fin (dims s), ∑ j : Fin (dims t),
        conj (cgME s t ν a i p) * conj (v a i) * (cgME s t ν b j p * v b j)) =
    ∑ a : Fin (dims s), ∑ i : Fin (dims t), ∑ b : Fin (dims s), ∑ j : Fin (dims t),
      conj (v a i) * v b j *
      (∑ ν : ι, ∑ p : Fin (dims ν),
        conj (cgME s t ν a i p) * cgME s t ν b j p) from ?_]
  · -- Step 5: Apply hcgME_unitary, collapse delta
    simp only [hcgME_unitary]
    congr 1; ext a; congr 1; ext i
    -- Goal: ∑ b, ∑ j, conj(v a i) * v b j * (if a = b ∧ i = j then 1 else 0) = conj(v a i) * v a i
    rw [Finset.sum_eq_single a]
    · -- b = a case: ∑ j, conj(v a i) * v a j * (if a = a ∧ i = j then 1 else 0) = conj(v a i) * v a i
      rw [Finset.sum_eq_single i]
      · -- j = i case
        rw [if_pos (And.intro rfl rfl)]
        ring
      · -- j ≠ i case
        intro j _ hij
        rw [if_neg (fun h => hij (h.2.symm))]
        ring
      · -- i ∉ univ case
        intro h; exact absurd (Finset.mem_univ i) h
    · -- b ≠ a case
      intro b _ hab
      apply Finset.sum_eq_zero
      intro j _
      rw [if_neg (fun h => hab (h.1.symm))]
      ring
    · -- a ∉ univ case
      intro h; exact absurd (Finset.mem_univ a) h
  · -- Step 6: Prove the sum exchange (reorder (ν,p,a,i,b,j) → (a,i,b,j,ν,p) + reassociate)
    -- Swap p,a (inside ν)
    rw [show (∑ ν : ι, ∑ p : Fin (dims ν), ∑ a : Fin (dims s), ∑ i : Fin (dims t),
        ∑ b : Fin (dims s), ∑ j : Fin (dims t),
        conj (cgME s t ν a i p) * conj (v a i) * (cgME s t ν b j p * v b j)) =
      (∑ ν : ι, ∑ a : Fin (dims s), ∑ p : Fin (dims ν), ∑ i : Fin (dims t),
        ∑ b : Fin (dims s), ∑ j : Fin (dims t),
        conj (cgME s t ν a i p) * conj (v a i) * (cgME s t ν b j p * v b j)) from by
      exact Finset.sum_congr rfl (fun ν _ => by rw [Finset.sum_comm])]
    -- Swap ν,a
    rw [show (∑ ν : ι, ∑ a : Fin (dims s), ∑ p : Fin (dims ν), ∑ i : Fin (dims t),
        ∑ b : Fin (dims s), ∑ j : Fin (dims t),
        conj (cgME s t ν a i p) * conj (v a i) * (cgME s t ν b j p * v b j)) =
      (∑ a : Fin (dims s), ∑ ν : ι, ∑ p : Fin (dims ν), ∑ i : Fin (dims t),
        ∑ b : Fin (dims s), ∑ j : Fin (dims t),
        conj (cgME s t ν a i p) * conj (v a i) * (cgME s t ν b j p * v b j)) from by
      rw [Finset.sum_comm]]
    -- Swap p,i (inside a,ν)
    rw [show (∑ a : Fin (dims s), ∑ ν : ι, ∑ p : Fin (dims ν), ∑ i : Fin (dims t),
        ∑ b : Fin (dims s), ∑ j : Fin (dims t),
        conj (cgME s t ν a i p) * conj (v a i) * (cgME s t ν b j p * v b j)) =
      (∑ a : Fin (dims s), ∑ ν : ι, ∑ i : Fin (dims t), ∑ p : Fin (dims ν),
        ∑ b : Fin (dims s), ∑ j : Fin (dims t),
        conj (cgME s t ν a i p) * conj (v a i) * (cgME s t ν b j p * v b j)) from by
      exact Finset.sum_congr rfl (fun a _ =>
        Finset.sum_congr rfl (fun ν _ => by rw [Finset.sum_comm]))]
    -- Swap ν,i (inside a)
    rw [show (∑ a : Fin (dims s), ∑ ν : ι, ∑ i : Fin (dims t), ∑ p : Fin (dims ν),
        ∑ b : Fin (dims s), ∑ j : Fin (dims t),
        conj (cgME s t ν a i p) * conj (v a i) * (cgME s t ν b j p * v b j)) =
      (∑ a : Fin (dims s), ∑ i : Fin (dims t), ∑ ν : ι, ∑ p : Fin (dims ν),
        ∑ b : Fin (dims s), ∑ j : Fin (dims t),
        conj (cgME s t ν a i p) * conj (v a i) * (cgME s t ν b j p * v b j)) from by
      exact Finset.sum_congr rfl (fun a _ => by rw [Finset.sum_comm])]
    -- Swap p,b (inside a,i,ν)
    rw [show (∑ a : Fin (dims s), ∑ i : Fin (dims t), ∑ ν : ι, ∑ p : Fin (dims ν),
        ∑ b : Fin (dims s), ∑ j : Fin (dims t),
        conj (cgME s t ν a i p) * conj (v a i) * (cgME s t ν b j p * v b j)) =
      (∑ a : Fin (dims s), ∑ i : Fin (dims t), ∑ ν : ι, ∑ b : Fin (dims s),
        ∑ p : Fin (dims ν), ∑ j : Fin (dims t),
        conj (cgME s t ν a i p) * conj (v a i) * (cgME s t ν b j p * v b j)) from by
      exact Finset.sum_congr rfl (fun a _ =>
        Finset.sum_congr rfl (fun i _ =>
          Finset.sum_congr rfl (fun ν _ => by rw [Finset.sum_comm])))]
    -- Swap ν,b (inside a,i)
    rw [show (∑ a : Fin (dims s), ∑ i : Fin (dims t), ∑ ν : ι, ∑ b : Fin (dims s),
        ∑ p : Fin (dims ν), ∑ j : Fin (dims t),
        conj (cgME s t ν a i p) * conj (v a i) * (cgME s t ν b j p * v b j)) =
      (∑ a : Fin (dims s), ∑ i : Fin (dims t), ∑ b : Fin (dims s), ∑ ν : ι,
        ∑ p : Fin (dims ν), ∑ j : Fin (dims t),
        conj (cgME s t ν a i p) * conj (v a i) * (cgME s t ν b j p * v b j)) from by
      exact Finset.sum_congr rfl (fun a _ =>
        Finset.sum_congr rfl (fun i _ => by rw [Finset.sum_comm]))]
    -- Swap p,j (inside a,i,b,ν)
    rw [show (∑ a : Fin (dims s), ∑ i : Fin (dims t), ∑ b : Fin (dims s), ∑ ν : ι,
        ∑ p : Fin (dims ν), ∑ j : Fin (dims t),
        conj (cgME s t ν a i p) * conj (v a i) * (cgME s t ν b j p * v b j)) =
      (∑ a : Fin (dims s), ∑ i : Fin (dims t), ∑ b : Fin (dims s), ∑ ν : ι,
        ∑ j : Fin (dims t), ∑ p : Fin (dims ν),
        conj (cgME s t ν a i p) * conj (v a i) * (cgME s t ν b j p * v b j)) from by
      exact Finset.sum_congr rfl (fun a _ =>
        Finset.sum_congr rfl (fun i _ =>
          Finset.sum_congr rfl (fun b _ =>
            Finset.sum_congr rfl (fun ν _ => by rw [Finset.sum_comm]))))]
    -- Swap ν,j (inside a,i,b)
    rw [show (∑ a : Fin (dims s), ∑ i : Fin (dims t), ∑ b : Fin (dims s), ∑ ν : ι,
        ∑ j : Fin (dims t), ∑ p : Fin (dims ν),
        conj (cgME s t ν a i p) * conj (v a i) * (cgME s t ν b j p * v b j)) =
      (∑ a : Fin (dims s), ∑ i : Fin (dims t), ∑ b : Fin (dims s), ∑ j : Fin (dims t),
        ∑ ν : ι, ∑ p : Fin (dims ν),
        conj (cgME s t ν a i p) * conj (v a i) * (cgME s t ν b j p * v b j)) from by
      exact Finset.sum_congr rfl (fun a _ =>
        Finset.sum_congr rfl (fun i _ =>
          Finset.sum_congr rfl (fun b _ => by rw [Finset.sum_comm])))]
    -- Reassociate and factor conj(v) * v out of the (ν,p) sum
    rw [show (∑ a : Fin (dims s), ∑ i : Fin (dims t), ∑ b : Fin (dims s), ∑ j : Fin (dims t),
        ∑ ν : ι, ∑ p : Fin (dims ν),
        conj (cgME s t ν a i p) * conj (v a i) * (cgME s t ν b j p * v b j)) =
      (∑ a : Fin (dims s), ∑ i : Fin (dims t), ∑ b : Fin (dims s), ∑ j : Fin (dims t),
        conj (v a i) * v b j *
        (∑ ν : ι, ∑ p : Fin (dims ν),
          conj (cgME s t ν a i p) * cgME s t ν b j p)) from by
      exact Finset.sum_congr rfl (fun a _ =>
        Finset.sum_congr rfl (fun i _ =>
          Finset.sum_congr rfl (fun b _ =>
            Finset.sum_congr rfl (fun j _ => by
              have h_term : ∀ (ν : ι) (p : Fin (dims ν)),
                  conj (cgME s t ν a i p) * conj (v a i) * (cgME s t ν b j p * v b j) =
                  conj (v a i) * v b j * (conj (cgME s t ν a i p) * cgME s t ν b j p) := by
                intro ν p; ring
              rw [Finset.sum_congr rfl (fun ν _ =>
                Finset.sum_congr rfl (fun p _ => h_term ν p))]
              simp only [← Finset.mul_sum]))))]

#print axioms cgME_isometry_normSq

/-! ## Multi-rep isometry (composed Parseval for the 3D cascade)

The 3D Lüscher cascade applies the CG change-of-basis with the FIRST
representation index summed over (the intermediate representation `ν` from the
first CG application).  The single isometry `cgME_isometry_normSq` handles a
FIXED `(s, t)` pair; the multi-rep isometry handles the case where the first
representation index `s` is itself a summation variable.

This requires a STRONGER hypothesis than `hcgME_unitary` alone: the
**cross-rep orthogonality** (orthogonality of CG matrices with different first
arguments, summed over the output).  We take this as a separate hypothesis
`hcgME_cross_rep`.

**Important finding (session 125):** `hcgME_cross_rep` is NOT a consequence of
`hcgME_unitary` alone — two different isometries can have overlapping column
spaces.  The cross-rep orthogonality is a consequence of the FULL unitarity of
the combined CG change-of-basis `⊕_s (V_s ⊗ V_t) → ⊕_α V_α`, which is derivable
from `hcgME_decomp` + Schur orthogonality (the matrix elements of distinct
irreps are orthogonal).  This derivation is planned for a future session; the
lemma here takes `hcgME_cross_rep` as a hypothesis.

This is "known but unformalized" — standard representation theory (unitarity of
the CG change-of-basis), not open math.  The formalization challenge is the
index bookkeeping, not the math. -/

/-- **Multi-rep CG isometry (composed Parseval).** The combined CG change-of-basis
from `⊕_s (V_s ⊗ V_t)` to `⊕_α V_α` is an isometry: for any `u`,

    ∑_{α,p} |∑_{s,a,i} cgME s t α a i p · u(s,a,i)|² = ∑_{s,a,i} |u(s,a,i)|²

This is the key building block for the 3D cascade (Step B.2): the second CG
application `cgME ν s3 α` has `ν` (the intermediate rep from the first CG
application) as a summation variable, requiring the multi-rep isometry rather
than the single isometry.

Hypotheses: `hcgME_unitary` (column orthonormality, the `s = s'` case) and
`hcgME_cross_rep` (cross-rep orthogonality, the `s ≠ s'` case). 0 sorries. -/
lemma cgME_multirep_isometry_normSq
    {ι : Type*} [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (cgME : ∀ (s t ν : ι), Fin (dims s) → Fin (dims t) → Fin (dims ν) → ℂ)
    (hcgME_unitary : ∀ (s t : ι) (a b : Fin (dims s)) (i j : Fin (dims t)),
        ∑ ν : ι, ∑ p : Fin (dims ν),
          conj (cgME s t ν a i p) * cgME s t ν b j p =
          if a = b ∧ i = j then (1 : ℂ) else 0)
    (hcgME_cross_rep : ∀ (s s' t : ι), s ≠ s' →
        ∀ (a : Fin (dims s)) (i : Fin (dims t)) (a' : Fin (dims s')) (i' : Fin (dims t)),
        ∑ α : ι, ∑ p : Fin (dims α),
          conj (cgME s t α a i p) * cgME s' t α a' i' p = 0)
    (t : ι) (u : ∀ (s : ι), Fin (dims s) → Fin (dims t) → ℂ) :
    ∑ (α : ι), ∑ (p : Fin (dims α)),
      Complex.normSq (∑ (s : ι), ∑ (a : Fin (dims s)), ∑ (i : Fin (dims t)),
        cgME s t α a i p * u s a i) =
    ∑ (s : ι), ∑ (a : Fin (dims s)), ∑ (i : Fin (dims t)),
      Complex.normSq (u s a i) := by
  -- Step 1: Convert ℝ equality to ℂ equality, expand normSq = conj * self
  rw [← Complex.ofReal_inj]
  simp only [Complex.ofReal_sum]
  simp only [Complex.normSq_eq_conj_mul_self]
  -- Step 2: Expand conj of the inner sum on the LHS
  have hconj : ∀ (α : ι) (p : Fin (dims α)),
      conj (∑ s : ι, ∑ a : Fin (dims s), ∑ i : Fin (dims t), cgME s t α a i p * u s a i) =
      ∑ s : ι, ∑ a : Fin (dims s), ∑ i : Fin (dims t), conj (cgME s t α a i p) * conj (u s a i) := by
    intro α p
    rw [map_sum (starRingEnd ℂ)
        (fun s => ∑ a : Fin (dims s), ∑ i : Fin (dims t), cgME s t α a i p * u s a i) Finset.univ]
    exact Finset.sum_congr rfl (fun s _ => by
      rw [map_sum (starRingEnd ℂ)
          (fun a => ∑ i : Fin (dims t), cgME s t α a i p * u s a i) Finset.univ]
      exact Finset.sum_congr rfl (fun a _ => by
        rw [map_sum (starRingEnd ℂ) (fun i => cgME s t α a i p * u s a i) Finset.univ]
        simp only [map_mul]))
  -- Step 3: Expand conj (via hconj) and distribute product of sums on the LHS
  rw [show (∑ α : ι, ∑ p : Fin (dims α),
      conj (∑ s : ι, ∑ a : Fin (dims s), ∑ i : Fin (dims t), cgME s t α a i p * u s a i) *
      (∑ s : ι, ∑ a : Fin (dims s), ∑ i : Fin (dims t), cgME s t α a i p * u s a i)) =
    (∑ α : ι, ∑ p : Fin (dims α),
      ∑ s' : ι, ∑ a' : Fin (dims s'), ∑ i' : Fin (dims t),
      ∑ s : ι, ∑ a : Fin (dims s), ∑ i : Fin (dims t),
        conj (cgME s' t α a' i' p) * conj (u s' a' i') * (cgME s t α a i p * u s a i)) from by
    apply Finset.sum_congr rfl; intro α _; apply Finset.sum_congr rfl; intro p _
    rw [hconj]
    simp only [Finset.sum_mul_sum]
    -- Reorder (s', s, a', a, i', i) → (s', a', i', s, a, i): 3 swaps
    rw [show (∑ s' : ι, ∑ s : ι, ∑ a' : Fin (dims s'), ∑ a : Fin (dims s),
          ∑ i' : Fin (dims t), ∑ i : Fin (dims t),
          conj (cgME s' t α a' i' p) * conj (u s' a' i') * (cgME s t α a i p * u s a i)) =
        (∑ s' : ι, ∑ s : ι, ∑ a' : Fin (dims s'), ∑ i' : Fin (dims t),
          ∑ a : Fin (dims s), ∑ i : Fin (dims t),
          conj (cgME s' t α a' i' p) * conj (u s' a' i') * (cgME s t α a i p * u s a i)) from by
      exact Finset.sum_congr rfl (fun s' _ => Finset.sum_congr rfl (fun s _ =>
        Finset.sum_congr rfl (fun a' _ => by rw [Finset.sum_comm])))]
    rw [show (∑ s' : ι, ∑ s : ι, ∑ a' : Fin (dims s'), ∑ i' : Fin (dims t),
          ∑ a : Fin (dims s), ∑ i : Fin (dims t),
          conj (cgME s' t α a' i' p) * conj (u s' a' i') * (cgME s t α a i p * u s a i)) =
        (∑ s' : ι, ∑ a' : Fin (dims s'), ∑ s : ι, ∑ i' : Fin (dims t),
          ∑ a : Fin (dims s), ∑ i : Fin (dims t),
          conj (cgME s' t α a' i' p) * conj (u s' a' i') * (cgME s t α a i p * u s a i)) from by
      exact Finset.sum_congr rfl (fun s' _ => by rw [Finset.sum_comm])]
    rw [show (∑ s' : ι, ∑ a' : Fin (dims s'), ∑ s : ι, ∑ i' : Fin (dims t),
          ∑ a : Fin (dims s), ∑ i : Fin (dims t),
          conj (cgME s' t α a' i' p) * conj (u s' a' i') * (cgME s t α a i p * u s a i)) =
        (∑ s' : ι, ∑ a' : Fin (dims s'), ∑ i' : Fin (dims t), ∑ s : ι,
          ∑ a : Fin (dims s), ∑ i : Fin (dims t),
          conj (cgME s' t α a' i' p) * conj (u s' a' i') * (cgME s t α a i p * u s a i)) from by
      exact Finset.sum_congr rfl (fun s' _ => Finset.sum_congr rfl (fun a' _ =>
        by rw [Finset.sum_comm]))]
  ]
  -- Step 4: Exchange (α,p) sum to inside, reassociate, and factor
  rw [show (∑ α : ι, ∑ p : Fin (dims α),
      ∑ s' : ι, ∑ a' : Fin (dims s'), ∑ i' : Fin (dims t),
      ∑ s : ι, ∑ a : Fin (dims s), ∑ i : Fin (dims t),
        conj (cgME s' t α a' i' p) * conj (u s' a' i') * (cgME s t α a i p * u s a i)) =
    ∑ (s : ι), ∑ (a : Fin (dims s)), ∑ (i : Fin (dims t)),
      ∑ (s' : ι), ∑ (a' : Fin (dims s')), ∑ (i' : Fin (dims t)),
        conj (u s' a' i') * u s a i *
        (∑ (α : ι), ∑ (p : Fin (dims α)),
          conj (cgME s' t α a' i' p) * cgME s t α a i p) from ?_]
  · -- Step 6: Apply hcgME_unitary / hcgME_cross_rep, collapse delta
    congr 1; ext s; congr 1; ext a; congr 1; ext i
    -- Goal: ∑ s', ∑ a', ∑ i', conj(u s' a' i') * u s a i * (inner sum) = conj(u s a i) * u s a i
    rw [Finset.sum_eq_single s]
    · -- s' = s case: inner sum = hcgME_unitary → if a' = a ∧ i' = i then 1 else 0
      simp only [hcgME_unitary]
      rw [Finset.sum_eq_single a]
      · -- a' = a case
        rw [Finset.sum_eq_single i]
        · -- i' = i case
          rw [if_pos (And.intro rfl rfl)]
          ring
        · -- i' ≠ i case
          intro i' _ hi'i
          rw [if_neg (fun h => hi'i h.2)]
          ring
        · -- i ∉ univ case
          intro h; exact absurd (Finset.mem_univ i) h
      · -- a' ≠ a case
        intro a' _ ha'a
        apply Finset.sum_eq_zero
        intro i' _
        rw [if_neg (fun h => ha'a h.1)]
        ring
      · -- a ∉ univ case
        intro h; exact absurd (Finset.mem_univ a) h
    · -- s' ≠ s case: inner sum = 0 (by hcgME_cross_rep)
      intro s' _ hs's
      apply Finset.sum_eq_zero
      intro a' _
      apply Finset.sum_eq_zero
      intro i' _
      rw [hcgME_cross_rep s' s t hs's a' i' a i]
      ring
    · -- s ∉ univ case
      intro h; exact absurd (Finset.mem_univ s) h
  · -- Step 5: 21 sum swaps + reassociation + factoring
    -- Phase 1: Move s to front (5 swaps: swap s with i', a', s', p, α)
    conv => enter [1, 2]; ext; enter [2]; ext; enter [2]; ext; enter [2]; ext; rw [Finset.sum_comm]
    conv => enter [1, 2]; ext; enter [2]; ext; enter [2]; ext; rw [Finset.sum_comm]
    conv => enter [1, 2]; ext; enter [2]; ext; rw [Finset.sum_comm]
    conv => enter [1, 2]; ext; rw [Finset.sum_comm]
    conv => enter [1]; rw [Finset.sum_comm]
    -- Phase 2: Move a to position 2 (5 swaps: swap a with i', a', s', p, α)
    conv => enter [1, 2]; ext; enter [2]; ext; enter [2]; ext; enter [2]; ext; enter [2]; ext; rw [Finset.sum_comm]
    conv => enter [1, 2]; ext; enter [2]; ext; enter [2]; ext; enter [2]; ext; rw [Finset.sum_comm]
    conv => enter [1, 2]; ext; enter [2]; ext; enter [2]; ext; rw [Finset.sum_comm]
    conv => enter [1, 2]; ext; enter [2]; ext; rw [Finset.sum_comm]
    conv => enter [1, 2]; ext; rw [Finset.sum_comm]
    -- Phase 3: Move i to position 3 (5 swaps: swap i with i', a', s', p, α)
    conv => enter [1, 2]; ext; enter [2]; ext; enter [2]; ext; enter [2]; ext; enter [2]; ext; enter [2]; ext; rw [Finset.sum_comm]
    conv => enter [1, 2]; ext; enter [2]; ext; enter [2]; ext; enter [2]; ext; enter [2]; ext; rw [Finset.sum_comm]
    conv => enter [1, 2]; ext; enter [2]; ext; enter [2]; ext; enter [2]; ext; rw [Finset.sum_comm]
    conv => enter [1, 2]; ext; enter [2]; ext; enter [2]; ext; rw [Finset.sum_comm]
    conv => enter [1, 2]; ext; enter [2]; ext; rw [Finset.sum_comm]
    -- Phase 4: Move s' to position 4 (2 swaps: swap s' with p, α)
    conv => enter [1, 2]; ext; enter [2]; ext; enter [2]; ext; enter [2]; ext; rw [Finset.sum_comm]
    conv => enter [1, 2]; ext; enter [2]; ext; enter [2]; ext; rw [Finset.sum_comm]
    -- Phase 5: Move a' to position 5 (2 swaps: swap a' with p, α)
    conv => enter [1, 2]; ext; enter [2]; ext; enter [2]; ext; enter [2]; ext; enter [2]; ext; rw [Finset.sum_comm]
    conv => enter [1, 2]; ext; enter [2]; ext; enter [2]; ext; enter [2]; ext; rw [Finset.sum_comm]
    -- Phase 6: Move i' to position 6 (2 swaps: swap i' with p, α)
    conv => enter [1, 2]; ext; enter [2]; ext; enter [2]; ext; enter [2]; ext; enter [2]; ext; enter [2]; ext; rw [Finset.sum_comm]
    conv => enter [1, 2]; ext; enter [2]; ext; enter [2]; ext; enter [2]; ext; enter [2]; ext; rw [Finset.sum_comm]
    -- Reassociation + factoring: conj(cgME) * conj(u) * (cgME * u) → conj(u) * u * (conj(cgME) * cgME)
    -- then factor conj(u) * u out of the (α, p) sum
    rw [show (∑ (s : ι), ∑ (a : Fin (dims s)), ∑ (i : Fin (dims t)),
      ∑ (s' : ι), ∑ (a' : Fin (dims s')), ∑ (i' : Fin (dims t)),
      ∑ (α : ι), ∑ (p : Fin (dims α)),
        conj (cgME s' t α a' i' p) * conj (u s' a' i') * (cgME s t α a i p * u s a i)) =
      (∑ (s : ι), ∑ (a : Fin (dims s)), ∑ (i : Fin (dims t)),
      ∑ (s' : ι), ∑ (a' : Fin (dims s')), ∑ (i' : Fin (dims t)),
        conj (u s' a' i') * u s a i *
        (∑ (α : ι), ∑ (p : Fin (dims α)),
          conj (cgME s' t α a' i' p) * cgME s t α a i p)) from by
      exact Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun a _ =>
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun s' _ =>
          Finset.sum_congr rfl (fun a' _ => Finset.sum_congr rfl (fun i' _ => by
            have h_term : ∀ (α : ι) (p : Fin (dims α)),
                conj (cgME s' t α a' i' p) * conj (u s' a' i') * (cgME s t α a i p * u s a i) =
                conj (u s' a' i') * u s a i * (conj (cgME s' t α a' i' p) * cgME s t α a i p) := by
              intro α p; ring
            rw [Finset.sum_congr rfl (fun α _ =>
              Finset.sum_congr rfl (fun p _ => h_term α p))]
            simp only [← Finset.mul_sum]))))))]
#print axioms cgME_multirep_isometry_normSq

/-! ## 3-fold CG isometry (composed Parseval for the 3D cascade)

The 3D Lüscher cascade applies the CG change-of-basis TWICE in sequence:
1. First CG: `(s1, s2) → ν` (combining reps s1, s2 → intermediate ν)
2. Second CG: `(ν, s3) → α` (combining ν, s3 → final α)

The 3-fold CG coefficient is `∑_{ν,r} cgME s1 s2 ν a1 a2 r * cgME ν s3 α r a3 p`.
The 3-fold isometry (composed Parseval) says this combined change-of-basis is an
isometry: it preserves the ℓ² norm.

This is proved by COMPOSING the multi-rep isometry (`cgME_multirep_isometry_normSq`)
with the single isometry (`cgME_isometry_normSq`):
1. Rewrite the LHS inner sum to the multi-rep isometry form (distribute + reorder +
   reassociate + factor).
2. Apply the multi-rep isometry (second CG: `(ν, s3) → α` with ν summed).
3. Reorder the RHS to apply the single isometry for each fixed `a3`.
4. Apply the single isometry (first CG: `(s1, s2) → ν` for each `a3`).
5. Reorder to the final form.

Hypotheses: `hcgME_unitary` + `hcgME_cross_rep` (same as the multi-rep isometry).
0 sorries, 0 new axioms. -/

set_option maxHeartbeats 1000000 in
lemma cgME_3fold_isometry_normSq
    {ι : Type*} [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (cgME : ∀ (s t ν : ι), Fin (dims s) → Fin (dims t) → Fin (dims ν) → ℂ)
    (hcgME_unitary : ∀ (s t : ι) (a b : Fin (dims s)) (i j : Fin (dims t)),
        ∑ ν : ι, ∑ p : Fin (dims ν),
          conj (cgME s t ν a i p) * cgME s t ν b j p =
          if a = b ∧ i = j then (1 : ℂ) else 0)
    (hcgME_cross_rep : ∀ (s s' t : ι), s ≠ s' →
        ∀ (a : Fin (dims s)) (i : Fin (dims t)) (a' : Fin (dims s')) (i' : Fin (dims t)),
        ∑ α : ι, ∑ p : Fin (dims α),
          conj (cgME s t α a i p) * cgME s' t α a' i' p = 0)
    (s1 s2 s3 : ι) (v : Fin (dims s1) → Fin (dims s2) → Fin (dims s3) → ℂ) :
    ∑ (α : ι), ∑ (p : Fin (dims α)),
      Complex.normSq (∑ (a1 : Fin (dims s1)), ∑ (a2 : Fin (dims s2)), ∑ (a3 : Fin (dims s3)),
        (∑ (ν : ι), ∑ (r : Fin (dims ν)),
          cgME s1 s2 ν a1 a2 r * cgME ν s3 α r a3 p) * v a1 a2 a3) =
    ∑ (a1 : Fin (dims s1)), ∑ (a2 : Fin (dims s2)), ∑ (a3 : Fin (dims s3)),
      Complex.normSq (v a1 a2 a3) := by
  -- Step 1: Rewrite LHS inner sum to multi-rep isometry form
  have hlhs : ∀ (α : ι) (p : Fin (dims α)),
      (∑ (a1 : Fin (dims s1)), ∑ (a2 : Fin (dims s2)), ∑ (a3 : Fin (dims s3)),
        (∑ (ν : ι), ∑ (r : Fin (dims ν)),
          cgME s1 s2 ν a1 a2 r * cgME ν s3 α r a3 p) * v a1 a2 a3) =
      (∑ (ν : ι), ∑ (r : Fin (dims ν)), ∑ (a3 : Fin (dims s3)),
        cgME ν s3 α r a3 p * (∑ (a1 : Fin (dims s1)), ∑ (a2 : Fin (dims s2)),
          cgME s1 s2 ν a1 a2 r * v a1 a2 a3)) := by
    intro α p
    simp only [Finset.sum_mul]
    -- 8 swaps: (a1, a2, a3, ν, r) → (ν, r, a3, a1, a2)
    -- Phase 1: Move ν to front (3 swaps: swap ν with a3, a2, a1)
    conv => enter [1, 2]; ext; enter [2]; ext; rw [Finset.sum_comm]
    conv => enter [1, 2]; ext; rw [Finset.sum_comm]
    conv => enter [1]; rw [Finset.sum_comm]
    -- Phase 2: Move r to position 2 (3 swaps: swap r with a3, a2, a1)
    conv => enter [1, 2]; ext; enter [2]; ext; enter [2]; ext; rw [Finset.sum_comm]
    conv => enter [1, 2]; ext; enter [2]; ext; rw [Finset.sum_comm]
    conv => enter [1, 2]; ext; rw [Finset.sum_comm]
    -- Phase 3: Move a3 to position 3 (2 swaps: swap a3 with a2, a1)
    conv => enter [1, 2]; ext; enter [2]; ext; enter [2]; ext; rw [Finset.sum_comm]
    conv => enter [1, 2]; ext; enter [2]; ext; rw [Finset.sum_comm]
    -- Reassociate and factor: cgME s1 s2 * cgME ν s3 * v → cgME ν s3 * (cgME s1 s2 * v)
    apply Finset.sum_congr rfl; intro ν _; apply Finset.sum_congr rfl; intro r _
    apply Finset.sum_congr rfl; intro a3 _
    have h_term : ∀ (a1 : Fin (dims s1)) (a2 : Fin (dims s2)),
        cgME s1 s2 ν a1 a2 r * cgME ν s3 α r a3 p * v a1 a2 a3 =
        cgME ν s3 α r a3 p * (cgME s1 s2 ν a1 a2 r * v a1 a2 a3) := by
      intro a1 a2; ring
    rw [Finset.sum_congr rfl (fun a1 _ => Finset.sum_congr rfl (fun a2 _ => h_term a1 a2))]
    simp only [← Finset.mul_sum]
  -- Apply hlhs to rewrite LHS
  rw [show (∑ (α : ι), ∑ (p : Fin (dims α)),
        Complex.normSq (∑ (a1 : Fin (dims s1)), ∑ (a2 : Fin (dims s2)), ∑ (a3 : Fin (dims s3)),
          (∑ (ν : ι), ∑ (r : Fin (dims ν)),
            cgME s1 s2 ν a1 a2 r * cgME ν s3 α r a3 p) * v a1 a2 a3)) =
      (∑ (α : ι), ∑ (p : Fin (dims α)),
        Complex.normSq (∑ (ν : ι), ∑ (r : Fin (dims ν)), ∑ (a3 : Fin (dims s3)),
          cgME ν s3 α r a3 p * (∑ (a1 : Fin (dims s1)), ∑ (a2 : Fin (dims s2)),
            cgME s1 s2 ν a1 a2 r * v a1 a2 a3))) from by
    exact Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun p _ =>
      congrArg Complex.normSq (hlhs α p)))]
  -- Step 2: Apply multi-rep isometry (second CG: (ν, s3) → α with ν summed)
  rw [cgME_multirep_isometry_normSq dims cgME hcgME_unitary hcgME_cross_rep s3
    (fun (ν : ι) (r : Fin (dims ν)) (a3 : Fin (dims s3)) =>
      ∑ (a1 : Fin (dims s1)), ∑ (a2 : Fin (dims s2)),
        cgME s1 s2 ν a1 a2 r * v a1 a2 a3)]
  -- Step 3: Reorder RHS from (ν, r, a3) to (a3, ν, r)
  conv => enter [1, 2]; ext; rw [Finset.sum_comm]
  conv => enter [1]; rw [Finset.sum_comm]
  -- Step 4: Apply single isometry for each a3 (first CG: (s1, s2) → ν)
  rw [show (∑ (a3 : Fin (dims s3)), ∑ (ν : ι), ∑ (r : Fin (dims ν)),
        Complex.normSq (∑ (a1 : Fin (dims s1)), ∑ (a2 : Fin (dims s2)),
          cgME s1 s2 ν a1 a2 r * v a1 a2 a3)) =
      (∑ (a3 : Fin (dims s3)), ∑ (a1 : Fin (dims s1)), ∑ (a2 : Fin (dims s2)),
        Complex.normSq (v a1 a2 a3)) from by
    exact Finset.sum_congr rfl (fun a3 _ =>
      cgME_isometry_normSq dims cgME hcgME_unitary s1 s2 (fun a1 a2 => v a1 a2 a3))]
  -- Step 5: Reorder from (a3, a1, a2) to (a1, a2, a3)
  conv => enter [1]; rw [Finset.sum_comm]
  conv => enter [1, 2]; ext; rw [Finset.sum_comm]

#print axioms cgME_3fold_isometry_normSq

end YangMills
