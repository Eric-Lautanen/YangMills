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

end YangMills
