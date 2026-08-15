/-
# Reflection Positivity: OS Decomposition
-/

import YangMills.Proofs.ReflectionPositivity.PeriodicLattice

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open scoped BigOperators
open MeasureTheory
open Complex
open scoped ComplexConjugate

namespace YangMills
namespace Lattice
/-! ### Osterwalder-Seiler decomposition (plaquette-based) -/
open scoped BigOperators

/-- Index type for oriented plaquettes on a periodic lattice: (base site, μ, ν). -/
abbrev PlaquetteIndex (T L : ℕ) : Type := PeriodicSite T L × Fin 4 × Fin 4

instance (T L : ℕ) [NeZero T] [NeZero L] : Fintype (PlaquetteIndex T L) :=
  inferInstanceAs (Fintype (PeriodicSite T L × Fin 4 × Fin 4))

/-- Cyclic permutation of trace for 4 matrices: Tr(ABCD) = Tr(BCDA). -/
lemma trace_cyclic_four (N : ℕ) (A B C D : Matrix (Fin N) (Fin N) ℂ) :
    Matrix.trace (A * B * C * D) = Matrix.trace (B * C * D * A) := by
  calc
    Matrix.trace (A * B * C * D) = Matrix.trace (D * (A * B * C)) := by
      rw [Matrix.trace_mul_comm (A * B * C) D]
    _ = Matrix.trace (D * A * B * C) := by noncomm_ring
    _ = Matrix.trace ((D * A) * (B * C)) := by noncomm_ring
    _ = Matrix.trace ((B * C) * (D * A)) := Matrix.trace_mul_comm (D * A) (B * C)
    _ = Matrix.trace (B * C * D * A) := by noncomm_ring
/-- For A ∈ SU(N), Re Tr(A) = Re Tr(A⁻¹). -/
lemma trace_re_inv (N : ℕ) (A : SU N) :
    ((Matrix.trace ((A : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) =
    ((Matrix.trace (((A⁻¹ : SU N) : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) := by
  have hstar : (A⁻¹ : SU N) = (star A : SU N) := by
    simpa using (Matrix.star_eq_inv (A : SU N)).symm
  have h_trace_star : Matrix.trace (star ((A : Matrix (Fin N) (Fin N) ℂ))) =
      star (Matrix.trace ((A : Matrix (Fin N) (Fin N) ℂ))) := by
    simp [Matrix.trace, map_sum]
  calc
    ((Matrix.trace ((A : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) =
        ((star (Matrix.trace ((A : Matrix (Fin N) (Fin N) ℂ)))).re : ℝ) := by simp
    _ = ((Matrix.trace (star ((A : Matrix (Fin N) (Fin N) ℂ)))).re : ℝ) := by
      simp [h_trace_star]
    _ = ((Matrix.trace (((A⁻¹ : SU N) : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) := by simp [hstar]

/-- The sum over all oriented plaquettes (n; μ, ν) where all four corners have
positive signed time. This is the correct positive-time part of the
Osterwalder-Seiler decomposition. -/
noncomputable def wilsonActionOSPositive (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) : ℝ :=
  ∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4,
    if signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
       signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
       signedTime T (addVectorPeriodic T L n ν).time > 0 then
      plaquetteContribution N β U n μ ν
    else 0

/-- The sum over all oriented plaquettes (n; μ, ν) where all four corners have
negative signed time. This is the correct negative-time part of the
Osterwalder-Seiler decomposition. -/
noncomputable def wilsonActionOSNegative (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) : ℝ :=
  ∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4,
    if signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
       signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
       signedTime T (addVectorPeriodic T L n ν).time < 0 then
      plaquetteContribution N β U n μ ν
    else 0

/-- The sum over the remaining oriented plaquettes (those with corners on both sides
of the time interface). This is the interface part of the
Osterwalder-Seiler decomposition. -/
noncomputable def wilsonActionOSInterface (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) : ℝ :=
  ∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4,
    if ¬ (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
          signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
          signedTime T (addVectorPeriodic T L n ν).time > 0) ∧
       ¬ (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
          signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
          signedTime T (addVectorPeriodic T L n ν).time < 0) then
      plaquetteContribution N β U n μ ν
    else 0

/--
For each oriented plaquette (n; μ, ν), exactly one of the three conditions holds:
positive (all corners > 0), negative (all corners < 0), or interface (the rest).
-/
lemma plaquette_classification (T L : ℕ) [NeZero T] [NeZero L] (n : PeriodicSite T L) (μ ν : Fin 4) :
    (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
     signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
     signedTime T (addVectorPeriodic T L n ν).time > 0) ∨
    (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
     signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
     signedTime T (addVectorPeriodic T L n ν).time < 0) ∨
    (¬ (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
        signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
        signedTime T (addVectorPeriodic T L n ν).time > 0) ∧
     ¬ (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
        signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
        signedTime T (addVectorPeriodic T L n ν).time < 0)) := by
  by_cases hpos : signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
                  signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
                  signedTime T (addVectorPeriodic T L n ν).time > 0
  · exact Or.inl hpos
  · by_cases hneg : signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
                   signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
                   signedTime T (addVectorPeriodic T L n ν).time < 0
    · exact Or.inr (Or.inl hneg)
    · exact Or.inr (Or.inr ⟨hpos, hneg⟩)

/--
The total Wilson action decomposes into positive, negative, and interface parts
(plaquette-based OS decomposition):
    S_W = S_OS⁺ + S_OS⁻ + S_OS_int
-/
lemma total_decomposition_os_periodic (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) :
    wilsonActionFinite N β (Finset.univ : Finset (PeriodicSite T L)) U =
    wilsonActionOSPositive N T L β U +
    wilsonActionOSNegative N T L β U +
    wilsonActionOSInterface N T L β U := by
  unfold wilsonActionOSPositive wilsonActionOSNegative wilsonActionOSInterface wilsonActionFinite
  have h_split (n : PeriodicSite T L) (μ ν : Fin 4) : plaquetteContribution N β U n μ ν =
    (if signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
         signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
         signedTime T (addVectorPeriodic T L n ν).time > 0 then
      plaquetteContribution N β U n μ ν else 0) +
    (if signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
         signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
         signedTime T (addVectorPeriodic T L n ν).time < 0 then
      plaquetteContribution N β U n μ ν else 0) +
    (if ¬ (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
          signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
          signedTime T (addVectorPeriodic T L n ν).time > 0) ∧
       ¬ (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
          signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
          signedTime T (addVectorPeriodic T L n ν).time < 0) then
      plaquetteContribution N β U n μ ν else 0) := by
    rcases plaquette_classification T L n μ ν with (⟨h1, h2, h3, h4⟩|⟨h1, h2, h3, h4⟩|⟨hnpos, hnneg⟩)
    · -- All signed times > 0
      have h_neg : ¬ (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
          signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
          signedTime T (addVectorPeriodic T L n ν).time < 0) := by
        intro h; rcases h with ⟨hn1, hn2, hn3, hn4⟩; have := h1; linarith
      have h_int : ¬ (¬ (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
          signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
          signedTime T (addVectorPeriodic T L n ν).time > 0) ∧
        ¬ (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
          signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
          signedTime T (addVectorPeriodic T L n ν).time < 0)) := by
        intro h; rcases h with ⟨hnpos', hnneg'⟩; apply hnpos'; exact ⟨h1, h2, h3, h4⟩
      calc
        plaquetteContribution N β U n μ ν
            = (plaquetteContribution N β U n μ ν) + 0 + 0 := by ring
        _ = (if signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
              signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
              signedTime T (addVectorPeriodic T L n ν).time > 0 then
              plaquetteContribution N β U n μ ν else 0) +
            (if signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
              signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
              signedTime T (addVectorPeriodic T L n ν).time < 0 then
              plaquetteContribution N β U n μ ν else 0) +
            (if ¬ (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
                  signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
                  signedTime T (addVectorPeriodic T L n ν).time > 0) ∧
               ¬ (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
                  signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
                  signedTime T (addVectorPeriodic T L n ν).time < 0) then
              plaquetteContribution N β U n μ ν else 0) := by
          rw [if_pos ⟨h1, h2, h3, h4⟩, if_neg h_neg, if_neg h_int]
    · -- All signed times < 0
      have h_pos : ¬ (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
          signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
          signedTime T (addVectorPeriodic T L n ν).time > 0) := by
        intro h; rcases h with ⟨hp1, hp2, hp3, hp4⟩; have := h1; linarith
      have h_int : ¬ (¬ (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
          signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
          signedTime T (addVectorPeriodic T L n ν).time > 0) ∧
        ¬ (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
          signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
          signedTime T (addVectorPeriodic T L n ν).time < 0)) := by
        intro h; rcases h with ⟨hnpos', hnneg'⟩; apply hnneg'; exact ⟨h1, h2, h3, h4⟩
      calc
        plaquetteContribution N β U n μ ν
            = 0 + (plaquetteContribution N β U n μ ν) + 0 := by ring
        _ = (if signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
              signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
              signedTime T (addVectorPeriodic T L n ν).time > 0 then
              plaquetteContribution N β U n μ ν else 0) +
            (if signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
              signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
              signedTime T (addVectorPeriodic T L n ν).time < 0 then
              plaquetteContribution N β U n μ ν else 0) +
            (if ¬ (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
                  signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
                  signedTime T (addVectorPeriodic T L n ν).time > 0) ∧
               ¬ (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
                  signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
                  signedTime T (addVectorPeriodic T L n ν).time < 0) then
              plaquetteContribution N β U n μ ν else 0) := by
          rw [if_neg h_pos, if_pos ⟨h1, h2, h3, h4⟩, if_neg h_int]
    · -- Interface case: neither all positive nor all negative
      have h_int_cond : (¬ (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
          signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
          signedTime T (addVectorPeriodic T L n ν).time > 0) ∧
        ¬ (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
          signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
          signedTime T (addVectorPeriodic T L n ν).time < 0)) := ⟨hnpos, hnneg⟩
      calc
        plaquetteContribution N β U n μ ν
            = 0 + 0 + (plaquetteContribution N β U n μ ν) := by ring
        _ = (if signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
              signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
              signedTime T (addVectorPeriodic T L n ν).time > 0 then
              plaquetteContribution N β U n μ ν else 0) +
            (if signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
              signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
              signedTime T (addVectorPeriodic T L n ν).time < 0 then
              plaquetteContribution N β U n μ ν else 0) +
            (if ¬ (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
                  signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
                  signedTime T (addVectorPeriodic T L n ν).time > 0) ∧
               ¬ (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
                  signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
                  signedTime T (addVectorPeriodic T L n ν).time < 0) then
              plaquetteContribution N β U n μ ν else 0) := by
          rw [if_neg hnpos, if_neg hnneg, if_pos h_int_cond]
  have h_sum : ∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4, plaquetteContribution N β U n μ ν =
    ∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4,
      ((if signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
            signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
            signedTime T (addVectorPeriodic T L n ν).time > 0 then
          plaquetteContribution N β U n μ ν else 0) +
        (if signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
            signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
            signedTime T (addVectorPeriodic T L n ν).time < 0 then
          plaquetteContribution N β U n μ ν else 0) +
        (if ¬ (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
              signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
              signedTime T (addVectorPeriodic T L n ν).time > 0) ∧
           ¬ (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
              signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
              signedTime T (addVectorPeriodic T L n ν).time < 0) then
          plaquetteContribution N β U n μ ν else 0)) := by
    refine Finset.sum_congr rfl (λ n hn => ?_)
    refine Finset.sum_congr rfl (λ μ hμ => ?_)
    refine Finset.sum_congr rfl (λ ν hν => ?_)
    exact h_split n μ ν
  rw [h_sum]
  simp [Finset.sum_add_distrib]

/-! ### Concrete-to-abstract plaquette-product bridge

These lemmas connect the *concrete* Wilson action (with its specific sign
convention `S_p = β(1 - (1/N) Re Tr(U_∂p))`) to the *abstract* plaquette-product
form `∏_p exp(c · Re Tr(g₁g₂g₃⁻¹g₄⁻¹))` with `c ≥ 0` that the
`interface_kernel_character_expansion` lemma (in `PeterWeyl.lean`) operates on.

This is the "exp-of-sum = product-of-exps" step of the KEY GAP identified in
`docs/transfer_matrix_positivity_design.md` §8.8 (task #46): the concrete
transfer-matrix kernel `exp(-β·S_OS)` must be rewritten as a product of
plaquette Boltzmann factors before the abstract character-expansion lemma can
be applied.  These lemmas are pure algebra (0 axioms, 0 sorries). -/

/-- The single-plaquette Boltzmann factor `exp(-S_p)` factors as a positive
constant `exp(-β)` times `exp(c·Re Tr(U_∂p))` with `c = β/N ≥ 0` (for `β ≥ 0`,
`1 ≤ N`).

This is the atomic building block of the concrete↔abstract bridge: it shows
that each plaquette's contribution to the Boltzmann factor matches the abstract
form `exp(c·Re Tr(g₁g₂g₃⁻¹g₄⁻¹))` (with `c ≥ 0`) up to a positive constant
that can be absorbed into the overall normalization.  The plaquette product
`plaquetteProduct = U(n,μ)·U(n+e_μ,ν)·U(n+e_μ+e_ν,μ)⁻¹·U(n+e_ν,ν)⁻¹` already has
the 3rd/4th links inverted, matching the abstract form.

This is the same decomposition used internally by `plaquetteContributionPD`
(in `BoltzmannFactor.lean`); it is extracted here as a standalone equality lemma
so it can be composed with `exp_neg_wilsonActionFinite_eq_prod` to bridge the
concrete kernel `exp(-S_W)` to the abstract plaquette-product form. -/
lemma plaquetteContribution_exp_decomp (N : ℕ) (β : ℝ)
    {Λ : Type} [AddVector Λ] (U : LinkVariable (SU N) Λ) (n : Λ) (μ ν : Fin 4) :
    Real.exp (-plaquetteContribution N β U n μ ν) =
    Real.exp (-β) *
    Real.exp ((β / N) *
      Complex.re (Matrix.trace ((plaquetteProduct N U n μ ν : Matrix (Fin N) (Fin N) ℂ)))) := by
  unfold plaquetteContribution
  have h : -(β * (1 - (1 / (N : ℝ)) *
      Complex.re (Matrix.trace ((plaquetteProduct N U n μ ν : Matrix (Fin N) (Fin N) ℂ))))) =
      (-β) + (β / N) *
      Complex.re (Matrix.trace ((plaquetteProduct N U n μ ν : Matrix (Fin N) (Fin N) ℂ))) := by
    rw [div_eq_inv_mul]; ring
  rw [h, Real.exp_add]

/-- The coupling constant `c = β/N` for the abstract plaquette-product form is
non-negative when `β ≥ 0` and `1 ≤ N`.  This is the hypothesis `0 ≤ c` required
by `peterWeyl_clebschGordan_plaquette` and `interface_kernel_character_expansion`. -/
lemma plaquetteBoltzmann_coupling_nonneg (N : ℕ) (β : ℝ) (hβ : 0 ≤ β) (hN : 1 ≤ N) :
    0 ≤ β / N := by
  exact div_nonneg hβ (Nat.cast_nonneg N)

/-- The per-plaquette constant `exp(-β)` is positive. -/
lemma plaquetteBoltzmann_const_pos (β : ℝ) : 0 < Real.exp (-β) :=
  Real.exp_pos _

/-- **Transfer-matrix kernel per-plaquette factorization.** The factor
`exp(-β·S_p)` (which appears in the transfer-matrix kernel `exp(-β·S_W) =
∏ exp(-β·S_p)`, since `osG(U)·osG(θU) = f(U)·f(θU)·exp(-β·S_W)`) decomposes as
`exp(-β²)·exp((β²/N)·Re Tr(U_∂p))` with coupling `c = β²/N ≥ 0`.

This is the version needed for the concrete transfer-matrix kernel: the `G`
function uses `exp(-β·S⁺)` (with the extra β), so the per-plaquette factor is
`exp(-β·S_p) = exp(-β²)·exp((β²/N)·Re Tr)`, NOT `exp(-S_p)`.  The coupling
`c = β²/N` is non-negative for all `β` (since `β² ≥ 0`) and `1 ≤ N`. -/
lemma plaquetteContribution_exp_decomp_tm (N : ℕ) (β : ℝ)
    {Λ : Type} [AddVector Λ] (U : LinkVariable (SU N) Λ) (n : Λ) (μ ν : Fin 4) :
    Real.exp (-β * plaquetteContribution N β U n μ ν) =
    Real.exp (-(β * β)) *
    Real.exp ((β * β / N) *
      Complex.re (Matrix.trace ((plaquetteProduct N U n μ ν : Matrix (Fin N) (Fin N) ℂ)))) := by
  unfold plaquetteContribution
  have h : -β * (β * (1 - (1 / (N : ℝ)) *
      Complex.re (Matrix.trace ((plaquetteProduct N U n μ ν : Matrix (Fin N) (Fin N) ℂ))))) =
      -(β * β) + (β * β / N) *
      Complex.re (Matrix.trace ((plaquetteProduct N U n μ ν : Matrix (Fin N) (Fin N) ℂ))) := by
    field_simp; ring
  rw [h, Real.exp_add]

/-- The transfer-matrix coupling `c = β²/N` is non-negative for all `β` and `1 ≤ N`.
Unlike `plaquetteBoltzmann_coupling_nonneg`, this does NOT require `β ≥ 0` (since
`β² ≥ 0` always). -/
lemma plaquetteBoltzmann_tm_coupling_nonneg (N : ℕ) (β : ℝ) (hN : 1 ≤ N) :
    0 ≤ β * β / N := by
  have hβ : 0 ≤ β * β := by nlinarith [sq_nonneg β, pow_two β]
  exact div_nonneg hβ (Nat.cast_nonneg N)

/-- The transfer-matrix per-plaquette constant `exp(-β²)` is positive. -/
lemma plaquetteBoltzmann_tm_const_pos (β : ℝ) : 0 < Real.exp (-(β * β)) :=
  Real.exp_pos _

/-- **exp-of-sum = product-of-exps for the transfer-matrix kernel.** The
transfer-matrix Boltzmann factor `exp(-β·S_W)` factorises as a product of
per-plaquette factors `exp(-β·S_p)`:

    exp(-β·S_W[U]) = ∏_{n ∈ sites} ∏_{μ : Fin 4} ∏_{ν : Fin 4} exp(-β·S_p(n,μ,ν))

This is the transfer-matrix analogue of `exp_neg_wilsonActionFinite_eq_prod`
(in `BoltzmannFactor.lean`), with the extra factor of `β` that the `G`/`osG`
functions introduce.  Pure algebra — no representation theory, no axioms beyond
the standard three. -/
lemma exp_neg_beta_wilsonActionFinite_eq_prod (N : ℕ) (β : ℝ)
    {Λ : Type} [AddVector Λ]
    (sites : Finset Λ) (U : Lattice.LinkVariable (SU N) Λ) :
    Real.exp (-β * Lattice.wilsonActionFinite N β sites U) =
    ∏ n ∈ sites, ∏ μ : Fin 4, ∏ ν : Fin 4,
      Real.exp (-β * Lattice.plaquetteContribution N β U n μ ν) := by
  simp only [Lattice.wilsonActionFinite, ← Finset.sum_neg_distrib, Real.exp_sum,
    Finset.mul_sum]

#print axioms plaquetteContribution_exp_decomp
#print axioms plaquetteBoltzmann_coupling_nonneg
#print axioms plaquetteBoltzmann_const_pos
#print axioms plaquetteContribution_exp_decomp_tm
#print axioms plaquetteBoltzmann_tm_coupling_nonneg
#print axioms plaquetteBoltzmann_tm_const_pos
#print axioms exp_neg_beta_wilsonActionFinite_eq_prod

