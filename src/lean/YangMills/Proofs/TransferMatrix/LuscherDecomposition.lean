/-
# Transfer Matrix: Lüscher Decomposition (Spatial/Temporal Split of OS Action)

This file formalizes Step A.4 of the Lüscher decomposition T = V^{1/2}·U·V^{1/2}
(§8.11.67 of `docs/transfer_matrix_positivity_design.md`).

The OS action components (positive, negative, interface) are split into spatial
plaquettes (both directions nonzero — within a single time slice) and temporal
plaquettes (at least one direction is the time direction 0 — spanning two time
slices).  The spatial part defines the multiplication operator V (PD by
`spatialBoltzmannPD`); the temporal part defines the integral operator U
(positive by the Lüscher cascade — Step B, not yet formalized).

The kernel `exp(-β·(S⁺/2 + S⁺/2 + S_int))` then factors as
`exp(-β·(spatial part)) · exp(-β·(temporal part))` via `Real.exp_add`.
-/

import YangMills.Proofs.TransferMatrix.FullLattice

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open scoped BigOperators
open MeasureTheory
open Complex
open scoped ComplexConjugate

namespace YangMills
namespace Lattice
section TransferMatrix

/-! ## Spatial/temporal split of the OS action components (Step A.4)

Each OS action component (positive, negative, interface) decomposes into a
spatial part (plaquettes with both directions nonzero) and a temporal part
(plaquettes with at least one direction equal to 0).  The split is by
intersecting the time-signature condition with the direction condition. -/

/-- The spatial part of the OS-positive action: sum over plaquettes that are
OS-positive (all four corners at positive signed time) AND spatial
(both directions nonzero). -/
noncomputable def wilsonActionOSPositiveSpatial (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) : ℝ :=
  ∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4,
    if signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
       signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
       signedTime T (addVectorPeriodic T L n ν).time > 0 ∧
       μ ≠ 0 ∧ ν ≠ 0 then
      plaquetteContribution N β U n μ ν
    else 0

/-- The temporal part of the OS-positive action: sum over plaquettes that are
OS-positive AND temporal (at least one direction is the time direction 0). -/
noncomputable def wilsonActionOSPositiveTemporal (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) : ℝ :=
  ∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4,
    if signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
       signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
       signedTime T (addVectorPeriodic T L n ν).time > 0 ∧
       (μ = 0 ∨ ν = 0) then
      plaquetteContribution N β U n μ ν
    else 0

/-- The spatial part of the OS-negative action. -/
noncomputable def wilsonActionOSNegativeSpatial (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) : ℝ :=
  ∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4,
    if signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
       signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
       signedTime T (addVectorPeriodic T L n ν).time < 0 ∧
       μ ≠ 0 ∧ ν ≠ 0 then
      plaquetteContribution N β U n μ ν
    else 0

/-- The temporal part of the OS-negative action. -/
noncomputable def wilsonActionOSNegativeTemporal (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) : ℝ :=
  ∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4,
    if signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
       signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
       signedTime T (addVectorPeriodic T L n ν).time < 0 ∧
       (μ = 0 ∨ ν = 0) then
      plaquetteContribution N β U n μ ν
    else 0

/-- The spatial part of the OS-interface action. -/
noncomputable def wilsonActionOSInterfaceSpatial (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) : ℝ :=
  ∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4,
    if ¬ (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
          signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
          signedTime T (addVectorPeriodic T L n ν).time > 0) ∧
       ¬ (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
          signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
          signedTime T (addVectorPeriodic T L n ν).time < 0) ∧
       μ ≠ 0 ∧ ν ≠ 0 then
      plaquetteContribution N β U n μ ν
    else 0

/-- The temporal part of the OS-interface action. -/
noncomputable def wilsonActionOSInterfaceTemporal (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) : ℝ :=
  ∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4,
    if ¬ (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
          signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
          signedTime T (addVectorPeriodic T L n ν).time > 0) ∧
       ¬ (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
          signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
          signedTime T (addVectorPeriodic T L n ν).time < 0) ∧
       (μ = 0 ∨ ν = 0) then
      plaquetteContribution N β U n μ ν
    else 0

/-! ### Decomposition lemmas: each OS component = spatial + temporal -/

/-- **S⁺ = S_spatial⁺ + S_temporal⁺.** The OS-positive action decomposes into
spatial and temporal parts.  The spatial/temporal direction condition
(`μ ≠ 0 ∧ ν ≠ 0` vs `μ = 0 ∨ ν = 0`) partitions all plaquettes, so each
OS-positive plaquette contributes to exactly one of the two parts. -/
lemma wilsonActionOSPositive_eq_spatial_plus_temporal (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) :
    wilsonActionOSPositive N T L β U =
      wilsonActionOSPositiveSpatial N T L β U +
      wilsonActionOSPositiveTemporal N T L β U := by
  unfold wilsonActionOSPositive wilsonActionOSPositiveSpatial wilsonActionOSPositiveTemporal
  have h_split (n : PeriodicSite T L) (μ ν : Fin 4) :
      (if signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
            signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
            signedTime T (addVectorPeriodic T L n ν).time > 0 then
        plaquetteContribution N β U n μ ν else 0) =
      (if signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
            signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
            signedTime T (addVectorPeriodic T L n ν).time > 0 ∧
            μ ≠ 0 ∧ ν ≠ 0 then
        plaquetteContribution N β U n μ ν else 0) +
      (if signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
            signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
            signedTime T (addVectorPeriodic T L n ν).time > 0 ∧
            (μ = 0 ∨ ν = 0) then
        plaquetteContribution N β U n μ ν else 0) := by
    by_cases hP : signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
                  signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
                  signedTime T (addVectorPeriodic T L n ν).time > 0
    · rcases hP with ⟨h1, h2, h3, h4⟩
      by_cases hμ0 : μ = 0
      · rw [if_pos ⟨h1, h2, h3, h4⟩,
            if_neg (fun h => by rcases h with ⟨_, _, _, _, ⟨hμ_ne, _⟩⟩; exact hμ_ne hμ0),
            if_pos ⟨h1, h2, h3, h4, Or.inl hμ0⟩]; ring
      · by_cases hν0 : ν = 0
        · rw [if_pos ⟨h1, h2, h3, h4⟩,
              if_neg (fun h => by rcases h with ⟨_, _, _, _, ⟨_, hν_ne⟩⟩; exact hν_ne hν0),
              if_pos ⟨h1, h2, h3, h4, Or.inr hν0⟩]; ring
        · rw [if_pos ⟨h1, h2, h3, h4⟩,
              if_pos ⟨h1, h2, h3, h4, ⟨hμ0, hν0⟩⟩,
              if_neg (fun h => by rcases h with ⟨_, _, _, _, h | h⟩ <;> first
                | exact hμ0 h | exact hν0 h)]; ring
    · rw [if_neg hP,
          if_neg (fun h => by rcases h with ⟨h1, h2, h3, h4, _⟩; exact hP ⟨h1, h2, h3, h4⟩),
          if_neg (fun h => by rcases h with ⟨h1, h2, h3, h4, _⟩; exact hP ⟨h1, h2, h3, h4⟩)];
        ring
  have h_sum : ∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4,
      (if signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
            signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
            signedTime T (addVectorPeriodic T L n ν).time > 0 then
        plaquetteContribution N β U n μ ν else 0) =
    ∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4,
      ((if signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
            signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
            signedTime T (addVectorPeriodic T L n ν).time > 0 ∧
            μ ≠ 0 ∧ ν ≠ 0 then
        plaquetteContribution N β U n μ ν else 0) +
       (if signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
            signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
            signedTime T (addVectorPeriodic T L n ν).time > 0 ∧
            (μ = 0 ∨ ν = 0) then
        plaquetteContribution N β U n μ ν else 0)) := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    refine Finset.sum_congr rfl (fun ν _ => ?_)
    exact h_split n μ ν
  rw [h_sum]
  simp [Finset.sum_add_distrib]

#print axioms wilsonActionOSPositive_eq_spatial_plus_temporal

/-- **S⁻ = S_spatial⁻ + S_temporal⁻.** The OS-negative action decomposes into
spatial and temporal parts. -/
lemma wilsonActionOSNegative_eq_spatial_plus_temporal (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) :
    wilsonActionOSNegative N T L β U =
      wilsonActionOSNegativeSpatial N T L β U +
      wilsonActionOSNegativeTemporal N T L β U := by
  unfold wilsonActionOSNegative wilsonActionOSNegativeSpatial wilsonActionOSNegativeTemporal
  have h_split (n : PeriodicSite T L) (μ ν : Fin 4) :
      (if signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
            signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
            signedTime T (addVectorPeriodic T L n ν).time < 0 then
        plaquetteContribution N β U n μ ν else 0) =
      (if signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
            signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
            signedTime T (addVectorPeriodic T L n ν).time < 0 ∧
            μ ≠ 0 ∧ ν ≠ 0 then
        plaquetteContribution N β U n μ ν else 0) +
      (if signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
            signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
            signedTime T (addVectorPeriodic T L n ν).time < 0 ∧
            (μ = 0 ∨ ν = 0) then
        plaquetteContribution N β U n μ ν else 0) := by
    by_cases hP : signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
                  signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
                  signedTime T (addVectorPeriodic T L n ν).time < 0
    · rcases hP with ⟨h1, h2, h3, h4⟩
      by_cases hμ0 : μ = 0
      · rw [if_pos ⟨h1, h2, h3, h4⟩,
            if_neg (fun h => by rcases h with ⟨_, _, _, _, ⟨hμ_ne, _⟩⟩; exact hμ_ne hμ0),
            if_pos ⟨h1, h2, h3, h4, Or.inl hμ0⟩]; ring
      · by_cases hν0 : ν = 0
        · rw [if_pos ⟨h1, h2, h3, h4⟩,
              if_neg (fun h => by rcases h with ⟨_, _, _, _, ⟨_, hν_ne⟩⟩; exact hν_ne hν0),
              if_pos ⟨h1, h2, h3, h4, Or.inr hν0⟩]; ring
        · rw [if_pos ⟨h1, h2, h3, h4⟩,
              if_pos ⟨h1, h2, h3, h4, ⟨hμ0, hν0⟩⟩,
              if_neg (fun h => by rcases h with ⟨_, _, _, _, h | h⟩ <;> first
                | exact hμ0 h | exact hν0 h)]; ring
    · rw [if_neg hP,
          if_neg (fun h => by rcases h with ⟨h1, h2, h3, h4, _⟩; exact hP ⟨h1, h2, h3, h4⟩),
          if_neg (fun h => by rcases h with ⟨h1, h2, h3, h4, _⟩; exact hP ⟨h1, h2, h3, h4⟩)];
        ring
  have h_sum : ∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4,
      (if signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
            signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
            signedTime T (addVectorPeriodic T L n ν).time < 0 then
        plaquetteContribution N β U n μ ν else 0) =
    ∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4,
      ((if signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
            signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
            signedTime T (addVectorPeriodic T L n ν).time < 0 ∧
            μ ≠ 0 ∧ ν ≠ 0 then
        plaquetteContribution N β U n μ ν else 0) +
       (if signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
            signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
            signedTime T (addVectorPeriodic T L n ν).time < 0 ∧
            (μ = 0 ∨ ν = 0) then
        plaquetteContribution N β U n μ ν else 0)) := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    refine Finset.sum_congr rfl (fun ν _ => ?_)
    exact h_split n μ ν
  rw [h_sum]
  simp [Finset.sum_add_distrib]

#print axioms wilsonActionOSNegative_eq_spatial_plus_temporal

/-- **S_int = S_spatial_int + S_temporal_int.** The OS-interface action decomposes
into spatial and temporal parts. -/
lemma wilsonActionOSInterface_eq_spatial_plus_temporal (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) :
    wilsonActionOSInterface N T L β U =
      wilsonActionOSInterfaceSpatial N T L β U +
      wilsonActionOSInterfaceTemporal N T L β U := by
  unfold wilsonActionOSInterface wilsonActionOSInterfaceSpatial wilsonActionOSInterfaceTemporal
  have h_split (n : PeriodicSite T L) (μ ν : Fin 4) :
      (if ¬ (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
            signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
            signedTime T (addVectorPeriodic T L n ν).time > 0) ∧
        ¬ (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
            signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
            signedTime T (addVectorPeriodic T L n ν).time < 0) then
        plaquetteContribution N β U n μ ν else 0) =
      (if ¬ (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
            signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
            signedTime T (addVectorPeriodic T L n ν).time > 0) ∧
        ¬ (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
            signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
            signedTime T (addVectorPeriodic T L n ν).time < 0) ∧
        μ ≠ 0 ∧ ν ≠ 0 then
        plaquetteContribution N β U n μ ν else 0) +
      (if ¬ (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
            signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
            signedTime T (addVectorPeriodic T L n ν).time > 0) ∧
        ¬ (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
            signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
            signedTime T (addVectorPeriodic T L n ν).time < 0) ∧
        (μ = 0 ∨ ν = 0) then
        plaquetteContribution N β U n μ ν else 0) := by
    by_cases hP : ¬ (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
                  signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
                  signedTime T (addVectorPeriodic T L n ν).time > 0) ∧
                ¬ (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
                  signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
                  signedTime T (addVectorPeriodic T L n ν).time < 0)
    · rcases hP with ⟨hnpos, hnneg⟩
      by_cases hμ0 : μ = 0
      · rw [if_pos ⟨hnpos, hnneg⟩,
            if_neg (fun h => by rcases h with ⟨_, _, ⟨hμ_ne, _⟩⟩; exact hμ_ne hμ0),
            if_pos ⟨hnpos, hnneg, Or.inl hμ0⟩]; ring
      · by_cases hν0 : ν = 0
        · rw [if_pos ⟨hnpos, hnneg⟩,
              if_neg (fun h => by rcases h with ⟨_, _, ⟨_, hν_ne⟩⟩; exact hν_ne hν0),
              if_pos ⟨hnpos, hnneg, Or.inr hν0⟩]; ring
        · rw [if_pos ⟨hnpos, hnneg⟩,
              if_pos ⟨hnpos, hnneg, ⟨hμ0, hν0⟩⟩,
              if_neg (fun h => by rcases h with ⟨_, _, h | h⟩ <;> first
                | exact hμ0 h | exact hν0 h)]; ring
    · rw [if_neg hP,
          if_neg (fun h => by rcases h with ⟨hnpos, hnneg, _⟩; exact hP ⟨hnpos, hnneg⟩),
          if_neg (fun h => by rcases h with ⟨hnpos, hnneg, _⟩; exact hP ⟨hnpos, hnneg⟩)];
        ring
  have h_sum : ∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4,
      (if ¬ (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
            signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
            signedTime T (addVectorPeriodic T L n ν).time > 0) ∧
        ¬ (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
            signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
            signedTime T (addVectorPeriodic T L n ν).time < 0) then
        plaquetteContribution N β U n μ ν else 0) =
    ∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4,
      ((if ¬ (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
            signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
            signedTime T (addVectorPeriodic T L n ν).time > 0) ∧
        ¬ (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
            signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
            signedTime T (addVectorPeriodic T L n ν).time < 0) ∧
        μ ≠ 0 ∧ ν ≠ 0 then
        plaquetteContribution N β U n μ ν else 0) +
       (if ¬ (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
            signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
            signedTime T (addVectorPeriodic T L n ν).time > 0) ∧
        ¬ (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
            signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
            signedTime T (addVectorPeriodic T L n ν).time < 0) ∧
        (μ = 0 ∨ ν = 0) then
        plaquetteContribution N β U n μ ν else 0)) := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    refine Finset.sum_congr rfl (fun ν _ => ?_)
    exact h_split n μ ν
  rw [h_sum]
  simp [Finset.sum_add_distrib]

#print axioms wilsonActionOSInterface_eq_spatial_plus_temporal

/-! ### PosInterface split: spatial/temporal parts of osPositiveOfPosInterface -/

/-- The spatial part of `osPositiveOfPosInterface`: the OS-positive spatial action
evaluated on the extended link variable from a PosInterfaceConfig. -/
noncomputable def osPositiveSpatialOfPosInterface (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (u : PosInterfaceConfig N T L) : ℝ :=
  wilsonActionOSPositiveSpatial N T L β
    (extendLinkVariable N (PeriodicSite T L) (positiveSites T L ∪ interfaceSites T L) u)

/-- The temporal part of `osPositiveOfPosInterface`: the OS-positive temporal action
evaluated on the extended link variable from a PosInterfaceConfig. -/
noncomputable def osPositiveTemporalOfPosInterface (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (u : PosInterfaceConfig N T L) : ℝ :=
  wilsonActionOSPositiveTemporal N T L β
    (extendLinkVariable N (PeriodicSite T L) (positiveSites T L ∪ interfaceSites T L) u)

/-- **osPositiveOfPosInterface = spatial + temporal.** The OS-positive action
evaluated on a PosInterfaceConfig decomposes into spatial and temporal parts. -/
lemma osPositiveOfPosInterface_eq_spatial_plus_temporal (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (u : PosInterfaceConfig N T L) :
    osPositiveOfPosInterface N T L β u =
      osPositiveSpatialOfPosInterface N T L β u +
      osPositiveTemporalOfPosInterface N T L β u := by
  unfold osPositiveOfPosInterface osPositiveSpatialOfPosInterface osPositiveTemporalOfPosInterface
  exact wilsonActionOSPositive_eq_spatial_plus_temporal N T L β _

#print axioms osPositiveOfPosInterface_eq_spatial_plus_temporal

/-! ### Kernel factorization: exp(spatial + temporal) = exp(spatial) · exp(temporal) -/

/-- **The transfer-matrix kernel exponent splits into spatial + temporal parts.**
The exponent `-β·(S⁺(u)/2 + S⁺(u')/2 + S_int)` decomposes as
`-β·(spatial part) + -β·(temporal part)` using the spatial/temporal splits of
`osPositiveOfPosInterface` and `wilsonActionOSInterface`.  Pure algebra. -/
lemma transferMatrix_kernel_exponent_spatial_temporal_split
    (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (u u' : PosInterfaceConfig N T L)
    (full_config : LinkVariable (SU N) (PeriodicSite T L)) :
    -β * (osPositiveOfPosInterface N T L β u / 2 +
          osPositiveOfPosInterface N T L β u' / 2 +
          wilsonActionOSInterface N T L β full_config) =
    -β * (osPositiveSpatialOfPosInterface N T L β u / 2 +
          osPositiveSpatialOfPosInterface N T L β u' / 2 +
          wilsonActionOSInterfaceSpatial N T L β full_config) +
    -β * (osPositiveTemporalOfPosInterface N T L β u / 2 +
          osPositiveTemporalOfPosInterface N T L β u' / 2 +
          wilsonActionOSInterfaceTemporal N T L β full_config) := by
  rw [osPositiveOfPosInterface_eq_spatial_plus_temporal N T L β u,
      osPositiveOfPosInterface_eq_spatial_plus_temporal N T L β u',
      wilsonActionOSInterface_eq_spatial_plus_temporal N T L β full_config]
  ring

#print axioms transferMatrix_kernel_exponent_spatial_temporal_split

/-- **The transfer-matrix kernel factors as exp(spatial) · exp(temporal).**
Using `Real.exp_add`, the kernel
`exp(-β·(S⁺(u)/2 + S⁺(u')/2 + S_int))` factors as
`exp(-β·(spatial part)) · exp(-β·(temporal part))`.
The spatial factor defines the multiplication operator V (PD by `spatialBoltzmannPD`);
the temporal factor defines the integral operator U (positive by the Lüscher cascade). -/
lemma transferMatrix_kernel_spatial_temporal_factor
    (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (u u' : PosInterfaceConfig N T L)
    (full_config : LinkVariable (SU N) (PeriodicSite T L)) :
    Real.exp (-β * (osPositiveOfPosInterface N T L β u / 2 +
          osPositiveOfPosInterface N T L β u' / 2 +
          wilsonActionOSInterface N T L β full_config)) =
    Real.exp (-β * (osPositiveSpatialOfPosInterface N T L β u / 2 +
          osPositiveSpatialOfPosInterface N T L β u' / 2 +
          wilsonActionOSInterfaceSpatial N T L β full_config)) *
    Real.exp (-β * (osPositiveTemporalOfPosInterface N T L β u / 2 +
          osPositiveTemporalOfPosInterface N T L β u' / 2 +
          wilsonActionOSInterfaceTemporal N T L β full_config)) := by
  rw [transferMatrix_kernel_exponent_spatial_temporal_split, Real.exp_add]

#print axioms transferMatrix_kernel_spatial_temporal_factor

end TransferMatrix
end Lattice
end YangMills
