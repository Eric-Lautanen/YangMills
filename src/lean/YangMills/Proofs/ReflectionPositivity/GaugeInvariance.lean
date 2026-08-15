/-
# Reflection Positivity: Gauge Invariance and Axiom
-/

import YangMills.Proofs.ReflectionPositivity.FullBoltzmannPD

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open scoped BigOperators
open MeasureTheory
open Complex
open scoped ComplexConjugate

namespace YangMills
namespace Lattice
section ConditionEquivalence

open scoped BigOperators

/-- For spatial-spatial plaquettes (μ≠0, ν≠0), the signed times at reflected corners
are the negations of the signed times at the original corners. -/
lemma signedTime_ss_reflect (T L : ℕ) [NeZero T] (hT : Odd T) (n : PeriodicSite T L) (μ ν : Fin 4) (hμ0 : μ ≠ 0) (hν0 : ν ≠ 0) :
    signedTime T (ReflectSite.reflectSite n).time = -signedTime T n.time ∧
    signedTime T (addVectorPeriodic T L (ReflectSite.reflectSite n) μ).time = -signedTime T (addVectorPeriodic T L n μ).time ∧
    signedTime T (addVectorPeriodic T L (addVectorPeriodic T L (ReflectSite.reflectSite n) μ) ν).time = -signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time ∧
    signedTime T (addVectorPeriodic T L (ReflectSite.reflectSite n) ν).time = -signedTime T (addVectorPeriodic T L n ν).time := by
  have h1 : signedTime T (ReflectSite.reflectSite n).time = -signedTime T n.time := by
    simp [ReflectSite.reflectSite, reflectSitePeriodic, signedTime_neg T n.time hT]
  have h2 : signedTime T (addVectorPeriodic T L (ReflectSite.reflectSite n) μ).time = -signedTime T (addVectorPeriodic T L n μ).time := by
    calc
      signedTime T (addVectorPeriodic T L (ReflectSite.reflectSite n) μ).time
          = signedTime T (ReflectSite.reflectSite (addVectorPeriodic T L n μ)).time := by
        show signedTime T (AddVector.addVector (ReflectSite.reflectSite n) μ).time =
             signedTime T (ReflectSite.reflectSite (AddVector.addVector n μ)).time
        rw [reflectSite_addVector_comm T L n μ hμ0]
      _ = -signedTime T (addVectorPeriodic T L n μ).time := by
        simp [ReflectSite.reflectSite, reflectSitePeriodic, signedTime_neg T (addVectorPeriodic T L n μ).time hT]
  have h3 : signedTime T (addVectorPeriodic T L (addVectorPeriodic T L (ReflectSite.reflectSite n) μ) ν).time =
      -signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time := by
    calc
      signedTime T (addVectorPeriodic T L (addVectorPeriodic T L (ReflectSite.reflectSite n) μ) ν).time
          = signedTime T (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n μ)) ν).time := by
        show signedTime T (AddVector.addVector (AddVector.addVector (ReflectSite.reflectSite n) μ) ν).time =
             signedTime T (AddVector.addVector (ReflectSite.reflectSite (AddVector.addVector n μ)) ν).time
        rw [reflectSite_addVector_comm T L n μ hμ0]
      _ = signedTime T (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν)).time := by
        show signedTime T (AddVector.addVector (ReflectSite.reflectSite (AddVector.addVector n μ)) ν).time =
             signedTime T (ReflectSite.reflectSite (AddVector.addVector (AddVector.addVector n μ) ν)).time
        rw [reflectSite_addVector_comm T L (AddVector.addVector n μ) ν hν0]
      _ = -signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time := by
        simp [ReflectSite.reflectSite, reflectSitePeriodic, signedTime_neg T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time hT]
  have h4 : signedTime T (addVectorPeriodic T L (ReflectSite.reflectSite n) ν).time = -signedTime T (addVectorPeriodic T L n ν).time := by
    calc
      signedTime T (addVectorPeriodic T L (ReflectSite.reflectSite n) ν).time
          = signedTime T (ReflectSite.reflectSite (addVectorPeriodic T L n ν)).time := by
        show signedTime T (AddVector.addVector (ReflectSite.reflectSite n) ν).time =
             signedTime T (ReflectSite.reflectSite (AddVector.addVector n ν)).time
        rw [reflectSite_addVector_comm T L n ν hν0]
      _ = -signedTime T (addVectorPeriodic T L n ν).time := by
        simp [ReflectSite.reflectSite, reflectSitePeriodic, signedTime_neg T (addVectorPeriodic T L n ν).time hT]
  exact ⟨h1, h2, h3, h4⟩

/-- Adding a spatial direction (μ ≠ 0) does not change the time coordinate of a
`PeriodicSite`; only the time direction `μ = 0` increments `time`. -/
lemma addVectorPeriodic_time_of_ne_zero (T L : ℕ) (n : PeriodicSite T L) (μ : Fin 4)
    (hμ0 : μ ≠ 0) : (addVectorPeriodic T L n μ).time = n.time := by
  fin_cases μ
  · exfalso; exact hμ0 rfl
  · simp [addVectorPeriodic]
  · simp [addVectorPeriodic]
  · simp [addVectorPeriodic]

/-- For time-spatial plaquettes (μ=0, ν≠0), the signed times at reflected corners
are the negations of the signed times at the original corners (with time shifts). -/
lemma signedTime_ts_reflect (T L : ℕ) [NeZero T] (hT : Odd T) (n : PeriodicSite T L) (ν : Fin 4) (hν0 : ν ≠ 0) :
    signedTime T (ReflectSite.reflectSite (addVectorPeriodic T L n 0)).time = -signedTime T (addVectorPeriodic T L n 0).time ∧
    signedTime T (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) ν).time = -signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n 0) ν).time ∧
    signedTime T (addVectorPeriodic T L (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) ν) 0).time = -signedTime T (addVectorPeriodic T L n ν).time ∧
    signedTime T (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) 0).time = -signedTime T n.time := by
  -- Time of n + e_0
  have h_n0_time : (addVectorPeriodic T L n 0).time = n.time + 1 := by simp [addVectorPeriodic]
  -- Time of θ(n + e_0) = -(n.time + 1)
  have h_refl_time : (ReflectSite.reflectSite (addVectorPeriodic T L n 0)).time = -(n.time + 1 : ZMod T) := by
    simp [ReflectSite.reflectSite, reflectSitePeriodic, h_n0_time]
  -- Time of θ(n + e_0) + e_ν = -(n.time + 1) (spatial doesn't change time)
  have h_refl_ν_time : (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) ν).time = -(n.time + 1 : ZMod T) := by
    have h_spatial : (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) ν).time =
        (ReflectSite.reflectSite (addVectorPeriodic T L n 0)).time :=
      addVectorPeriodic_time_of_ne_zero T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) ν hν0
    rw [h_spatial, h_refl_time]
  -- Time of θ(n + e_0) + e_ν + e_0 = -(n.time + 1) + 1 = -n.time
  have h_refl_ν_0_time : (addVectorPeriodic T L (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) ν) 0).time = -n.time := by
    have h_add0 : (addVectorPeriodic T L (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) ν) 0).time = (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) ν).time + 1 := by
      simp [addVectorPeriodic]
    rw [h_add0, h_refl_ν_time]
    ring
  -- Time of θ(n + e_0) + e_0 = -(n.time + 1) + 1 = -n.time
  have h_refl_0_time : (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) 0).time = -n.time := by
    have h_add0 : (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) 0).time = (ReflectSite.reflectSite (addVectorPeriodic T L n 0)).time + 1 := by
      simp [addVectorPeriodic]
    rw [h_add0, h_refl_time]
    ring
  -- Time of n + e_ν = n.time (spatial)
  have h_nν_time : (addVectorPeriodic T L n ν).time = n.time :=
    addVectorPeriodic_time_of_ne_zero T L n ν hν0
  -- Time of n + e_0 + e_ν = n.time + 1 (spatial doesn't change time)
  have h_n0ν_time : (addVectorPeriodic T L (addVectorPeriodic T L n 0) ν).time = n.time + 1 := by
    have h_spatial : (addVectorPeriodic T L (addVectorPeriodic T L n 0) ν).time =
        (addVectorPeriodic T L n 0).time :=
      addVectorPeriodic_time_of_ne_zero T L (addVectorPeriodic T L n 0) ν hν0
    rw [h_spatial, h_n0_time]
  -- Assemble the four conjuncts using signedTime_neg
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h_refl_time, h_n0_time]; exact signedTime_neg T (n.time + 1) hT
  · rw [h_refl_ν_time, h_n0ν_time]; exact signedTime_neg T (n.time + 1) hT
  · rw [h_refl_ν_0_time, h_nν_time]; exact signedTime_neg T n.time hT
  · rw [h_refl_0_time]; exact signedTime_neg T n.time hT

-- Additional signed-time reflection lemmas for (μ≠0, ν=0) and (μ=0, ν=0) cases.

/-- For spatial-time plaquettes (μ≠0, ν=0), the signed times at reflected corners
are the negations of the signed times at the original corners. -/
lemma signedTime_st_reflect (T L : ℕ) [NeZero T] (hT : Odd T) (n : PeriodicSite T L) (μ : Fin 4) (hμ0 : μ ≠ 0) :
    signedTime T (ReflectSite.reflectSite (addVectorPeriodic T L n 0)).time = -signedTime T (addVectorPeriodic T L n 0).time ∧
    signedTime T (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) 0).time = -signedTime T n.time ∧
    signedTime T (addVectorPeriodic T L (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) 0) μ).time = -signedTime T (addVectorPeriodic T L n μ).time ∧
    signedTime T (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) μ).time = -signedTime T (addVectorPeriodic T L n 0).time := by
  -- Time of n + e_0
  have h_n0_time : (addVectorPeriodic T L n 0).time = n.time + 1 := by simp [addVectorPeriodic]
  -- Time of θ(n + e_0) = -(n.time + 1)
  have h_refl_time : (ReflectSite.reflectSite (addVectorPeriodic T L n 0)).time = -(n.time + 1 : ZMod T) := by
    simp [ReflectSite.reflectSite, reflectSitePeriodic, h_n0_time]
  -- Time of θ(n + e_0) + e_0 = -n.time
  have h_refl_0_time : (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) 0).time = -n.time := by
    have h_add0 : (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) 0).time = (ReflectSite.reflectSite (addVectorPeriodic T L n 0)).time + 1 := by
      simp [addVectorPeriodic]
    rw [h_add0, h_refl_time]
    ring
  -- Time of θ(n + e_0) + e_0 + e_μ = -n.time (spatial doesn't change time)
  have h_refl_0_μ_time : (addVectorPeriodic T L (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) 0) μ).time = -n.time := by
    have h_spatial : (addVectorPeriodic T L (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) 0) μ).time =
        (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) 0).time :=
      addVectorPeriodic_time_of_ne_zero T L (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) 0) μ hμ0
    rw [h_spatial, h_refl_0_time]
  -- Time of θ(n + e_0) + e_μ = -(n.time + 1) (spatial doesn't change time)
  have h_refl_μ_time : (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) μ).time = -(n.time + 1 : ZMod T) := by
    have h_spatial : (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) μ).time =
        (ReflectSite.reflectSite (addVectorPeriodic T L n 0)).time :=
      addVectorPeriodic_time_of_ne_zero T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) μ hμ0
    rw [h_spatial, h_refl_time]
  -- Time of n + e_μ = n.time (spatial)
  have h_nμ_time : (addVectorPeriodic T L n μ).time = n.time :=
    addVectorPeriodic_time_of_ne_zero T L n μ hμ0
  -- Assemble
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h_refl_time, h_n0_time]; exact signedTime_neg T (n.time + 1) hT
  · rw [h_refl_0_time]; exact signedTime_neg T n.time hT
  · rw [h_refl_0_μ_time, h_nμ_time]; exact signedTime_neg T n.time hT
  · rw [h_refl_μ_time, h_n0_time]; exact signedTime_neg T (n.time + 1) hT

/-- For time-time plaquettes (μ=0, ν=0), the signed times at reflected corners
are the negations of the signed times at the original corners. -/
lemma signedTime_tt_reflect (T L : ℕ) [NeZero T] (hT : Odd T) (n : PeriodicSite T L) :
    signedTime T (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0)).time = -signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0).time ∧
    signedTime T (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0)) 0).time = -signedTime T (addVectorPeriodic T L n 0).time ∧
    signedTime T (addVectorPeriodic T L (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0)) 0) 0).time = -signedTime T n.time ∧
    signedTime T (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0)) 0).time = -signedTime T (addVectorPeriodic T L n 0).time := by
  -- Time of n + e_0
  have h_n0_time : (addVectorPeriodic T L n 0).time = n.time + 1 := by simp [addVectorPeriodic]
  -- Time of n + 2e_0
  have h_n00_time : (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0).time = n.time + 2 := by
    have h_add0 : (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0).time = (addVectorPeriodic T L n 0).time + 1 := by simp [addVectorPeriodic]
    rw [h_add0, h_n0_time]
    ring
  -- Time of θ(n + 2e_0) = -(n.time + 2)
  have h_refl_time : (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0)).time = -(n.time + 2 : ZMod T) := by
    simp [ReflectSite.reflectSite, reflectSitePeriodic, h_n00_time]
  -- Time of θ(n + 2e_0) + e_0 = -(n.time + 2) + 1 = -(n.time + 1)
  have h_refl_0_time : (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0)) 0).time = -(n.time + 1 : ZMod T) := by
    have h_add0 : (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0)) 0).time = (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0)).time + 1 := by
      simp [addVectorPeriodic]
    rw [h_add0, h_refl_time]
    ring
  -- Time of θ(n + 2e_0) + 2e_0 = -(n.time + 2) + 2 = -n.time
  have h_refl_00_time : (addVectorPeriodic T L (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0)) 0) 0).time = -n.time := by
    have h_add0 : (addVectorPeriodic T L (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0)) 0) 0).time = (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0)) 0).time + 1 := by
      simp [addVectorPeriodic]
    rw [h_add0, h_refl_0_time]
    ring
  -- Assemble
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h_refl_time, h_n00_time]; exact signedTime_neg T (n.time + 2) hT
  · rw [h_refl_0_time, h_n0_time]; exact signedTime_neg T (n.time + 1) hT
  · rw [h_refl_00_time]; exact signedTime_neg T n.time hT
  · rw [h_refl_0_time, h_n0_time]; exact signedTime_neg T (n.time + 1) hT

end ConditionEquivalence

/-- Symmetric form of `trace_plaquetteProduct_reflect_ss`: the trace of the original
spatial plaquette equals the trace of the reflected plaquette (μ ≠ 0, ν ≠ 0). -/
lemma trace_plaquetteProduct_reflect_ss' (N T L : ℕ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) (n : PeriodicSite T L) (μ ν : Fin 4)
    (hμ0 : μ ≠ 0) (hν0 : ν ≠ 0) :
    ((Matrix.trace ((plaquetteProduct N U n μ ν : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) =
    ((Matrix.trace ((plaquetteProduct N (reflectLinkVariable N U)
      (ReflectSite.reflectSite n) μ ν : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) :=
  (trace_plaquetteProduct_reflect_ss N T L U n μ ν hμ0 hν0).symm

set_option maxHeartbeats 1000000 in
/--
When all four corners of a plaquette have negative signed time, the trace of the
reflected plaquette (under the Osterwalder-Seiler bijection) equals the trace of
the original plaquette. This dispatches to the appropriate
`trace_plaquetteProduct_reflect_*` lemma based on the directions μ, ν.
-/
lemma trace_plaquetteProduct_neg_to_pos (N T L : ℕ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) (n : PeriodicSite T L) (μ ν : Fin 4)
    (h_neg : signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
             signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
             signedTime T (addVectorPeriodic T L n ν).time < 0) :
    ((Matrix.trace ((plaquetteProduct N U n μ ν : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) =
    ((Matrix.trace ((plaquetteProduct N (reflectLinkVariable N U)
      (match μ, ν with
      | 0, 0 => ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0)
      | 0, _ => ReflectSite.reflectSite (addVectorPeriodic T L n 0)
      | _, 0 => ReflectSite.reflectSite (addVectorPeriodic T L n 0)
      | _, _ => ReflectSite.reflectSite n)
      (match μ, ν with
      | 0, 0 => 0
      | 0, ν => ν
      | μ, 0 => 0
      | μ, ν => μ)
      (match μ, ν with
      | 0, 0 => 0
      | 0, ν => 0
      | μ, 0 => μ
      | μ, ν => ν)
    : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) := by
  -- The trace identity holds for every direction pair (μ, ν); the sign hypothesis
  -- `h_neg` only selects which plaquettes land in the negative-time sum, so it is
  -- irrelevant to the pointwise trace equality. We dispatch to the four already-proven
  -- `trace_plaquetteProduct_reflect_*` lemmas by case analysis on (μ, ν).  Explicit
  -- bullets (rather than `first`) keep each case to a single `defEq` check.
  obtain ⟨h1, h2, h3, h4⟩ := h_neg
  fin_cases μ <;> fin_cases ν
  · exact trace_plaquetteProduct_reflect_tt N T L U n
  · apply trace_plaquetteProduct_reflect_ts N T L U n _; decide
  · apply trace_plaquetteProduct_reflect_ts N T L U n _; decide
  · apply trace_plaquetteProduct_reflect_ts N T L U n _; decide
  · apply trace_plaquetteProduct_reflect_st N T L U n _; decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide
  · apply trace_plaquetteProduct_reflect_st N T L U n _; decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide
  · apply trace_plaquetteProduct_reflect_st N T L U n _; decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide

set_option maxHeartbeats 1000000 in
/-- Reflection cancels a single forward time step: θ(θ(n+e₀)+e₀) = n. -/
lemma reflectSite_addVector0_inv (T L : ℕ) [NeZero T] (n : PeriodicSite T L) :
    ReflectSite.reflectSite (addVectorPeriodic T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0)) 0) = n := by
  ext <;> simp [ReflectSite.reflectSite, reflectSitePeriodic, addVectorPeriodic]

set_option maxHeartbeats 1000000 in
/-- Reflection cancels two forward time steps: θ(θ(n+2e₀)+2e₀) = n. -/
lemma reflectSite_addVector00_inv (T L : ℕ) [NeZero T] (n : PeriodicSite T L) :
    ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L
      (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0)) 0) 0) = n := by
  ext <;> simp [ReflectSite.reflectSite, reflectSitePeriodic, addVectorPeriodic]

/-- The Osterwalder-Seiler reflection of a plaquette index (n, μ, ν) maps it to the
reflected plaquette (n', μ', ν') whose trace equals the original (by
`trace_plaquetteProduct_neg_to_pos`). -/
def reflectPlaquetteIndex (T L : ℕ) [NeZero T] : PlaquetteIndex T L → PlaquetteIndex T L
  | (n, 0, 0) => (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0), 0, 0)
  | (n, 0, ν) => (ReflectSite.reflectSite (addVectorPeriodic T L n 0), ν, 0)
  | (n, μ, 0) => (ReflectSite.reflectSite (addVectorPeriodic T L n 0), 0, μ)
  | (n, μ, ν) => (ReflectSite.reflectSite n, μ, ν)

/-- `reflectPlaquetteIndex` is involutive, hence a bijection on plaquette indices. -/
lemma reflectPlaquetteIndex_involution (T L : ℕ) [NeZero T] (p : PlaquetteIndex T L) :
    reflectPlaquetteIndex T L (reflectPlaquetteIndex T L p) = p := by
  rcases p with ⟨n, μ, ν⟩
  fin_cases μ <;> fin_cases ν <;>
    simp [reflectPlaquetteIndex, reflectSite_addVector0_inv, reflectSite_addVector00_inv,
      ReflectSite.involution]

/-- The Osterwalder-Seiler plaquette reflection as an equivalence (involution → bijection). -/
def reflectPlaquetteIndexEquiv (T L : ℕ) [NeZero T] : PlaquetteIndex T L ≃ PlaquetteIndex T L where
  toFun := reflectPlaquetteIndex T L
  invFun := reflectPlaquetteIndex T L
  left_inv := reflectPlaquetteIndex_involution T L
  right_inv := reflectPlaquetteIndex_involution T L

/-- A plaquette index is "negative" if all four corners have strictly negative signed time. -/
abbrev plaquetteNegative (T L : ℕ) (p : PlaquetteIndex T L) : Prop :=
  signedTime T p.1.time < 0 ∧ signedTime T (addVectorPeriodic T L p.1 p.2.1).time < 0 ∧
  signedTime T (addVectorPeriodic T L (addVectorPeriodic T L p.1 p.2.1) p.2.2).time < 0 ∧
  signedTime T (addVectorPeriodic T L p.1 p.2.2).time < 0

/-- A plaquette index is "positive" if all four corners have strictly positive signed time. -/
abbrev plaquettePositive (T L : ℕ) (p : PlaquetteIndex T L) : Prop :=
  signedTime T p.1.time > 0 ∧ signedTime T (addVectorPeriodic T L p.1 p.2.1).time > 0 ∧
  signedTime T (addVectorPeriodic T L (addVectorPeriodic T L p.1 p.2.1) p.2.2).time > 0 ∧
  signedTime T (addVectorPeriodic T L p.1 p.2.2).time > 0

set_option maxHeartbeats 1000000 in
/-- Reflection maps negative plaquettes to positive ones and vice versa: (0,0) case. -/
lemma signedTime_tt_sign_iff (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T) (n : PeriodicSite T L) :
    plaquettePositive T L (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0), 0, 0) ↔
    plaquetteNegative T L (n, 0, 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := signedTime_tt_reflect T L hT n
  simp only [plaquettePositive, plaquetteNegative]
  omega

set_option maxHeartbeats 1000000 in
/-- Reflection maps negative plaquettes to positive ones and vice versa: (0,ν) case. -/
lemma signedTime_ts_sign_iff (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T) (n : PeriodicSite T L)
    (ν : Fin 4) (hν0 : ν ≠ 0) :
    plaquettePositive T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0), ν, 0) ↔
    plaquetteNegative T L (n, 0, ν) := by
  obtain ⟨h1, h2, h3, h4⟩ := signedTime_ts_reflect T L hT n ν hν0
  simp only [plaquettePositive, plaquetteNegative]
  omega

set_option maxHeartbeats 1000000 in
/-- Reflection maps negative plaquettes to positive ones and vice versa: (μ,0) case. -/
lemma signedTime_st_sign_iff (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T) (n : PeriodicSite T L)
    (μ : Fin 4) (hμ0 : μ ≠ 0) :
    plaquettePositive T L (ReflectSite.reflectSite (addVectorPeriodic T L n 0), 0, μ) ↔
    plaquetteNegative T L (n, μ, 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := signedTime_st_reflect T L hT n μ hμ0
  -- n+e_μ+e₀ and n+e₀ have the same time coordinate (e_μ is spatial), so their
  -- signed times are equal.  Omega needs this to close the iff.
  have h_same : signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) 0).time =
      signedTime T (addVectorPeriodic T L n 0).time := by
    have h1 : (addVectorPeriodic T L (addVectorPeriodic T L n μ) 0).time =
        (addVectorPeriodic T L n μ).time + 1 := rfl
    have h2 : (addVectorPeriodic T L n 0).time = n.time + 1 := rfl
    rw [h1, addVectorPeriodic_time_of_ne_zero T L n μ hμ0, h2]
  simp only [plaquettePositive, plaquetteNegative]
  omega

set_option maxHeartbeats 1000000 in
/-- Reflection maps negative plaquettes to positive ones and vice versa: (μ,ν) case. -/
lemma signedTime_ss_sign_iff (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T) (n : PeriodicSite T L)
    (μ ν : Fin 4) (hμ0 : μ ≠ 0) (hν0 : ν ≠ 0) :
    plaquettePositive T L (ReflectSite.reflectSite n, μ, ν) ↔
    plaquetteNegative T L (n, μ, ν) := by
  obtain ⟨h1, h2, h3, h4⟩ := signedTime_ss_reflect T L hT n μ ν hμ0 hν0
  simp only [plaquettePositive, plaquetteNegative]
  omega

set_option maxHeartbeats 1000000 in
/-- Reflection maps negative plaquettes to positive ones and vice versa. -/
lemma reflectPlaquetteIndex_sign (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (p : PlaquetteIndex T L) :
    plaquettePositive T L (reflectPlaquetteIndex T L p) ↔ plaquetteNegative T L p := by
  rcases p with ⟨n, μ, ν⟩
  fin_cases μ <;> fin_cases ν <;> simp only [reflectPlaquetteIndex] <;> first
    | exact signedTime_tt_sign_iff T L hT n
    | (apply signedTime_ts_sign_iff T L hT n _; decide)
    | (apply signedTime_st_sign_iff T L hT n _; decide)
    | (apply signedTime_ss_sign_iff T L hT n _ _; all_goals decide)

/-- `reflectPlaquetteIndex` first component expanded as a match expression. -/
lemma reflectPlaquetteIndex_fst (T L : ℕ) [NeZero T] (n : PeriodicSite T L) (μ ν : Fin 4) :
    (reflectPlaquetteIndex T L (n, μ, ν)).1 =
    (match μ, ν with
    | 0, 0 => ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0)
    | 0, _ => ReflectSite.reflectSite (addVectorPeriodic T L n 0)
    | _, 0 => ReflectSite.reflectSite (addVectorPeriodic T L n 0)
    | _, _ => ReflectSite.reflectSite n) := by
  fin_cases μ <;> fin_cases ν <;> rfl

/-- `reflectPlaquetteIndex` second component (μ') expanded as a match expression. -/
lemma reflectPlaquetteIndex_snd_fst (T L : ℕ) [NeZero T] (n : PeriodicSite T L) (μ ν : Fin 4) :
    (reflectPlaquetteIndex T L (n, μ, ν)).2.1 =
    (match μ, ν with
    | 0, 0 => 0
    | 0, ν => ν
    | μ, 0 => 0
    | μ, ν => μ) := by
  fin_cases μ <;> fin_cases ν <;> rfl

/-- `reflectPlaquetteIndex` third component (ν') expanded as a match expression. -/
lemma reflectPlaquetteIndex_snd_snd (T L : ℕ) [NeZero T] (n : PeriodicSite T L) (μ ν : Fin 4) :
    (reflectPlaquetteIndex T L (n, μ, ν)).2.2 =
    (match μ, ν with
    | 0, 0 => 0
    | 0, ν => 0
    | μ, 0 => μ
    | μ, ν => ν) := by
  fin_cases μ <;> fin_cases ν <;> rfl

/-- `reflectPlaquetteIndex` expanded as a match expression (for rewriting). -/
lemma reflectPlaquetteIndex_eq (T L : ℕ) [NeZero T] (n : PeriodicSite T L) (μ ν : Fin 4) :
    reflectPlaquetteIndex T L (n, μ, ν) =
    (match μ, ν with
    | 0, 0 => (ReflectSite.reflectSite (addVectorPeriodic T L (addVectorPeriodic T L n 0) 0), 0, 0)
    | 0, ν => (ReflectSite.reflectSite (addVectorPeriodic T L n 0), ν, 0)
    | μ, 0 => (ReflectSite.reflectSite (addVectorPeriodic T L n 0), 0, μ)
    | μ, ν => (ReflectSite.reflectSite n, μ, ν)) := by
  fin_cases μ <;> fin_cases ν <;> rfl

/-- Congruence: equal traces give equal plaquette contributions. -/
lemma plaquetteContribution_congr (N : ℕ) (β : ℝ) (A B : ℝ) (h : A = B) :
    β * ((1 : ℝ) - (1 / (N : ℝ)) * A) = β * ((1 : ℝ) - (1 / (N : ℝ)) * B) := by rw [h]

set_option maxHeartbeats 1000000 in
/-- Variant of `trace_plaquetteProduct_neg_to_pos` whose RHS is expressed via
`reflectPlaquetteIndex` (rather than an explicit `match`), so it composes cleanly with
`plaquetteContribution`. -/
lemma trace_plaquetteProduct_neg_to_pos' (N T L : ℕ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) (n : PeriodicSite T L) (μ ν : Fin 4)
    (h_neg : plaquetteNegative T L (n, μ, ν)) :
    ((Matrix.trace ((plaquetteProduct N U n μ ν : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) =
    ((Matrix.trace ((plaquetteProduct N (reflectLinkVariable N U)
      (reflectPlaquetteIndex T L (n, μ, ν)).1
      (reflectPlaquetteIndex T L (n, μ, ν)).2.1
      (reflectPlaquetteIndex T L (n, μ, ν)).2.2
    : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) := by
  obtain ⟨h1, h2, h3, h4⟩ := h_neg
  fin_cases μ <;> fin_cases ν
  · exact trace_plaquetteProduct_reflect_tt N T L U n
  · apply trace_plaquetteProduct_reflect_ts N T L U n _; decide
  · apply trace_plaquetteProduct_reflect_ts N T L U n _; decide
  · apply trace_plaquetteProduct_reflect_ts N T L U n _; decide
  · apply trace_plaquetteProduct_reflect_st N T L U n _; decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide
  · apply trace_plaquetteProduct_reflect_st N T L U n _; decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide
  · apply trace_plaquetteProduct_reflect_st N T L U n _; decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide
  · apply trace_plaquetteProduct_reflect_ss' N T L U n _ _; all_goals decide

set_option maxHeartbeats 4000000 in
/-- Under the negative-time hypothesis, the plaquette contribution is preserved by the
Osterwalder-Seiler reflection (the reflected trace equals the original trace). -/
lemma plaquetteContribution_reflect_eq (N T L : ℕ) [NeZero T] [NeZero L] (β : ℝ)
    (U : LinkVariable (SU N) (PeriodicSite T L)) (p : PlaquetteIndex T L)
    (h : plaquetteNegative T L p) :
    plaquetteContribution N β U p.1 p.2.1 p.2.2 =
    plaquetteContribution N β (reflectLinkVariable N U)
      (reflectPlaquetteIndex T L p).1 (reflectPlaquetteIndex T L p).2.1
      (reflectPlaquetteIndex T L p).2.2 := by
  rcases p with ⟨n, μ, ν⟩
  obtain ⟨h1, h2, h3, h4⟩ := h
  -- Reduce the tuple projections on the LHS to `n μ ν` (definitional).
  show plaquetteContribution N β U n μ ν =
    plaquetteContribution N β (reflectLinkVariable N U)
      (reflectPlaquetteIndex T L (n, μ, ν)).1
      (reflectPlaquetteIndex T L (n, μ, ν)).2.1
      (reflectPlaquetteIndex T L (n, μ, ν)).2.2
  unfold plaquetteContribution
  rw [trace_plaquetteProduct_neg_to_pos' N T L U n μ ν ⟨h1, h2, h3, h4⟩]

set_option maxHeartbeats 8000000 in
lemma trace_plaquetteProduct_reflect_all (N T L : ℕ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) (n : PeriodicSite T L) (μ ν : Fin 4) :
    ((Matrix.trace ((plaquetteProduct N U n μ ν : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) =
    ((Matrix.trace ((plaquetteProduct N (reflectLinkVariable N U)
      (reflectPlaquetteIndex T L (n, μ, ν)).1
      (reflectPlaquetteIndex T L (n, μ, ν)).2.1
      (reflectPlaquetteIndex T L (n, μ, ν)).2.2 : Matrix (Fin N) (Fin N) ℂ))).re : ℝ) := by
  -- The equality holds for every direction pair (μ, ν) by the specific trace lemmas.
  -- We dispatch by cases on μ and ν.
  fin_cases μ <;> fin_cases ν
  · simpa [reflectPlaquetteIndex] using trace_plaquetteProduct_reflect_tt N T L U n
  · simpa [reflectPlaquetteIndex] using trace_plaquetteProduct_reflect_ts N T L U n 1 (by decide)
  · simpa [reflectPlaquetteIndex] using trace_plaquetteProduct_reflect_ts N T L U n 2 (by decide)
  · simpa [reflectPlaquetteIndex] using trace_plaquetteProduct_reflect_ts N T L U n 3 (by decide)
  · simpa [reflectPlaquetteIndex] using trace_plaquetteProduct_reflect_st N T L U n 1 (by decide)
  · simpa [reflectPlaquetteIndex] using trace_plaquetteProduct_reflect_ss' N T L U n 1 1 (by decide) (by decide)
  · simpa [reflectPlaquetteIndex] using trace_plaquetteProduct_reflect_ss' N T L U n 1 2 (by decide) (by decide)
  · simpa [reflectPlaquetteIndex] using trace_plaquetteProduct_reflect_ss' N T L U n 1 3 (by decide) (by decide)
  · simpa [reflectPlaquetteIndex] using trace_plaquetteProduct_reflect_st N T L U n 2 (by decide)
  · simpa [reflectPlaquetteIndex] using trace_plaquetteProduct_reflect_ss' N T L U n 2 1 (by decide) (by decide)
  · simpa [reflectPlaquetteIndex] using trace_plaquetteProduct_reflect_ss' N T L U n 2 2 (by decide) (by decide)
  · simpa [reflectPlaquetteIndex] using trace_plaquetteProduct_reflect_ss' N T L U n 2 3 (by decide) (by decide)
  · simpa [reflectPlaquetteIndex] using trace_plaquetteProduct_reflect_st N T L U n 3 (by decide)
  · simpa [reflectPlaquetteIndex] using trace_plaquetteProduct_reflect_ss' N T L U n 3 1 (by decide) (by decide)
  · simpa [reflectPlaquetteIndex] using trace_plaquetteProduct_reflect_ss' N T L U n 3 2 (by decide) (by decide)
  · simpa [reflectPlaquetteIndex] using trace_plaquetteProduct_reflect_ss' N T L U n 3 3 (by decide) (by decide)
set_option maxHeartbeats 4000000 in
/-- Unconditional version: `plaquetteContribution_reflect_eq` without the `plaquetteNegative`
hypothesis.  The trace equality holds for any plaquette index `p`. -/
lemma plaquetteContribution_reflect_eq_all (N T L : ℕ) [NeZero T] [NeZero L] (β : ℝ)
    (U : LinkVariable (SU N) (PeriodicSite T L)) (p : PlaquetteIndex T L) :
    plaquetteContribution N β U p.1 p.2.1 p.2.2 =
    plaquetteContribution N β (reflectLinkVariable N U)
      (reflectPlaquetteIndex T L p).1 (reflectPlaquetteIndex T L p).2.1
      (reflectPlaquetteIndex T L p).2.2 := by
  rcases p with ⟨n, μ, ν⟩
  unfold plaquetteContribution
  rw [trace_plaquetteProduct_reflect_all N T L U n μ ν]

set_option maxHeartbeats 8000000 in
/-- **Link correspondence under reflection.** For any plaquette `p` and link position `j`,
the reflected link `(θ(link p j).1, (link p j).2)` equals `link (reflectPlaquetteIndex p) j'`
for some `j'`. The position `j'` is a permutation of `j` depending on the directions:
- (μ≠0, ν≠0): `j' = j` (spatial directions commute with reflection)
- (μ=0, ν≠0): `j' = j + 3` (time direction reversed)
- (μ≠0, ν=0): `j' = j + 1` (time direction reversed)
- (μ=0, ν=0): `j' = j + 2` (both time directions reversed)

This is the key lemma showing the reflection maps `interfacePlaqLinkFinset` to itself. -/
lemma plaquetteLinkIdx_reflect (T L : ℕ) [NeZero T] [NeZero L]
    (p : PlaquetteIndex T L) (j : Fin 4) :
    ∃ j' : Fin 4, plaquetteLinkIdx T L (reflectPlaquetteIndex T L p) j' =
      (ReflectSite.reflectSite (plaquetteLinkIdx T L p j).1, (plaquetteLinkIdx T L p j).2) := by
  rcases p with ⟨n, μ, ν⟩
  by_cases hμ : μ = 0
  · by_cases hν : ν = 0
    · subst hμ hν
      refine ⟨j + 2, ?_⟩
      fin_cases j <;>
        simp [plaquetteLinkIdx, reflectPlaquetteIndex, ReflectSite.reflectSite,
          reflectSitePeriodic, addVectorPeriodic]
    · subst hμ
      refine ⟨j + 3, ?_⟩
      fin_cases j <;> fin_cases ν <;> first
        | contradiction
        | simp [plaquetteLinkIdx, reflectPlaquetteIndex, ReflectSite.reflectSite,
            reflectSitePeriodic, addVectorPeriodic]
  · by_cases hν : ν = 0
    · subst hν
      refine ⟨j + 1, ?_⟩
      fin_cases j <;> fin_cases μ <;> first
        | contradiction
        | simp [plaquetteLinkIdx, reflectPlaquetteIndex, ReflectSite.reflectSite,
            reflectSitePeriodic, addVectorPeriodic]
    · refine ⟨j, ?_⟩
      fin_cases j <;> fin_cases μ <;> fin_cases ν <;> first
        | contradiction
        | simp [plaquetteLinkIdx, reflectPlaquetteIndex, ReflectSite.reflectSite,
            reflectSitePeriodic, addVectorPeriodic]

#print axioms plaquetteLinkIdx_reflect

set_option maxHeartbeats 1000000 in
/-- Reflection preserves the interface plaquette predicate: a plaquette is an
interface plaquette iff its reflection is. -/
lemma isInterfacePlaquette_reflect (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (p : PlaquetteIndex T L) :
    isInterfacePlaquette T L (reflectPlaquetteIndex T L p).1 (reflectPlaquetteIndex T L p).2.1
        (reflectPlaquetteIndex T L p).2.2 ↔
    isInterfacePlaquette T L p.1 p.2.1 p.2.2 := by
  have h1 := reflectPlaquetteIndex_sign T L hT p
  have h2 : plaquetteNegative T L (reflectPlaquetteIndex T L p) ↔ plaquettePositive T L p := by
    have h_inv : reflectPlaquetteIndex T L (reflectPlaquetteIndex T L p) = p :=
      reflectPlaquetteIndex_involution T L p
    have h' := reflectPlaquetteIndex_sign T L hT (reflectPlaquetteIndex T L p)
    simpa [h_inv] using h'.symm
  simp only [isInterfacePlaquette, plaquettePositive, plaquetteNegative]
  constructor
  · rintro ⟨hnpos, hnneg⟩
    exact ⟨mt h2.symm.mp hnneg, mt h1.symm.mp hnpos⟩
  · rintro ⟨hnpos, hnneg⟩
    exact ⟨mt h1.mp hnneg, mt h2.mp hnpos⟩

#print axioms isInterfacePlaquette_reflect

/-- The reflection of an interface link: maps `l = (n, μ)` to `(θn, μ)`.
The reflected link is again an interface link because reflection maps interface
plaquettes to interface plaquettes (`isInterfacePlaquette_reflect`) and maps
links of interface plaquettes to links of reflected interface plaquettes
(`plaquetteLinkIdx_reflect`). -/
def reflectInterfaceLink (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (l : InterfaceLink T L) : InterfaceLink T L :=
  ⟨(ReflectSite.reflectSite l.val.1, l.val.2), by
    have hl := l.prop
    simp only [interfacePlaqLinkFinset, Finset.mem_image, Finset.mem_univ, true_and,
      Prod.exists, exists_prop] at hl
    obtain ⟨p, j, hj⟩ := hl
    have hp : isInterfacePlaquette T L (reflectPlaquetteIndex T L p.val).1
        (reflectPlaquetteIndex T L p.val).2.1 (reflectPlaquetteIndex T L p.val).2.2 :=
      (isInterfacePlaquette_reflect T L hT p.val).mpr p.prop
    simp only [interfacePlaqLinkFinset, Finset.mem_image, Finset.mem_univ, true_and,
      Prod.exists, exists_prop]
    obtain ⟨j', hj'⟩ := plaquetteLinkIdx_reflect T L p.val j
    refine ⟨⟨reflectPlaquetteIndex T L p.val, hp⟩, j', ?_⟩
    rw [hj] at hj'
    exact hj'⟩

/-- `reflectInterfaceLink` is involutive: reflecting twice is the identity. -/
lemma reflectInterfaceLink_involution (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    (l : InterfaceLink T L) :
    reflectInterfaceLink T L hT (reflectInterfaceLink T L hT l) = l := by
  simp only [reflectInterfaceLink, Subtype.mk_eq_mk]
  ext <;> simp [ReflectSite.involution]

#print axioms reflectInterfaceLink_involution

/-- Reflection maps positive-time interface links to negative-time interface links. -/
lemma reflectInterfaceLink_mem_neg_of_pos (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    {l : InterfaceLink T L} (hl : l ∈ interfaceLinkPos T L) :
    reflectInterfaceLink T L hT l ∈ interfaceLinkNeg T L := by
  rw [interfaceLinkPos, Finset.mem_filter] at hl
  obtain ⟨_, hpos⟩ := hl
  rw [interfaceLinkNeg, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, reflectInterfaceLink]
  rw [signedTime_reflectSite hT l.val.1]
  omega

/-- Reflection maps negative-time interface links to positive-time interface links. -/
lemma reflectInterfaceLink_mem_pos_of_neg (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    {l : InterfaceLink T L} (hl : l ∈ interfaceLinkNeg T L) :
    reflectInterfaceLink T L hT l ∈ interfaceLinkPos T L := by
  rw [interfaceLinkNeg, Finset.mem_filter] at hl
  obtain ⟨_, hneg⟩ := hl
  rw [interfaceLinkPos, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, reflectInterfaceLink]
  rw [signedTime_reflectSite hT l.val.1]
  omega

/-- Reflection maps interface (time-0) interface links to interface interface links. -/
lemma reflectInterfaceLink_mem_int_of_int (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T)
    {l : InterfaceLink T L} (hl : l ∈ interfaceLinkInt T L) :
    reflectInterfaceLink T L hT l ∈ interfaceLinkInt T L := by
  rw [interfaceLinkInt, Finset.mem_filter] at hl
  obtain ⟨_, hint⟩ := hl
  rw [interfaceLinkInt, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, reflectInterfaceLink]
  rw [signedTime_reflectSite hT l.val.1, hint]
  omega

#print axioms reflectInterfaceLink_mem_neg_of_pos
#print axioms reflectInterfaceLink_mem_pos_of_neg
#print axioms reflectInterfaceLink_mem_int_of_int

/-- The reflection bijection between positive-time and negative-time interface
links.  This is the map `φ : interfaceLinkNeg → interfaceLinkPos` (read in
reverse) used by the reindexing `θ` in the σ-inversion lemma. -/
def reflectInterfaceLinkPosNegEquiv (T L : ℕ) [NeZero T] [NeZero L] (hT : Odd T) :
    {l : InterfaceLink T L // l ∈ interfaceLinkPos T L} ≃
    {l : InterfaceLink T L // l ∈ interfaceLinkNeg T L} where
  toFun l := ⟨reflectInterfaceLink T L hT l.val, reflectInterfaceLink_mem_neg_of_pos T L hT l.prop⟩
  invFun l := ⟨reflectInterfaceLink T L hT l.val, reflectInterfaceLink_mem_pos_of_neg T L hT l.prop⟩
  left_inv l := by
    apply Subtype.eq
    exact reflectInterfaceLink_involution T L hT l.val
  right_inv l := by
    apply Subtype.eq
    exact reflectInterfaceLink_involution T L hT l.val

#print axioms reflectInterfaceLinkPosNegEquiv

set_option maxHeartbeats 1000000 in
lemma neg_action_reflection_os_periodic (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (hT : Odd T) (U : LinkVariable (SU N) (PeriodicSite T L)) :
    wilsonActionOSNegative N T L β U =
    wilsonActionOSPositive N T L β (reflectLinkVariable N U) := by
  have h_neg_sum : wilsonActionOSNegative N T L β U = ∑ p : PlaquetteIndex T L,
      (if plaquetteNegative T L p then plaquetteContribution N β U p.1 p.2.1 p.2.2 else 0) := by
    unfold wilsonActionOSNegative
    simp [PlaquetteIndex, plaquetteNegative, Fintype.sum_prod_type]
  have h_pos_sum : wilsonActionOSPositive N T L β (reflectLinkVariable N U) = ∑ p : PlaquetteIndex T L,
      (if plaquettePositive T L p then plaquetteContribution N β (reflectLinkVariable N U) p.1 p.2.1 p.2.2 else 0) := by
    unfold wilsonActionOSPositive
    simp [PlaquetteIndex, plaquettePositive, Fintype.sum_prod_type]
  rw [h_neg_sum, h_pos_sum]
  let f : PlaquetteIndex T L → ℝ := λ p =>
    (if plaquetteNegative T L p then plaquetteContribution N β U p.1 p.2.1 p.2.2 else 0)
  let g : PlaquetteIndex T L → ℝ := λ p =>
    (if plaquettePositive T L p then plaquetteContribution N β (reflectLinkVariable N U) p.1 p.2.1 p.2.2 else 0)
  let e : PlaquetteIndex T L ≃ PlaquetteIndex T L := reflectPlaquetteIndexEquiv T L
  have h_eq (p : PlaquetteIndex T L) : f (e p) = g p := by
    have h_e_val : e p = reflectPlaquetteIndex T L p := rfl
    rw [h_e_val]
    have h_neg_iff_pos : plaquetteNegative T L (reflectPlaquetteIndex T L p) ↔ plaquettePositive T L p := by
      have h := reflectPlaquetteIndex_sign T L hT (reflectPlaquetteIndex T L p)
      have h_inv : reflectPlaquetteIndex T L (reflectPlaquetteIndex T L p) = p :=
        reflectPlaquetteIndex_involution T L p
      simpa [h_inv] using h.symm
    by_cases h : plaquettePositive T L p
    · have h_neg : plaquetteNegative T L (reflectPlaquetteIndex T L p) := (h_neg_iff_pos.mpr h)
      have h_contrib : plaquetteContribution N β U (reflectPlaquetteIndex T L p).1 (reflectPlaquetteIndex T L p).2.1
          (reflectPlaquetteIndex T L p).2.2 = plaquetteContribution N β (reflectLinkVariable N U) p.1 p.2.1 p.2.2 := by
        simpa [reflectPlaquetteIndex_involution T L p] using
          plaquetteContribution_reflect_eq_all N T L β U (reflectPlaquetteIndex T L p)
      dsimp [f, g]
      rw [if_pos h_neg, if_pos h, h_contrib]
    · have h_not_neg : ¬ plaquetteNegative T L (reflectPlaquetteIndex T L p) := mt h_neg_iff_pos.mp h
      dsimp [f, g]
      rw [if_neg h_not_neg, if_neg h]
  calc
    ∑ p : PlaquetteIndex T L, f p = ∑ p : PlaquetteIndex T L, f (e p) := by
      symm
      exact Fintype.sum_equiv e (λ p => f (e p)) f (λ p => rfl)
    _ = ∑ p : PlaquetteIndex T L, g p := by
      refine Finset.sum_congr rfl (λ p hp => ?_)
      rw [h_eq p]

set_option maxHeartbeats 1000000 in
lemma interface_action_reflection_symmetric_os_periodic (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (hT : Odd T) (U : LinkVariable (SU N) (PeriodicSite T L)) :
    wilsonActionOSInterface N T L β (reflectLinkVariable N U) =
    wilsonActionOSInterface N T L β U := by
  have h_sum_eq : wilsonActionOSInterface N T L β U = ∑ p : PlaquetteIndex T L,
      (if ¬ plaquettePositive T L p ∧ ¬ plaquetteNegative T L p then plaquetteContribution N β U p.1 p.2.1 p.2.2 else 0) := by
    unfold wilsonActionOSInterface
    simp [PlaquetteIndex, plaquettePositive, plaquetteNegative, Fintype.sum_prod_type]
  have h_sum_eq_reflect : wilsonActionOSInterface N T L β (reflectLinkVariable N U) = ∑ p : PlaquetteIndex T L,
      (if ¬ plaquettePositive T L p ∧ ¬ plaquetteNegative T L p then plaquetteContribution N β (reflectLinkVariable N U) p.1 p.2.1 p.2.2 else 0) := by
    unfold wilsonActionOSInterface
    simp [PlaquetteIndex, plaquettePositive, plaquetteNegative, Fintype.sum_prod_type]
  rw [h_sum_eq_reflect, h_sum_eq]
  let f : PlaquetteIndex T L → ℝ := λ p =>
    (if ¬ plaquettePositive T L p ∧ ¬ plaquetteNegative T L p then plaquetteContribution N β (reflectLinkVariable N U) p.1 p.2.1 p.2.2 else 0)
  let g : PlaquetteIndex T L → ℝ := λ p =>
    (if ¬ plaquettePositive T L p ∧ ¬ plaquetteNegative T L p then plaquetteContribution N β U p.1 p.2.1 p.2.2 else 0)
  let e : PlaquetteIndex T L ≃ PlaquetteIndex T L := reflectPlaquetteIndexEquiv T L
  have h_interface_inv (p : PlaquetteIndex T L) : 
      (¬ plaquettePositive T L (reflectPlaquetteIndex T L p) ∧ ¬ plaquetteNegative T L (reflectPlaquetteIndex T L p)) ↔
      (¬ plaquettePositive T L p ∧ ¬ plaquetteNegative T L p) := by
    have h1 := reflectPlaquetteIndex_sign T L hT p
    have h2 : plaquetteNegative T L (reflectPlaquetteIndex T L p) ↔ plaquettePositive T L p := by
      have h_inv : reflectPlaquetteIndex T L (reflectPlaquetteIndex T L p) = p :=
        reflectPlaquetteIndex_involution T L p
      have h' := reflectPlaquetteIndex_sign T L hT (reflectPlaquetteIndex T L p)
      simpa [h_inv] using h'.symm
    constructor
    · rintro ⟨hnpos, hnneg⟩
      constructor
      · exact mt h2.symm.mp hnneg
      · exact mt h1.symm.mp hnpos
    · rintro ⟨hnpos, hnneg⟩
      constructor
      · exact mt h1.mp hnneg
      · exact mt h2.mp hnpos
  have h_eq (p : PlaquetteIndex T L) : f (e p) = g p := by
    have h_e_val : e p = reflectPlaquetteIndex T L p := rfl
    rw [h_e_val]
    have h_cond : ¬ plaquettePositive T L (reflectPlaquetteIndex T L p) ∧ ¬ plaquetteNegative T L (reflectPlaquetteIndex T L p) ↔
      ¬ plaquettePositive T L p ∧ ¬ plaquetteNegative T L p := h_interface_inv p
    dsimp [f, g]
    by_cases hi : (¬ plaquettePositive T L p ∧ ¬ plaquetteNegative T L p)
    · rw [if_pos hi, if_pos ((h_interface_inv p).mpr hi)]
      rw [← plaquetteContribution_reflect_eq_all N T L β U p]
    · rw [if_neg hi, if_neg (mt (h_interface_inv p).mp hi)]
  calc
    ∑ p : PlaquetteIndex T L, f p = ∑ p : PlaquetteIndex T L, f (e p) := by
      symm
      exact Fintype.sum_equiv e (λ p => f (e p)) f (λ p => rfl)
    _ = ∑ p : PlaquetteIndex T L, g p := by
      refine Finset.sum_congr rfl (λ p hp => ?_)
      rw [h_eq p]
/-- The Osterwalder-Seiler "G" function: the Boltzmann factor for the positive
half-lattice, including the interface action at half weight.  This is the
function whose integral `∫ G(U)·G(θU) dμ₀` must be shown non-negative. -/
noncomputable def osG (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ)
    (U : LinkVariable (SU N) (PeriodicSite T L)) : ℝ :=
  f U * Real.exp (-β * wilsonActionOSPositive N T L β U) *
  Real.exp (-β * wilsonActionOSInterface N T L β U / 2)
/-! ## Key gauge-invariance lemma: matrix elements vanish for non-trivial representations

For a gauge-invariant function `φ`, the integral `∫ φ(U) · (ρ_γ(U(x,μ)))_{r,s} dμ(U)`
vanishes for non-trivial irreducible representations `γ ≠ trivial`.  This is the key
lemma for closing `transferMatrixPositivity_axiom`: it shows that the character
expansion of a gauge-invariant function collapses to the trivial representation,
where the cyclic-shift obstacle (§8.11.51) disappears.
-/

open MeasureTheory
open Complex
open scoped ComplexConjugate

/-- For a gauge-invariant `φ`, the integral `∫ φ(ext cfg) · f(ext cfg .value x μ) dμ₀`
is invariant under left-multiplying the link `U(x,μ)` by any `h ∈ SU(N)`. -/
lemma gaugeInvariant_integral_leftMul
    (N : ℕ) {Λ : Type} [DecidableEq Λ] [AddVector Λ] [Fintype Λ]
    (φ : LinkVariable (SU N) Λ → ℂ)
    (hφ_gauge : IsGaugeInvariantC N φ)
    (x : Λ) (μ : Fin 4) (h_xμ : AddVector.addVector x μ ≠ x)
    (f : SU N → ℂ)
    (h_int : Integrable (fun cfg =>
        φ (extendLinkVariable N Λ Finset.univ cfg) * f ((extendLinkVariable N Λ Finset.univ cfg).value x μ))
        (productHaarMeasure N Λ Finset.univ))
    (h : SU N) :
    ∫ (cfg : FiniteLinkConfig N Λ Finset.univ),
        φ (extendLinkVariable N Λ Finset.univ cfg) * f ((extendLinkVariable N Λ Finset.univ cfg).value x μ)
        ∂(productHaarMeasure N Λ Finset.univ) =
    ∫ (cfg : FiniteLinkConfig N Λ Finset.univ),
        φ (extendLinkVariable N Λ Finset.univ cfg) * f (h * (extendLinkVariable N Λ Finset.univ cfg).value x μ)
        ∂(productHaarMeasure N Λ Finset.univ) := by
  set μ₀ : Measure _ := productHaarMeasure N Λ Finset.univ with hμ₀
  set ext := extendLinkVariable N Λ Finset.univ
  set g_h : Λ → SU N := fun y => if y = x then h else 1 with hg_h
  have h_mp : MeasurePreserving (gaugeTransformConfig N Finset.univ g_h) μ₀ μ₀ :=
    gaugeTransformConfig_measurePreserving N Finset.univ g_h
  have h_map : Measure.map (gaugeTransformConfig N Finset.univ g_h) μ₀ = μ₀ := h_mp.map_eq
  have h_aemeas : AEMeasurable (gaugeTransformConfig N Finset.univ g_h) μ₀ := h_mp.measurable.aemeasurable
  have h_aesm : AEStronglyMeasurable (fun cfg => φ (ext cfg) * f ((ext cfg).value x μ)) μ₀ :=
    h_int.aestronglyMeasurable
  have h1 : ∫ (cfg : _), φ (ext cfg) * f ((ext cfg).value x μ) ∂μ₀ =
      ∫ (cfg : _), φ (ext cfg) * f ((ext cfg).value x μ) ∂(Measure.map (gaugeTransformConfig N Finset.univ g_h) μ₀) := by rw [h_map]
  rw [h1, integral_map h_aemeas (by rw [h_map]; exact h_aesm)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro cfg
  show φ (extendLinkVariable N Λ Finset.univ (gaugeTransformConfig N Finset.univ g_h cfg)) *
      f ((extendLinkVariable N Λ Finset.univ (gaugeTransformConfig N Finset.univ g_h cfg)).value x μ) =
    φ (extendLinkVariable N Λ Finset.univ cfg) *
    f (h * (extendLinkVariable N Λ Finset.univ cfg).value x μ)
  rw [extendLinkVariable_gaugeTransformConfig N g_h cfg]
  rw [hφ_gauge g_h (extendLinkVariable N Λ Finset.univ cfg)]
  have h_key : (gaugeTransformLinkVariable N g_h (extendLinkVariable N Λ Finset.univ cfg)).value x μ =
      h * (extendLinkVariable N Λ Finset.univ cfg).value x μ :=
    gaugeTransformLinkVariable_single_site N x μ h (extendLinkVariable N Λ Finset.univ cfg) h_xμ
  rw [h_key]

/-- **Key lemma: matrix elements of non-trivial representations vanish for gauge-invariant φ.**

For a gauge-invariant `φ`, an irreducible unitary representation `ρ_σ` with `σ ≠ σ_0`
(trivial), and a link `(x, μ)` with `x + e_μ ≠ x`:
`∫ φ(U) · (ρ_σ(U(x,μ)))_{r,s} dμ(U) = 0`.

Proof: by gauge invariance, the integral is invariant under `U(x,μ) ↦ h · U(x,μ)`.
Expanding `(ρ(h·U))_{r,s} = Σ_k (ρ h)_{r,k} · (ρ U)_{k,s}` and averaging over `h`
gives `A_{r,s} = Σ_k [∫ (ρ h)_{r,k} dμ(h)] · A_{k,s}`.  By Schur orthogonality,
`∫ (ρ h)_{r,k} dμ = 0` for `σ ≠ σ_0`, hence `A_{r,s} = 0`. -/
lemma gaugeInvariant_matrixElement_integral_zero
    (N : ℕ) {Λ : Type} [DecidableEq Λ] [AddVector Λ] [Fintype Λ]
    (φ : LinkVariable (SU N) Λ → ℂ)
    (hφ_gauge : IsGaugeInvariantC N φ)
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ) (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (σ_0 : ι) (hσ_0_dims : dims σ_0 = 1) (hσ_0_trivial : ∀ g, (ρ σ_0 g) = 1)
    (σ : ι) (hσ_ne : σ ≠ σ_0)
    (x : Λ) (μ : Fin 4) (h_xμ : AddVector.addVector x μ ≠ x)
    (r : Fin (dims σ)) (s : Fin (dims σ))
    (hφ_int_all : ∀ (k : Fin (dims σ)) (j : Fin (dims σ)),
        Integrable (fun cfg =>
          φ (extendLinkVariable N Λ Finset.univ cfg) *
          (ρ σ ((extendLinkVariable N Λ Finset.univ cfg).value x μ)) k j)
          (productHaarMeasure N Λ Finset.univ)) :
    ∫ (cfg : FiniteLinkConfig N Λ Finset.univ),
        φ (extendLinkVariable N Λ Finset.univ cfg) *
        (ρ σ ((extendLinkVariable N Λ Finset.univ cfg).value x μ)) r s
        ∂(productHaarMeasure N Λ Finset.univ) = 0 := by
  set μ₀ : Measure _ := productHaarMeasure N Λ Finset.univ with hμ₀
  set ext := extendLinkVariable N Λ Finset.univ
  set A : Fin (dims σ) → Fin (dims σ) → ℂ := fun k j =>
    ∫ (cfg : FiniteLinkConfig N Λ Finset.univ), φ (ext cfg) * (ρ σ ((ext cfg).value x μ)) k j ∂μ₀
  let K : TopologicalSpace.PositiveCompacts (SU N) :=
    ⟨⟨Set.univ, isCompact_univ⟩, by simpa using Set.univ_nonempty (α := SU N)⟩
  set ν : Measure (SU N) := MeasureTheory.Measure.haarMeasure K with hν
  haveI : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    simpa [K, hν] using MeasureTheory.Measure.haarMeasure_self (K₀ := K)
  -- Key identity: for all h, A r s = Σ_k (ρ_σ h)_{r,k} · A_{k,s}
  have h_id : ∀ (h : SU N), A r s = ∑ k : Fin (dims σ), (ρ σ h) r k * A k s := by
    intro h
    have h_leftMul := gaugeInvariant_integral_leftMul N φ hφ_gauge x μ h_xμ
      (fun g => (ρ σ g) r s) (hφ_int_all r s) h
    -- Unfold A r s on the LHS
    show (∫ (cfg : FiniteLinkConfig N Λ Finset.univ), φ (ext cfg) * (ρ σ ((ext cfg).value x μ)) r s ∂μ₀) = _
    rw [h_leftMul]
    have h_expand : ∀ (cfg : FiniteLinkConfig N Λ Finset.univ),
        (ρ σ (h * (ext cfg).value x μ)) r s =
        ∑ k : Fin (dims σ), (ρ σ h) r k * (ρ σ ((ext cfg).value x μ)) k s := by
      intro cfg
      rw [MonoidHom.map_mul (ρ σ) h ((ext cfg).value x μ), Matrix.mul_apply]
    rw [integral_congr_ae (Filter.Eventually.of_forall (fun cfg => by
      show φ (ext cfg) * (ρ σ (h * (ext cfg).value x μ)) r s =
        ∑ k : Fin (dims σ), (ρ σ h) r k * (φ (ext cfg) * (ρ σ ((ext cfg).value x μ)) k s)
      rw [h_expand cfg, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by ring)))]
    rw [integral_finsetSum Finset.univ (fun k _ => (hφ_int_all k s).const_mul ((ρ σ h) r k))]
    simp only [integral_const_mul, A]
  -- Schur orthogonality: ∫ (ρ_σ h)_{r,k} dν = 0 for σ ≠ σ_0
  have h_int_schur : ∀ (k : Fin (dims σ)),
      ∫ (h : SU N), (ρ σ h) r k ∂ν = 0 := by
    intro k
    have h := integral_matrix_element_trivial_projection ν ι dims hDims ρ hU hIrr
      σ_0 hσ_0_dims hσ_0_trivial σ r k
    rw [h, if_neg hσ_ne]
  -- Integrate h_id over h: A r s = Σ_k A_{k,s} · 0 = 0
  have h_const_int : ∫ (h : SU N), A r s ∂ν = A r s := by
    rw [integral_const]; simp
  -- Integrability of the sum for the exchange
  obtain ⟨hInt, _, _⟩ := characterOrthogonality ν ι dims hDims ρ hU hIrr
  have i0 : Fin (dims σ_0) := ⟨0, hDims σ_0⟩
  have h_conj00 : ∀ h, conj ((ρ σ_0 h) i0 i0) = 1 := by
    intro h; rw [hσ_0_trivial h]; simp [Matrix.one_apply]
  have h_int_rk : ∀ (k : Fin (dims σ)), Integrable (fun h => (ρ σ h) r k) ν := by
    intro k
    have h := hInt σ σ_0 r k i0 i0
    have h_eq : (fun h => (ρ σ h) r k * conj ((ρ σ_0 h) i0 i0)) = (fun h => (ρ σ h) r k) := by
      funext h; rw [h_conj00 h, mul_one]
    rw [h_eq] at h
    exact h
  have h_int_summand : ∀ (k : Fin (dims σ)), Integrable (fun h => (ρ σ h) r k * A k s) ν := by
    intro k
    have h := (h_int_rk k).const_mul (A k s)
    exact Integrable.congr h (Filter.Eventually.of_forall (fun g => by ring))
  have h_int_sum : Integrable (fun h => ∑ k : Fin (dims σ), (ρ σ h) r k * A k s) ν :=
    integrable_finsetSum Finset.univ (fun k _ => h_int_summand k)
  have h_zero : A r s = 0 := by
    have h_eq : A r s = ∫ (h : SU N), ∑ k : Fin (dims σ), (ρ σ h) r k * A k s ∂ν := by
      rw [← h_const_int]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun h => h_id h))
    rw [h_eq, integral_finsetSum Finset.univ (fun k _ => h_int_summand k)]
    simp only [integral_mul_const, h_int_schur]
    simp
  exact h_zero

#print axioms gaugeInvariant_matrixElement_integral_zero

/-- **Axiom (Transfer-matrix positivity).**

For `f` depending only on positive-time and **spatial** interface links (i.e.
`dependsOnlyOnPosSpatialInterface`), the integral `∫ G(U)·G(θU) dμ₀ ≥ 0`,
where `G = osG` is the Osterwalder-Seiler Boltzmann factor and `θ` is the
time-reflection.

⚠️ **The hypothesis `dependsOnlyOnPosSpatialInterface` (not the weaker
`dependsOnlyOnPosInterface`) is essential.**  The weaker condition allows `f`
to depend on temporal interface links (`μ = 0` at `t = 0`), for which the
axiom is **false**: for `β = 0`, `f(g) = Im Tr(g)` on a single temporal
interface link gives `∫ f(g)·f(g⁻¹) dg = -∫ (Im Tr(g))² dg < 0`.  The
temporal-link inversion `σ` (which inverts `μ = 0` links at the interface)
is the sole obstacle.  See `docs/transfer_matrix_positivity_design.md`
§8.11.36.

This is the positivity of the transfer matrix `T` constructed from the
plaquette Boltzmann factor.  The mathematical justification is:

1. The plaquette Boltzmann factor `exp(c·Re Tr(g₁g₂g₃g₄))` is a
   positive-definite function on `SU(N)⁴` — this is proved (from the
   Peter-Weyl / Clebsch-Gordan axiom) in `PeterWeyl.lean` as
   `plaquetteBoltzmannPD`.
2. Positive-definiteness of the plaquette factor implies that the transfer
   matrix `T` (which integrates out the negative-time links with the
   reflection kernel) is a positive operator on `L²(SU(N)^{spatial})`.
   The temporal interface links are integrated out as part of the transfer
   matrix kernel (Lüscher decomposition `T = V^{1/2}·U·V^{1/2}`), avoiding
   the `σ` twist.
3. The identity `∫ G(U)·G(θU) dμ₀ = ∫ g(u)·(Tg)(u) dμ⁺⁰` (proved in
   `TransferMatrix.lean` as `integral_G_thetaG_eq_inner_g_Tg`) then gives
   `∫ G·G(θU) ≥ 0` from the positivity of `T`.

Steps 2–3 require the full transfer-matrix construction (measure-theoretic
factorization of the product Haar measure, Fubini, and the character-expansion
argument).  The positive-definiteness of the plaquette factor (step 1) is the
key input and is proved in `PeterWeyl.lean`; the remaining measure theory is
axiomatized here.  See `docs/found_issues.md` §3 and `docs/gap_analysis.md`.

Note: a gauge-invariance hypothesis (`IsGaugeInvariant N f`) was previously
included (session 62) based on the §8.11.51 analysis, but has been REMOVED
(session 65) after §8.11.53 showed that analysis was flawed — the positivity
holds for ALL `f` with `dependsOnlyOnPosSpatialInterface`, not just
gauge-invariant `f`.  See `docs/transfer_matrix_positivity_design.md` §8.11.53. -/
axiom transferMatrixPositivity_axiom (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (hT : Odd T) (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ)
    (hf_supported : dependsOnlyOnPosSpatialInterface N T L f) :
    0 ≤ ∫ (cfg : FiniteLinkConfig N (PeriodicSite T L)
        (Finset.univ : Finset (PeriodicSite T L))),
      osG N T L β f
        (extendLinkVariable N (PeriodicSite T L)
          (Finset.univ : Finset (PeriodicSite T L)) cfg) *
      osG N T L β f
        (reflectLinkVariable N
          (extendLinkVariable N (PeriodicSite T L)
            (Finset.univ : Finset (PeriodicSite T L)) cfg))
      ∂ productHaarMeasure N (PeriodicSite T L)
        (Finset.univ : Finset (PeriodicSite T L))

lemma gibbsExpectationPeriodic_reflection_positive (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (hT : Odd T) (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ)
    (hf_supported : dependsOnlyOnPosSpatialInterface N T L f) :
    0 ≤ gibbsExpectation N β (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))
      (λ U => f U * reflectObservable N f U) := by
  dsimp [gibbsExpectation]
  have hZ_pos : partitionFunctionFinite N β (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) > 0 :=
    partitionFunctionFinite_pos N β (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))
  refine div_nonneg ?_ (le_of_lt hZ_pos)
  set μ₀ := productHaarMeasure N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) with hμ₀
  set S_total := wilsonActionFiniteConfig N β (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) with hS
  set U_ext := extendLinkVariable N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L)) with hU
  have h_total_decomp : ∀ (cfg : FiniteLinkConfig N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))),
      S_total cfg = wilsonActionOSPositive N T L β (U_ext cfg) +
        wilsonActionOSNegative N T L β (U_ext cfg) +
        wilsonActionOSInterface N T L β (U_ext cfg) := by
    intro cfg
    calc
      S_total cfg = wilsonActionFinite N β (Finset.univ : Finset (PeriodicSite T L)) (U_ext cfg) := rfl
      _ = wilsonActionOSPositive N T L β (U_ext cfg) +
          wilsonActionOSNegative N T L β (U_ext cfg) +
          wilsonActionOSInterface N T L β (U_ext cfg) :=
        total_decomposition_os_periodic N T L β (U_ext cfg)
  have h_neg_reflect : ∀ (cfg : FiniteLinkConfig N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))),
      wilsonActionOSNegative N T L β (U_ext cfg) =
      wilsonActionOSPositive N T L β (reflectLinkVariable N (U_ext cfg)) := by
    intro cfg
    exact neg_action_reflection_os_periodic N T L β hT (U_ext cfg)
  have h_int_reflect : ∀ (cfg : FiniteLinkConfig N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))),
      wilsonActionOSInterface N T L β (reflectLinkVariable N (U_ext cfg)) =
      wilsonActionOSInterface N T L β (U_ext cfg) := by
    intro cfg
    exact interface_action_reflection_symmetric_os_periodic N T L β hT (U_ext cfg)
  have h_factorization : ∀ (cfg : FiniteLinkConfig N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))),
      Real.exp (-β * S_total cfg) = 
      (Real.exp (-β * wilsonActionOSPositive N T L β (U_ext cfg)) *
        Real.exp (-β * wilsonActionOSInterface N T L β (U_ext cfg) / 2)) *
      (Real.exp (-β * wilsonActionOSPositive N T L β (reflectLinkVariable N (U_ext cfg))) *
        Real.exp (-β * wilsonActionOSInterface N T L β (reflectLinkVariable N (U_ext cfg)) / 2)) := by
    intro cfg
    rw [h_total_decomp cfg]
    have h_mul : -β * (wilsonActionOSPositive N T L β (U_ext cfg) + wilsonActionOSNegative N T L β (U_ext cfg) +
      wilsonActionOSInterface N T L β (U_ext cfg)) = 
      (-β * wilsonActionOSPositive N T L β (U_ext cfg)) + 
      (-β * wilsonActionOSNegative N T L β (U_ext cfg)) + 
      (-β * wilsonActionOSInterface N T L β (U_ext cfg)) := by ring
    rw [h_mul]
    rw [Real.exp_add, Real.exp_add]
    rw [h_neg_reflect cfg, h_int_reflect cfg]
    have h_exp_split : Real.exp (-β * wilsonActionOSInterface N T L β (U_ext cfg)) =
      Real.exp (-β * wilsonActionOSInterface N T L β (U_ext cfg) / 2) *
      Real.exp (-β * wilsonActionOSInterface N T L β (U_ext cfg) / 2) := by
      calc
        Real.exp (-β * wilsonActionOSInterface N T L β (U_ext cfg)) =
          Real.exp ((-β * wilsonActionOSInterface N T L β (U_ext cfg) / 2) +
                   (-β * wilsonActionOSInterface N T L β (U_ext cfg) / 2)) := by ring
        _ = Real.exp (-β * wilsonActionOSInterface N T L β (U_ext cfg) / 2) *
            Real.exp (-β * wilsonActionOSInterface N T L β (U_ext cfg) / 2) := by rw [Real.exp_add]
    rw [h_exp_split]
    ring
  set G := osG N T L β f with hG
  have h_integrand_eq : ∀ (cfg : FiniteLinkConfig N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))),
      f (U_ext cfg) * f (reflectLinkVariable N (U_ext cfg)) *
      Real.exp (-β * S_total cfg) =
      G (U_ext cfg) * G (reflectLinkVariable N (U_ext cfg)) := by
    intro cfg
    dsimp [G, osG]
    rw [h_factorization cfg]
    ring
  have h_fun_eq : (λ (cfg : FiniteLinkConfig N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))) =>
      f (U_ext cfg) * f (reflectLinkVariable N (U_ext cfg)) * Real.exp (-β * S_total cfg)) =
    (λ (cfg : FiniteLinkConfig N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))) =>
      G (U_ext cfg) * G (reflectLinkVariable N (U_ext cfg))) := by
    ext cfg; exact h_integrand_eq cfg
  calc
    (∫ (cfg : FiniteLinkConfig N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))),
      f (U_ext cfg) * f (reflectLinkVariable N (U_ext cfg)) * Real.exp (-β * S_total cfg) ∂ μ₀)
        = (∫ (cfg : FiniteLinkConfig N (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))),
      G (U_ext cfg) * G (reflectLinkVariable N (U_ext cfg)) ∂ μ₀) := by
      rw [h_fun_eq]
    _ ≥ 0 := by
      -- GOAL: Prove that ∫ G(U)·G(θU) dμ₀(U) ≥ 0.
      -- The positivity follows from `transferMatrixPositivity_axiom`, which is
      -- justified by `plaquetteBoltzmannPD` (Peter-Weyl / Clebsch-Gordan) ⟹
      -- transfer matrix T positive ⟹ ∫ G·G(θU) ≥ 0.  See the axiom's docstring.
      exact transferMatrixPositivity_axiom N T L β hT f hf_supported

