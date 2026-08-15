/-
# Peter-Weyl: Finite Sums of Positive-Definite Functions
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.Pi
import YangMills.Proofs.PositiveDefinite

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open Finset
open Matrix
open MeasureTheory
open scoped ComplexConjugate

namespace YangMills
/-! ## Finite sums of positive-definite functions -/

section PositiveDefiniteSum

variable {G : Type*} [Group G]

/-- A finite weighted sum of positive-definite functions with non-negative real
weights is positive-definite.  This is the workhorse for building PD functions
out of character expansions. -/
lemma PositiveDefinite.sum {α : Type*} (s : Finset α)
    (f : α → G → ℂ) (hf : ∀ a ∈ s, PositiveDefinite (f a))
    (w : α → ℝ) (hw : ∀ a ∈ s, 0 ≤ w a) :
    PositiveDefinite (λ g => ∑ a ∈ s, (w a : ℂ) * f a g) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact PositiveDefinite.zero
  | insert x s hx ih =>
    have hPDx : PositiveDefinite (λ g => (w x : ℂ) * f x g) :=
      PositiveDefinite.smul_nonneg (hw x (Finset.mem_insert_self x s))
        (hf x (Finset.mem_insert_self x s))
    have hPDs : PositiveDefinite (λ g => ∑ a ∈ s, (w a : ℂ) * f a g) :=
      ih (fun a ha => hf a (Finset.mem_insert_of_mem ha))
        (fun a ha => hw a (Finset.mem_insert_of_mem ha))
    have heq : (λ g => ∑ a ∈ insert x s, (w a : ℂ) * f a g) =
        (λ g => (w x : ℂ) * f x g + ∑ a ∈ s, (w a : ℂ) * f a g) := by
      funext g; rw [Finset.sum_insert hx]
    rw [heq]
    exact PositiveDefinite.add hPDx hPDs

/-- An unweighted finite sum of positive-definite functions is positive-definite. -/
lemma PositiveDefinite.sum' {α : Type*} (s : Finset α)
    (f : α → G → ℂ) (hf : ∀ a ∈ s, PositiveDefinite (f a)) :
    PositiveDefinite (λ g => ∑ a ∈ s, f a g) := by
  have h := PositiveDefinite.sum s f hf (fun _ => 1) (fun _ _ => by norm_num)
  have heq : (λ g => ∑ a ∈ s, (1 : ℂ) * f a g) = (λ g => ∑ a ∈ s, f a g) := by
    funext g; exact Finset.sum_congr rfl (fun a _ => one_mul _)
  rw [← heq]; exact h

end PositiveDefiniteSum

