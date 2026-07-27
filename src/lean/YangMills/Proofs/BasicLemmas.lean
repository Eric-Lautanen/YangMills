/-
# Basic Proofs: Matrix Identities

Foundational lemmas for Yang-Mills formalization.

This file contains elementary proofs about matrices, traces, and the
conjugate transpose that are used throughout the project.
-/

import YangMills.SpecialUnitary
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

open Matrix
open scoped Matrix

namespace YangMills

section TraceLemmas

/--
The trace of a commutator of two matrices is zero:
  Tr([A, B]) = Tr(AB - BA) = 0
-/
lemma trace_commutator_zero (N : ℕ) (A B : Matrix (Fin N) (Fin N) ℂ) : trace (A * B - B * A) = 0 := by
  calc
    trace (A * B - B * A) = trace (A * B) - trace (B * A) := by
      simp
    _ = trace (A * B) - trace (A * B) := by
      rw [trace_mul_comm A B]
    _ = 0 := by simp

/--
Trace of a product is invariant under cyclic permutations:
  Tr(ABC) = Tr(BCA) = Tr(CAB)
-/
lemma trace_mul_rotate (N : ℕ) (A B C : Matrix (Fin N) (Fin N) ℂ) :
    trace (A * B * C) = trace (B * C * A) := by
  calc
    trace (A * B * C) = trace ((A * B) * C) := by rw [mul_assoc]
    _ = trace (C * (A * B)) := by rw [trace_mul_comm (A * B) C]
    _ = trace (C * A * B) := by rw [mul_assoc]
    _ = trace (B * (C * A)) := by rw [trace_mul_comm (C * A) B]
    _ = trace (B * C * A) := by rw [mul_assoc]

end TraceLemmas

section ConjTransposeLemmas

/--
The conjugate transpose is involutive: (A†)† = A.
-/
lemma conjTranspose_involutive (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ) : Aᴴᴴ = A := by
  simp

/--
Conjugate transpose distributes over multiplication: (AB)† = B† A†.
-/
lemma conjTranspose_mul_distrib (N : ℕ) (A B : Matrix (Fin N) (Fin N) ℂ) : (A * B)ᴴ = Bᴴ * Aᴴ := by
  simp

end ConjTransposeLemmas

section SkewHermitianLemmas

/--
If X is skew-Hermitian (X† = -X), then iX is Hermitian ((iX)† = iX).
This is important for the correspondence between Lie algebra and physical fields.
-/
lemma skewHermitian_to_hermitian (N : ℕ) (X : LieAlgebraSU N) : X.matrixᴴ = -X.matrix :=
  X.skewHermitian

end SkewHermitianLemmas

end YangMills
