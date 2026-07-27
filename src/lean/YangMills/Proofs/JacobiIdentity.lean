/-
# Jacobi Identity for the su(N) Lie Algebra

We prove the Jacobi identity for the matrix commutator on su(N):

    [X, [Y, Z]] + [Y, [Z, X]] + [Z, [X, Y]] = 0

for all X, Y, Z in the Lie algebra su(N) (skew-Hermitian traceless matrices).

The proof is purely algebraic, using only the associativity of matrix
multiplication. It holds for any associative algebra, and thus in particular
for the matrix algebra M_N(ℂ).

Reference:
- R. Gilmore, "Lie Groups, Lie Algebras, and Some of Their Applications"
- Any text on Lie algebras
-/

import YangMills.SpecialUnitary
import Mathlib.LinearAlgebra.Matrix.Trace

open Matrix
open scoped Matrix

namespace YangMills

section JacobiIdentity

/--
The matrix commutator [X, Y] = XY - YX.
-/
def commutator (N : ℕ) (X Y : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  X * Y - Y * X

/--
The commutator is antisymmetric: [X, Y] = -[Y, X].
-/
lemma commutator_antisymmetric (N : ℕ) (X Y : Matrix (Fin N) (Fin N) ℂ) :
    commutator N X Y = -commutator N Y X := by
  dsimp [commutator]
  abel

/--
The Jacobi identity for the matrix commutator:

    [X, [Y, Z]] + [Y, [Z, X]] + [Z, [X, Y]] = 0

Proof: Expand each double commutator using [A,B] = AB - BA. After expansion,
the 12 monomials cancel pairwise.
-/
theorem jacobi_identity (N : ℕ) (X Y Z : Matrix (Fin N) (Fin N) ℂ) :
    commutator N X (commutator N Y Z) + commutator N Y (commutator N Z X)
    + commutator N Z (commutator N X Y) = 0 := by
  dsimp [commutator]
  -- Expand products using distributivity
  rw [mul_sub, sub_mul, mul_sub, sub_mul, mul_sub, sub_mul]
  -- Use associativity to simplify products
  simp [mul_assoc, sub_eq_add_neg]
  -- Now the goal is a sum of 12 terms with only + and unary -. Cancel pairs.
  abel

/--
The Jacobi identity for elements of the Lie algebra su(N).
This is the same identity, but restricted to the subalgebra of skew-Hermitian
traceless matrices.
-/
theorem jacobi_identity_su (N : ℕ) (X Y Z : LieAlgebraSU N) :
    commutator N X.matrix (commutator N Y.matrix Z.matrix)
    + commutator N Y.matrix (commutator N Z.matrix X.matrix)
    + commutator N Z.matrix (commutator N X.matrix Y.matrix) = 0 := by
  apply jacobi_identity N X.matrix Y.matrix Z.matrix

/--
The Jacobi identity in the form [[X,Y],Z] + [[Y,Z],X] + [[Z,X],Y] = 0.
This follows from the standard form using antisymmetry of the commutator:

    [[X,Y],Z] = -[Z,[X,Y]]
    [[Y,Z],X] = -[X,[Y,Z]]
    [[Z,X],Y] = -[Y,[Z,X]]

Summing gives -([Z,[X,Y]] + [X,[Y,Z]] + [Y,[Z,X]]) = 0 by jacobi_identity.
-/
theorem jacobi_identity_lie_bracket (N : ℕ) (X Y Z : LieAlgebraSU N) :
    commutator N (commutator N X.matrix Y.matrix) Z.matrix
    + commutator N (commutator N Y.matrix Z.matrix) X.matrix
    + commutator N (commutator N Z.matrix X.matrix) Y.matrix = 0 := by
  have h := jacobi_identity N X.matrix Y.matrix Z.matrix
  calc
    commutator N (commutator N X.matrix Y.matrix) Z.matrix
        + commutator N (commutator N Y.matrix Z.matrix) X.matrix
        + commutator N (commutator N Z.matrix X.matrix) Y.matrix
        = (-commutator N Z.matrix (commutator N X.matrix Y.matrix))
          + (-commutator N X.matrix (commutator N Y.matrix Z.matrix))
          + (-commutator N Y.matrix (commutator N Z.matrix X.matrix)) := by
      rw [commutator_antisymmetric N (commutator N X.matrix Y.matrix) Z.matrix,
        commutator_antisymmetric N (commutator N Y.matrix Z.matrix) X.matrix,
        commutator_antisymmetric N (commutator N Z.matrix X.matrix) Y.matrix]
    _ = -(commutator N Z.matrix (commutator N X.matrix Y.matrix)
          + commutator N X.matrix (commutator N Y.matrix Z.matrix)
          + commutator N Y.matrix (commutator N Z.matrix X.matrix)) := by
      abel
    _ = -(commutator N X.matrix (commutator N Y.matrix Z.matrix)
          + commutator N Y.matrix (commutator N Z.matrix X.matrix)
          + commutator N Z.matrix (commutator N X.matrix Y.matrix)) := by
      abel
    _ = -0 := by rw [h]
    _ = 0 := by simp

end JacobiIdentity

end YangMills
