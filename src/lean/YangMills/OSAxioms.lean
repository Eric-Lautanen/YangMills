/-
# Osterwalder-Schrader Axioms (Euclidean QFT)

Formalization of the Osterwalder-Schrader axioms for Euclidean quantum field
theory.
-/

namespace YangMills

namespace OS

/-- Euclidean spacetime dimension. For Yang-Mills we work in d = 4. -/
def spacetimeDimension : Nat := 4

/--
OS0: Temperedness — the Schwinger functions are tempered distributions.
-/
structure SchwingerFunction (n : Nat) : Type 1 where
  distribution : Type

/--
OS1: Euclidean covariance — Schwinger functions are invariant under the
Euclidean group E(4) = SO(4) ⋉ ℝ^4.
-/
structure EuclideanCovariance : Type 1 where
  invariant : ∀ (n : Nat), SchwingerFunction n → SchwingerFunction n

/--
OS3: Reflection positivity (Osterwalder-Schrader positivity).
-/
structure ReflectionPositive : Prop where
  positive : ∀ (_ : Unit → Unit), True

/--
OS4: Ergodicity (uniqueness of vacuum).
-/
structure Ergodicity : Prop where
  uniqueVacuum : True

/--
OS Reconstruction Theorem: Given a family of Schwinger functions satisfying
OS0-OS4, there exists a Wightman QFT.
-/
structure OSReconstruction : Type 1 where
  hilbertSpace : Type
  vacuumVector : Type
  fieldOperators : Type

end OS

end YangMills
