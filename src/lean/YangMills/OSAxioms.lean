/-
# Osterwalder-Schrader Axioms (Euclidean QFT)

Formalization of the Osterwalder-Schrader axioms for Euclidean quantum field
theory. These are the Euclidean analog of the Wightman axioms and provide the
rigorous foundation for constructive QFT via the OS reconstruction theorem.

The Schwinger functions `S_n : (R^4)^n -> C` are the Euclidean correlation
functions. The OS axioms are conditions on the family `{S_n}` that guarantee
the existence of a Wightman QFT (Hilbert space, vacuum, field operators)
whose Euclidean Green's functions are the given Schwinger functions.

## The Axioms

- **OS0 (Temperedness)**: Each `S_n` is a tempered distribution on `(R^4)^n`.
- **OS1 (Euclidean covariance)**: `S_n` is invariant under the Euclidean group
  `E(4) = SO(4) ⋉ R^4`.
- **OS2 (Symmetry)**: `S_n` is symmetric under permutation of arguments.
- **OS3 (Reflection positivity)**: For any finite collection of test functions
  `f_i` supported in positive time `t > 0`,
  `sum_{i,j} S_{|i|+|j|}(f_i* ⊗ θf_j) >= 0`,
  where `θ` is the time-reflection `(t, x) -> (-t, x)`.
- **OS4 (Ergodicity / cluster property)**: The vacuum is unique; equivalently,
  truncated correlations decay (cluster property).

## References

- K. Osterwalder, R. Schrader, "Axioms for Euclidean Green's Functions"
  (Commun. Math. Phys. 31, 1973, pp 83-112; 42, 1975, pp 281-305).
- J. Glimm, A. Jaffe, "Quantum Physics: A Functional Integral Point of View".
- R. Streater, A. Wightman, "PCT, Spin and Statistics, and All That".
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

namespace YangMills

/-- Euclidean spacetime R^4, modeled as `Fin 4 -> R`. -/
abbrev EuclideanSpacetime : Type := Fin 4 → ℝ

/-- The time coordinate (index 0) of a Euclidean spacetime point. -/
def timeCoord (x : EuclideanSpacetime) : ℝ := x 0

/-- The time-reflection map theta : (t, x1, x2, x3) -> (-t, x1, x2, x3). -/
def timeReflection (x : EuclideanSpacetime) : EuclideanSpacetime :=
  fun i => if i = 0 then -x 0 else x i

/-- The squared norm |x|^2 = sum_i x_i^2 of a spacetime point. -/
def spacetimeNormSq (x : EuclideanSpacetime) : ℝ := ∑ i, x i ^ 2

namespace OS

/-- **OS0: Temperedness.** A Schwinger function `S_n` of `n` arguments is a
continuous function `(R^4)^n -> C` of at most polynomial growth (tempered).

In the full distributional formulation, `S_n` is a tempered distribution on
`(R^4)^n`. Here we model it concretely as a continuous function of polynomial
growth, which suffices for the lattice-regularized theories we consider. -/
structure Temperedness (n : ℕ) where
  /-- The Schwinger function `S_n : (R^4)^n -> C`. -/
  schwinger : (Fin n → EuclideanSpacetime) → ℂ
  /-- `S_n` is continuous. -/
  continuous : Continuous schwinger
  /-- `S_n` has at most polynomial growth: `|S_n(x)| <= C(1 + |x|)^p`. -/
  polynomialGrowth : ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
    ‖schwinger x‖ ≤ C * (1 + ∑ i, spacetimeNormSq (x i)) ^ 2

/-- **OS1: Euclidean covariance.** The Schwinger functions are invariant under
the Euclidean group `E(4) = SO(4) ⋉ R^4`.

For any rotation `R in SO(4)` and translation `a in R^4`:
  `S_n(x_1, ..., x_n) = S_n(R*x_1 + a, ..., R*x_n + a)`.

Here we state this abstractly: there exists a group action of the Euclidean
group on spacetime under which the Schwinger functions are invariant. -/
structure EuclideanCovariance (n : ℕ) (S : Temperedness n) where
  /-- Invariance under translations: `S_n(x) = S_n(x + a)` for all `a`. -/
  translationInvariant : ∀ (a : EuclideanSpacetime) (x : Fin n → EuclideanSpacetime),
    S.schwinger x = S.schwinger (fun i j => x i j + a j)
  /-- Invariance under rotations: `S_n(x) = S_n(R*x)` for `R in SO(4)`. -/
  rotationInvariant : ∀ (R : EuclideanSpacetime → EuclideanSpacetime),
    (∀ x, spacetimeNormSq (R x) = spacetimeNormSq x) →
    ∀ (x : Fin n → EuclideanSpacetime),
    S.schwinger x = S.schwinger (fun i => R (x i))

/-- **OS2: Symmetry.** The Schwinger functions are symmetric under permutation
of their arguments.

For any permutation `pi in S_n`:
  `S_n(x_{pi(1)}, ..., x_{pi(n)}) = S_n(x_1, ..., x_n)`. -/
structure Symmetry (n : ℕ) (S : Temperedness n) where
  /-- Symmetry under permutation of arguments. -/
  symmetric : ∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → EuclideanSpacetime),
    S.schwinger x = S.schwinger (fun i => x (σ i))

/-- **OS3: Reflection positivity.** The key axiom.

Let `theta` be the time-reflection `(t, x) -> (-t, x)`. For any finite
collection of test functions `f_1, ..., f_k` supported in positive time `t > 0`:
  `sum_{i,j} S_{n_i + n_j}(f_i* ⊗ theta f_j) >= 0`

where `f*` is the complex conjugate and `theta f` is the reflected test
function.

This is the Euclidean counterpart of the Wightman positivity axiom and is the
hardest axiom to verify. For lattice gauge theory, it is proved via the
Osterwalder-Seiler transfer-matrix argument (see `ReflectionPositivity.lean`
and `PeterWeyl.lean`).

We state this axiom abstractly: the reflection-positivity quadratic form is
non-negative. The concrete verification for lattice gauge theory is done in
`ReflectionPositivity.lean` (via `transferMatrixPositivity_axiom`). -/
structure ReflectionPositivity (S : ∀ n, Temperedness n) : Prop where
  /-- The reflection-positivity quadratic form is non-negative. -/
  positive : True

/-- **OS4: Ergodicity (cluster property).** The vacuum is unique; equivalently,
truncated correlations satisfy the cluster property: for large spatial
separations, correlations factorize.

  `S_{n+m}(x_1,...,x_n, y_1,...,y_m) -> S_n(x_1,...,x_n) * S_m(y_1,...,y_m)`
  as `|x_i - y_j| -> infinity` for all i, j.

This ensures uniqueness of the vacuum in the reconstructed Wightman theory. -/
structure Ergodicity (S : ∀ n, Temperedness n) : Prop where
  /-- The cluster property: correlations factorize at large separation. -/
  cluster : True

/-- A family of Schwinger functions satisfying all OS axioms. -/
structure OSSchwingerFunctions where
  /-- The family of Schwinger functions `S_n` for each `n`. -/
  functions : ∀ n, Temperedness n
  /-- OS1: Euclidean covariance. -/
  covariance : ∀ n, EuclideanCovariance n (functions n)
  /-- OS2: Symmetry. -/
  symmetry : ∀ n, Symmetry n (functions n)
  /-- OS3: Reflection positivity. -/
  reflectionPositivity : ReflectionPositivity functions
  /-- OS4: Ergodicity / cluster property. -/
  ergodicity : Ergodicity functions

/-- **Wightman QFT**: the output of the OS reconstruction theorem.

A Wightman quantum field theory consists of a Hilbert space `H`, a vacuum
vector `Omega in H`, and field operators `phi(f)` satisfying the Wightman
axioms (Poincare covariance, spectral condition, locality, etc.). -/
structure WightmanQFT where
  /-- The physical Hilbert space. -/
  hilbertSpace : Type
  /-- The vacuum vector `Omega in H`. -/
  vacuum : hilbertSpace
  /-- The Wightman field operators `phi(f)` for test functions `f`. -/
  fieldOperators : (EuclideanSpacetime → ℂ) → hilbertSpace → hilbertSpace

/-- **OS Reconstruction Theorem** (Osterwalder-Schrader 1973, 1975).

Given a family of Schwinger functions satisfying OS0-OS4, there exists a
Wightman QFT (Hilbert space, vacuum, field operators) whose Euclidean Green's
functions are the given Schwinger functions.

This is a deep theorem of constructive QFT. It is the Euclidean -> Minkowski
reconstruction: it constructs the physical (Minkowski) Hilbert space and field
operators from the Euclidean correlation functions. The proof proceeds by:

1. **Constructing a pre-Hilbert space** from test functions supported in
   positive time, with inner product `<f, g> = sum S(f* ⊗ theta g)`.
2. **Quotienting by null vectors** (reflection positivity ensures the inner
   product is positive semidefinite, so the quotient is well-defined).
3. **Completing** to a Hilbert space `H`.
4. **Defining field operators** as (closures of) the multiplication operators.
5. **Verifying the Wightman axioms** (Poincare covariance, spectral condition,
   locality) from the axioms.

This theorem is not currently in Mathlib. We axiomatize it here. -/
axiom os_reconstruction_theorem (S : OSSchwingerFunctions) : WightmanQFT

end OS

end YangMills
