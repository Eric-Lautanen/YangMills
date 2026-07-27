/-
# Gauge Theory Foundations

Formalization of principal G-bundles, connections, curvature, and the
Yang-Mills action functional.

References:
- T. Balaban, "Renormalization group approach to lattice gauge field theories"
- M. Atiyah, "Geometry of Yang-Mills fields"
- S. Kobayashi, K. Nomizu, "Foundations of Differential Geometry"
-/

import YangMills.SpecialUnitary
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

open scoped Matrix

namespace YangMills

/--
The base manifold: ℝ⁴ (Euclidean spacetime).
We use `EuclideanSpace ℝ (Fin 4)` as a model for ℝ⁴.
-/
abbrev Spacetime : Type :=
  EuclideanSpace ℝ (Fin 4)

/--
A principal G-bundle over a manifold M.
In a full formalization this would be a fibre bundle with structure group G.
Here we give an abstract type for the total space with a projection to M.

TODO: Use Mathlib's `FiberBundle` when available.
-/
structure PrincipalBundle (M G : Type) : Type 1 where
  totalSpace : Type
  projection : totalSpace → M
  /-- Right action of G on the total space (place holder). -/
  rightAction : G → totalSpace → totalSpace

/--
A connection 1-form on a principal G-bundle with Lie algebra 𝔤.
In local coordinates on ℝ⁴, this is a 𝔤-valued 1-form A = A_μ dx^μ.

The connection is represented locally as a smooth map from spacetime to
the Lie algebra-valued 1-forms.
-/
structure Connection (𝔤 : Type) : Type 1 where
  /-- Local connection form: a 𝔤-valued 1-form on ℝ⁴. -/
  localForm : Spacetime → (Fin 4 → 𝔤)

/--
The curvature 2-form F = dA + A ∧ A.
In local coordinates F_{μν} = ∂_μ A_ν - ∂_ν A_μ + [A_μ, A_ν].
-/
structure Curvature (𝔤 : Type) : Type 1 where
  /-- Local curvature form: a 𝔤-valued 2-form on ℝ⁴. -/
  localForm : Spacetime → (Fin 4 → Fin 4 → 𝔤)

/--
The Yang-Mills action functional:
  S(A) = (1/2g²) ∫ Tr(F ∧ *F)
where F is the curvature, * is the Hodge star, and Tr is the trace on 𝔤.

For SU(N) gauge theory, the Lie algebra is su(N) and the trace is in the
fundamental representation.
-/
structure YangMillsAction (𝔤 : Type) : Type 1 where
  /-- The Yang-Mills Lagrangian density: L = (1/2) Tr(F_{μν} F^{μν}). -/
  lagrangianDensity : (Spacetime → 𝔤) → Spacetime → ℝ
  /-- The action functional: S(A) = ∫ L d⁴x. -/
  action : (Spacetime → 𝔤) → ℝ

/--
A gauge transformation: a map U : M → G acting on connections by
  A ↦ U A U⁻¹ + U dU⁻¹
-/
structure GaugeTransformation (G : Type) : Type 1 where
  /-- The gauge transformation map from spacetime to G. -/
  map : Spacetime → G
  /-- Action on a connection. -/
  act : ∀ (A : Type), A → A

end YangMills
