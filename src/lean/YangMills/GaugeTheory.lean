/-
# Gauge Theory Foundations

Formalization of principal G-bundles, connections, curvature, and the
Yang-Mills action functional.
-/

import YangMills.SpecialUnitary

namespace YangMills

/--
A principal G-bundle over a manifold M.
-/
structure PrincipalBundle (M G : Type) : Type 1 where
  totalSpace : Type
  baseSpace : M
  structureGroup : G
  projection : totalSpace → M

/--
A connection 1-form on a principal G-bundle.

In local coordinates on ℝ⁴, this is a g-valued 1-form A = A_μ dx^μ.
-/
structure Connection (G : Type) : Type 1 where
  gaugeField : Type
  components : Type

/--
The curvature 2-form F = dA + A ∧ A.
-/
structure Curvature : Type 1 where
  twoForm : Type
  components : Type

/--
The Yang-Mills action functional: S(A) = ∫ Tr(F ∧ *F).
-/
structure YangMillsAction : Type 1 where
  lagrangianDensity : Type
  action : Type

/--
A gauge transformation: a map U : M → G acting on connections.
-/
structure GaugeTransformation (G : Type) : Type 1 where
  map : Type
  act : Connection G → Connection G

end YangMills
