/-
# Lattice Gauge Theory

Formalization of lattice gauge theory: Wilson action, plaquette variables,
and the continuum limit.
-/

namespace YangMills

namespace Lattice

/--
A finite lattice Λ ⊂ ℤ⁴ as a hypercube with spacing a.
-/
structure Lattice (Λ : Type) : Type 1 where
  spacing : Nat → Nat -- placeholder for ℝ
  sites : Λ
  links : Λ → Λ → Prop
  plaquettes : (Λ × Λ × Λ × Λ) → Prop

/--
A gauge field configuration on the lattice: each link (x, μ) carries a
group element U(x, μ) ∈ G.
-/
structure LinkVariable (G : Type) (Λ : Type) : Type 1 where
  value : Λ → Fin 4 → G

/--
The Wilson plaquette action S_W[U].
-/
structure WilsonAction (G : Type) (Λ : Type) : Type 1 where
  beta : Nat → Nat -- placeholder for ℝ
  evaluate : LinkVariable G Λ → Nat → Nat

/--
The Yang-Mills measure on the lattice.
-/
structure LatticeMeasure (G : Type) (Λ : Type) : Type 1 where
  partitionFunction : Nat → Nat
  density : LinkVariable G Λ → Nat → Nat

/--
Continuum limit: as lattice spacing a → 0, the lattice theory should
converge to the continuum Yang-Mills theory.
-/
structure ContinuumLimit : Prop where
  existsLimit : True

end Lattice

end YangMills
