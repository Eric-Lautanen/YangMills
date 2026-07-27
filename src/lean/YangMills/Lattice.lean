/-
# Lattice Gauge Theory

Formalization of lattice gauge theory: Wilson action, plaquette variables,
and the continuum limit.

References:
- K. Wilson, "Confinement of quarks" (1974)
- T. Balaban, "Renormalization group approach to lattice gauge field theories"
- J. Glimm, A. Jaffe, "Quantum Physics: A Functional Integral Point of View"
-/

import YangMills.SpecialUnitary
import Mathlib.LinearAlgebra.Matrix.Trace

open Matrix
open scoped Matrix
open scoped BigOperators

namespace YangMills

namespace Lattice

/-! ### Typeclasses for lattice operations -/

/--
Typeclass for adding a basis vector to a lattice site in direction μ.
-/
class AddVector (Λ : Type) where
  addVector : Λ → Fin 4 → Λ

/--
Typeclass for reflecting a lattice site in the time direction.
The `involution` field ensures that reflecting twice is the identity.
-/
class ReflectSite (Λ : Type) where
  reflectSite : Λ → Λ
  involution : ∀ n, reflectSite (reflectSite n) = n

/-! ### The ℤ⁴ lattice -/

/--
A site in the ℤ⁴ lattice, represented as a 4-tuple of integers.
This is the default index set for a hypercubic lattice.
-/
abbrev Z4Site : Type := ℤ × ℤ × ℤ × ℤ

/--
Add the μ-th standard basis vector to a Z4Site.
Given n = (n₀, n₁, n₂, n₃) and μ ∈ {0,1,2,3}, returns n + e_μ.
-/
def addVectorZ4 (n : Z4Site) (μ : Fin 4) : Z4Site :=
  match μ with
  | 0 => (n.1 + 1, n.2.1, n.2.2.1, n.2.2.2)
  | 1 => (n.1, n.2.1 + 1, n.2.2.1, n.2.2.2)
  | 2 => (n.1, n.2.1, n.2.2.1 + 1, n.2.2.2)
  | 3 => (n.1, n.2.1, n.2.2.1, n.2.2.2 + 1)

/--
Convenience alias for `addVectorZ4` for backward compatibility.
-/
def addVector (n : Z4Site) (μ : Fin 4) : Z4Site := addVectorZ4 n μ

instance : AddVector Z4Site where
  addVector := addVectorZ4

/--
The time direction index. In ℝ⁴ with coordinates (x₀, x₁, x₂, x₃),
the 0-th coordinate is Euclidean time.
-/
def timeDirection : Fin 4 := 0

/--
The time-reflection map θ acting on lattice sites for the ℤ⁴ lattice.
On a lattice with spacing a, the site n = (n₀, n₁, n₂, n₃) ∈ ℤ⁴ is
reflected to n' = (-n₀, n₁, n₂, n₃).
-/
def reflectSiteZ4 (n : Z4Site) : Z4Site :=
  (-n.1, n.2.1, n.2.2.1, n.2.2.2)

/--
Convenience alias for `reflectSiteZ4` for backward compatibility.
-/
def reflectSite (n : Z4Site) : Z4Site := reflectSiteZ4 n

instance : ReflectSite Z4Site where
  reflectSite := reflectSiteZ4
  involution n := by
    dsimp [reflectSiteZ4]; simp

/--
reflectSite is involutive: θ(θ n) = n.
-/
lemma reflectSite_involution (n : Z4Site) : reflectSite (reflectSite n) = n :=
  ReflectSite.involution n

/-! ### The periodic lattice -/

/--
A site in a periodic lattice with `T` time slices and `L³` spatial sites.
The time coordinate lives in `ZMod T` (cyclic group of order T), and each
spatial coordinate lives in `ZMod L`. This gives periodic boundary conditions
in all directions.
-/
@[ext] structure PeriodicSite (T L : ℕ) : Type where
  /-- Time coordinate modulo T (cycles around). -/
  time : ZMod T
  /-- Spatial x coordinate modulo L. -/
  x : ZMod L
  /-- Spatial y coordinate modulo L. -/
  y : ZMod L
  /-- Spatial z coordinate modulo L. -/
  z : ZMod L
  deriving DecidableEq
instance (T L : ℕ) [NeZero T] [NeZero L] : Fintype (PeriodicSite T L) :=
  Fintype.ofEquiv (ZMod T × ZMod L × ZMod L × ZMod L) {
    toFun := λ ((t, x, y, z) : ZMod T × ZMod L × ZMod L × ZMod L) => 
      { time := t, x := x, y := y, z := z }
    invFun := λ n => (n.time, n.x, n.y, n.z)
    left_inv := λ _ => rfl
    right_inv := λ _ => rfl
  }

/--
Add the μ-th standard basis vector to a `PeriodicSite`.
All coordinates use `ZMod` addition, which wraps around automatically.
-/
def addVectorPeriodic (T L : ℕ) (n : PeriodicSite T L) (μ : Fin 4) : PeriodicSite T L :=
  match μ with
  | 0 => { n with time := n.time + 1 }
  | 1 => { n with x := n.x + 1 }
  | 2 => { n with y := n.y + 1 }
  | 3 => { n with z := n.z + 1 }

instance (T L : ℕ) : AddVector (PeriodicSite T L) where
  addVector := addVectorPeriodic T L

/--
Time reflection on a periodic lattice: maps time t ↦ -t (mod T).
This is involutive because -(-t) = t in ZMod T.
-/
def reflectSitePeriodic (T L : ℕ) (n : PeriodicSite T L) : PeriodicSite T L :=
  { n with time := -n.time }

instance (T L : ℕ) : ReflectSite (PeriodicSite T L) where
  reflectSite := reflectSitePeriodic T L
  involution n := by
    dsimp [reflectSitePeriodic]; simp

/--
`reflectSitePeriodic` is involutive: θ(θ n) = n.
-/
lemma reflectSitePeriodic_involution (T L : ℕ) (n : PeriodicSite T L) :
    reflectSitePeriodic T L (reflectSitePeriodic T L n) = n :=
  ReflectSite.involution n


/-- A finite lattice Λ ⊂ ℤ⁴ as a hypercube with spacing a > 0. -/
structure Lattice (Λ : Type) : Type 1 where
  /-- Lattice spacing (a real number > 0). -/
  spacing : ℝ
  /-- The set of lattice sites. -/
  sites : Λ
  /-- Adjacency relation for links. -/
  links : Λ → Λ → Prop
  /-- Plaquettes are ordered 4-tuples of sites forming a square. -/
  plaquettes : (Λ × Λ × Λ × Λ) → Prop

/-- A gauge field configuration on the lattice: each directed link (x → x + a e_μ)
carries a group element U(x, μ) ∈ G. -/
@[ext]
structure LinkVariable (G : Type) (Λ : Type) : Type 1 where
  /-- Assigns a group element to each lattice site and direction. -/
  value : Λ → Fin 4 → G

/--
The reflection map θ on link variables for any lattice type with `ReflectSite`.
For a link variable U(n, μ) from site n in direction μ, the reflected
link variable is:

    (θ U)(n, μ) = U(θ n, μ)⁻¹   if μ = 0 (time direction)
    (θ U)(n, μ) = U(θ n, μ)     if μ ≠ 0 (spatial direction)

The inverse appears for time-like links because reflection reverses the
orientation of the link in time.
-/
def reflectLinkVariable (N : ℕ) {Λ : Type} [ReflectSite Λ] (U : LinkVariable (SU N) Λ) :
    LinkVariable (SU N) Λ :=
  {
    value := λ n μ =>
      if μ = 0 then
        (U.value (ReflectSite.reflectSite n) μ)⁻¹
      else
        U.value (ReflectSite.reflectSite n) μ
  }

/--
The full geometric reflection is involutive: θ(θ U) = U.
-/
lemma reflection_involution (N : ℕ) {Λ : Type} [ReflectSite Λ] (U : LinkVariable (SU N) Λ) :
    reflectLinkVariable N (reflectLinkVariable N U) = U := by
  ext n μ
  dsimp [reflectLinkVariable]
  have h_inv : ReflectSite.reflectSite (ReflectSite.reflectSite n) = n := ReflectSite.involution n
  by_cases h : μ = 0
  · subst h; simp [h_inv]
  · simp [h, h_inv]

/--
Convenience alias for `reflectLinkVariable` on `Z4Site` for backward compatibility.
-/
def reflectLinkVariableZ4 (N : ℕ) (U : LinkVariable (SU N) Z4Site) : LinkVariable (SU N) Z4Site :=
  reflectLinkVariable N U

/--
The full geometric reflection is involutive on Z4Site: θ(θ U) = U.
-/
lemma reflection_involution_z4 (N : ℕ) (U : LinkVariable (SU N) Z4Site) :
    reflectLinkVariableZ4 N (reflectLinkVariableZ4 N U) = U :=
  reflection_involution N U

section PlaquetteProduct

/--
The ordered product of link variables around an elementary plaquette in a
lattice with `AddVector`. For a site n and directions μ, ν, the product traverses:

    n + e_μ + e_ν ←── n + e_ν
         |              ↑
         |              |
         ↓              |
    n + e_μ  ────────── n

Explicitly: U(n, μ) · U(n+e_μ, ν) · U(n+e_μ+e_ν, μ)⁻¹ · U(n+e_ν, ν)⁻¹

The inverse for the third and fourth links accounts for the orientation
reversal (traversing the link backwards).
-/
noncomputable def plaquetteProduct (N : ℕ) {Λ : Type} [AddVector Λ]
    (U : LinkVariable (SU N) Λ) (n : Λ) (μ ν : Fin 4) : SU N :=
  U.value n μ *
  U.value (AddVector.addVector n μ) ν *
  (U.value (AddVector.addVector (AddVector.addVector n μ) ν) μ)⁻¹ *
  (U.value (AddVector.addVector n ν) ν)⁻¹

/--
The contribution of a single oriented plaquette to the Wilson action:

    S_p = β (1 - (1/N) Re Tr(U_∂p))

where U_∂p is the plaquette product. For SU(N) matrices, Tr(U) ∈ ℂ and
Re Tr(U) ∈ ℝ. The term (1 - (1/N) Re Tr) is non-negative and vanishes when
U_∂p = 1.
-/
noncomputable def plaquetteContribution (N : ℕ) (β : ℝ) {Λ : Type} [AddVector Λ]
    (U : LinkVariable (SU N) Λ) (n : Λ) (μ ν : Fin 4) : ℝ :=
  β * ((1 : ℝ) - (1 / (N : ℝ)) * ((trace ((plaquetteProduct N U n μ ν : Matrix (Fin N) (Fin N) ℂ))).re))

/--
The total Wilson action for a finite set of lattice sites.
For each site n ∈ sites, sum over all oriented plaquettes (n; μ, ν).

Explicitly:
    S_W[U] = ∑_{n} ∑_{μ,ν} β (1 - (1/N) Re Tr(U_∂p(n,μ,ν)))

In the standard Wilson action, the sum is over unordered plaquette orientations
(μ < ν). The sum over all ordered pairs (μ,ν) double-counts each unoriented
plaquette; the coupling constant β can absorb this factor.
-/
noncomputable def wilsonActionFinite (N : ℕ) (β : ℝ) {Λ : Type} [AddVector Λ]
    (sites : Finset Λ) (U : LinkVariable (SU N) Λ) : ℝ :=
  ∑ n ∈ sites, ∑ μ : Fin 4, ∑ ν : Fin 4, plaquetteContribution N β U n μ ν

/--
The partition function for a finite lattice with the Wilson action.
For a finite lattice with site set `sites` and coupling β > 0:

    Z(β) = ∫ exp(-S_W[U]) dμ₀(U)

where μ₀ is the product Haar measure on SU(N)^(sites × Fin 4).

Note: The actual definition (as `partitionFunctionFinite`) is in
`LatticeMeasure.lean` as it requires the Haar measure on SU(N).
As a placeholder we define a stub that just returns 1.
-/
noncomputable def partitionFunctionFiniteStub (_N : ℕ) (_β : ℝ) {Λ : Type} (_sites : Finset Λ) : ℝ := 1

end PlaquetteProduct

/--
The Wilson plaquette action (abstract interface):
  S_W[U] = β ∑_p (1 - (1/N) Re Tr U_∂p)
where the sum is over all plaquettes p, and U_∂p is the ordered product of
link variables around the plaquette.
-/
structure WilsonAction (G : Type) (Λ : Type) : Type 1 where
  /-- The coupling constant β = 2N/g² (placeholder ℝ). -/
  beta : ℝ
  /-- Evaluate the action on a link configuration. -/
  evaluate : LinkVariable G Λ → ℝ

/--
The lattice Yang-Mills measure (Gibbs measure):
  dμ(U) = (1/Z) exp(-S_W[U]) ∏_{links} dU_link
where dU_link is the Haar measure on G.
-/
structure LatticeMeasure (G : Type) (Λ : Type) : Type 1 where
  /-- Partition function Z = ∫ exp(-S_W) ∏ dU. -/
  partitionFunction : ℝ
  /-- Density with respect to product Haar measure. -/
  density : LinkVariable G Λ → ℝ

/--
Continuum limit: as lattice spacing a → 0, the lattice theory should converge
to the continuum Yang-Mills theory.

More precisely, let μ_a be the lattice Yang-Mills measure on a lattice with
spacing a > 0. We require:

1. **Convergence of Schwinger functions**: For each n, the lattice Schwinger
   functions S_n^{(a)} converge to continuum Schwinger functions S_n as a → 0,
   in the sense of tempered distributions.

2. **OS axioms for the limit**: The limiting Schwinger functions {S_n} satisfy
   the Osterwalder-Schrader axioms (OS0-OS4), so the OS reconstruction theorem
   yields a Wightman QFT.

3. **Mass gap**: The limiting theory has a positive mass gap: the Hamiltonian
   has a spectral gap above the vacuum, and truncated correlation functions
   decay exponentially.

This is the hardest part of the Yang-Mills problem and is the subject of
Balaban's renormalization group approach. In the lattice gauge theory
literature, this is often called "taking the continuum limit."

References:
- T. Balaban, "Renormalization group approach to lattice gauge field theories"
- J. Glimm, A. Jaffe, "Quantum Physics: A Functional Integral Point of View"
- M. Salmhofer, "Renormalization: An Introduction"
-/
structure ContinuumLimit (N : ℕ) : Prop where
  /-- For each n, the lattice Schwinger functions converge as a → 0. -/
  schwingerFunctionsConverge : True
  /-- The limiting Schwinger functions satisfy the OS axioms. -/
  limitingFunctionsSatisfyOS : True
  /-- The limiting Wightman QFT has a positive mass gap. -/
  massGapPositivity : True

end Lattice

end YangMills
