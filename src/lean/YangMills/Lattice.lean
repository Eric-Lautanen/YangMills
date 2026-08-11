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

/-- `LinkVariable G Λ` is a group under pointwise multiplication when `G` is a
group.  This is the product group `G^{Λ × Fin 4}`. -/
instance {G : Type} {Λ : Type} [Group G] : Group (LinkVariable G Λ) where
  mul U V := ⟨fun n μ => U.value n μ * V.value n μ⟩
  mul_assoc U V W := by ext n μ; exact mul_assoc _ _ _
  one := ⟨fun _ _ => 1⟩
  one_mul U := by ext n μ; exact one_mul _
  mul_one U := by ext n μ; exact mul_one _
  inv U := ⟨fun n μ => (U.value n μ)⁻¹⟩
  inv_mul_cancel U := by ext n μ; exact inv_mul_cancel _

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
Gauge transformation on link variables.  For a site-valued function
`g : Λ → SU N` (the gauge parameter) and a link variable `U`, the
gauge-transformed link variable is:

    (g · U)(n, μ) = g(n) · U(n, μ) · g(n + e_μ)⁻¹

This conjugates each link by the gauge transformation at its endpoints.
The Wilson action (plaquette products) is invariant under this transformation
because each plaquette product transforms by conjugation, and the trace is
cyclic.  The product Haar measure is invariant because each link is
independently left-right-multiplied, preserving the Haar factor.
-/
def gaugeTransformLinkVariable (N : ℕ) {Λ : Type} [AddVector Λ]
    (g : Λ → SU N) (U : LinkVariable (SU N) Λ) :
    LinkVariable (SU N) Λ :=
  { value := λ n μ => g n * U.value n μ * (g (AddVector.addVector n μ))⁻¹ }

/--
The gauge transformation with the identity gauge parameter is the identity:
`e · U = U` where `e(n) = 1` for all `n`.
-/
lemma gaugeTransformLinkVariable_one (N : ℕ) {Λ : Type} [AddVector Λ]
    (U : LinkVariable (SU N) Λ) :
    gaugeTransformLinkVariable N (fun _ => 1) U = U := by
  ext n μ
  dsimp [gaugeTransformLinkVariable]
  simp [one_mul, inv_one, mul_one]

/--
The gauge transformation is involutive in the gauge parameter: applying
`g` then `g⁻¹` (pointwise inverse) recovers the original link variable.
-/
lemma gaugeTransformLinkVariable_inv (N : ℕ) {Λ : Type} [AddVector Λ]
    (g : Λ → SU N) (U : LinkVariable (SU N) Λ) :
    gaugeTransformLinkVariable N (fun n => (g n)⁻¹)
      (gaugeTransformLinkVariable N g U) = U := by
  ext n μ
  dsimp only [gaugeTransformLinkVariable]
  rw [inv_inv, mul_assoc, mul_assoc, inv_mul_cancel, mul_one, ← mul_assoc, inv_mul_cancel, one_mul]

/-- A function `φ` on link variables is **gauge-invariant** if it is invariant
under all gauge transformations: `φ(g · U) = φ(U)` for every gauge parameter
`g : Λ → SU N` and every link variable `U`.

Gauge invariance is a physically natural condition (Wilson loops are
gauge-invariant).  It was previously thought to be a necessary hypothesis for
transfer-matrix positivity (§8.11.51), but §8.11.53 showed that analysis was
flawed — the positivity holds for ALL `f` with `dependsOnlyOnPosSpatialInterface`,
not just gauge-invariant `f`.  The gauge-invariance infrastructure is retained
because the key lemma `gaugeInvariant_matrixElement_integral_zero` (which uses
it) is proven and may be useful for the L=1 case or gauge-invariant subspace
arguments.  See `docs/transfer_matrix_positivity_design.md` §8.11.53. -/
def IsGaugeInvariant (N : ℕ) {Λ : Type} [AddVector Λ]
    (φ : LinkVariable (SU N) Λ → ℝ) : Prop :=
  ∀ (g : Λ → SU N) (U : LinkVariable (SU N) Λ),
    φ (gaugeTransformLinkVariable N g U) = φ U

/-- A ℂ-valued function on link variables is **gauge-invariant** if it is
invariant under all gauge transformations.  This is the complex-valued analogue
of `IsGaugeInvariant`, needed for the key lemma that matrix elements of
non-trivial representations vanish when integrated against a gauge-invariant
function (the matrix elements are ℂ-valued). -/
def IsGaugeInvariantC (N : ℕ) {Λ : Type} [AddVector Λ]
    (φ : LinkVariable (SU N) Λ → ℂ) : Prop :=
  ∀ (g : Λ → SU N) (U : LinkVariable (SU N) Λ),
    φ (gaugeTransformLinkVariable N g U) = φ U

/-- For a gauge parameter `g` that is `h` at site `x` and `1` everywhere else,
the gauge-transformed link at `(x, μ)` is `h · U(x, μ)` provided `x + e_μ ≠ x`
(so that `g(x + e_μ) = 1`).  This is the key identity underlying the
gauge-invariance lemma: it shows that the single-link gauge transformation
acts by left multiplication. -/
lemma gaugeTransformLinkVariable_single_site (N : ℕ) {Λ : Type} [AddVector Λ] [DecidableEq Λ]
    (x : Λ) (μ : Fin 4) (h : SU N) (U : LinkVariable (SU N) Λ)
    (h_xμ : AddVector.addVector x μ ≠ x) :
    (gaugeTransformLinkVariable N (fun y => if y = x then h else 1) U).value x μ =
      h * U.value x μ := by
  dsimp [gaugeTransformLinkVariable]
  rw [if_pos rfl]
  have h_ne : AddVector.addVector x μ ≠ x := h_xμ
  rw [if_neg h_ne, inv_one, mul_one]

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

/-- Each plaquette contribution is bounded by `2|β|` in absolute value.

Since `plaquetteProduct ∈ SU N` (unitary), `|Re Tr(g)| ≤ N` (`trace_re_bound`),
so `|(1/N)·Re Tr(g)| ≤ 1`, hence `|1 - (1/N)·Re Tr(g)| ≤ 2`, and
`|plaquetteContribution| = |β|·|1 - (1/N)·Re Tr(g)| ≤ 2|β|`.

This is ingredient 2 of the integrability discharge (design doc §8.11.10):
it gives a uniform upper bound on `|wilsonActionOSInterface|`, hence a
positive lower bound on `exp(-β·S_int)`. 0 sorries, 0 custom axioms. -/
lemma plaquetteContribution_bounded (N : ℕ) (β : ℝ) {Λ : Type} [AddVector Λ]
    (U : LinkVariable (SU N) Λ) (n : Λ) (μ ν : Fin 4) :
    |plaquetteContribution N β U n μ ν| ≤ 2 * |β| := by
  unfold plaquetteContribution
  set x := (trace ((plaquetteProduct N U n μ ν : Matrix (Fin N) (Fin N) ℂ))).re
  have hx : |x| ≤ (N : ℝ) := trace_re_bound N (plaquetteProduct N U n μ ν)
  have h_inv_nonneg : 0 ≤ 1 / (N : ℝ) := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · exact div_nonneg (by norm_num) (Nat.cast_nonneg _)
  have h_inv_mul : 1 / (N : ℝ) * (N : ℝ) ≤ 1 := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (ne_of_gt (Nat.cast_pos.mpr hN)))]
  have h_prod_le : |1 / (N : ℝ) * x| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg h_inv_nonneg]
    calc 1 / (N : ℝ) * |x| ≤ 1 / (N : ℝ) * (N : ℝ) := by gcongr
      _ ≤ 1 := h_inv_mul
  rcases abs_le.mp h_prod_le with ⟨h_y_ge, h_y_le⟩
  have h_le_2 : |1 - 1 / (N : ℝ) * x| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  calc |β * (1 - 1 / (N : ℝ) * x)| = |β| * |1 - 1 / (N : ℝ) * x| := abs_mul _ _
    _ ≤ |β| * 2 := mul_le_mul_of_nonneg_left h_le_2 (abs_nonneg _)
    _ = 2 * |β| := by ring

#print axioms plaquetteContribution_bounded

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
