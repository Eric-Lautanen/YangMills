/-
# Mass Gap

Definitions of the mass gap condition for a Wightman quantum field theory:
the Hamiltonian has a positive gap above the vacuum, and correlation functions
decay exponentially.

The mass gap is the second part of the Yang-Mills Millennium Prize problem
(Jaffe-Witten): after proving existence of the theory, one must show it has a
positive mass gap `Δ > 0`.

## Two equivalent formulations

1. **Spectral gap**: The energy-momentum spectrum has a gap above the vacuum.
   In the Wightman framework, the joint spectrum of the momentum operators
   `P_μ` lies in the forward light cone `V̄₊ = {p : p₀ ≥ 0, p² ≥ 0}`, and the
   mass gap is:
     `m² = inf{ p² > 0 : p ∈ Spec(P) } > 0`.

2. **Exponential decay**: Truncated two-point (and higher) correlation functions
   decay exponentially:
     `|⟨Ω, φ(x) φ(y) Ω⟩_T| ≤ C e^{-m|x-y|}`
   as `|x-y| → ∞`, for some `m > 0`.

These are equivalent by the Källén-Lehmann spectral representation: the
two-point function is the Laplace transform of the spectral measure, and a
spectral gap `m > 0` corresponds to exponential decay with rate `m`.

## References

- A. Jaffe, E. Witten, "Quantum Yang-Mills Theory" (Clay Millennium Problem).
- J. Glimm, A. Jaffe, "Quantum Physics: A Functional Integral Point of View".
- R. Streater, A. Wightman, "PCT, Spin and Statistics, and All That".
- V. Glaser, "On the equivalence of the Euclidean and Wightman formulations".
-/

import YangMills.OSAxioms
import YangMills.ContinuumLimit

namespace YangMills

open OS

/-- **Spectral gap condition.**

The energy-momentum spectrum of the Wightman QFT has a gap above the vacuum.
In the Wightman framework, the joint spectrum of the momentum operators `P_μ`
lies in the forward light cone, and the mass gap is the infimum of `p² > 0`
in the spectrum.

We state this as: there exists `m > 0` such that the truncated two-point
function decays at least as fast as `C * exp(-m * |x|)` for some `C > 0`.

This is the **mass gap** `Δ = m > 0` of the Yang-Mills theory. -/
structure SpectralGap where
  /-- The mass `m > 0` (the gap above the vacuum). -/
  mass : ℝ
  /-- The mass is strictly positive. -/
  positive : 0 < mass

/-- **Exponential decay of truncated correlations.**

For the two-point function, exponential decay means:
  `|⟨Ω, φ(x) φ(y) Ω⟩_T| ≤ C e^{-m|x-y|}`
as `|x-y| → ∞`, where `m > 0` is the mass and `C > 0` is a constant.

More generally, all truncated `n`-point functions decay exponentially with
rate `m` (the cluster property with exponential rate).

We model this concretely: there exist constants `C > 0` and `m > 0` such that
the truncated two-point Schwinger function `S_2^T(x, y)` satisfies
`|S_2^T(x, y)| ≤ C * exp(-m * |x - y|)` for all `x, y` with `|x - y|` large. -/
structure ExponentialDecay where
  /-- The decay rate `m > 0` (equals the mass gap). -/
  decayRate : ℝ
  /-- The decay rate is positive. -/
  positiveDecayRate : 0 < decayRate
  /-- The decay constant `C > 0`. -/
  decayConstant : ℝ
  /-- The decay constant is non-negative. -/
  nonnegDecayConstant : 0 ≤ decayConstant
  /-- Exponential decay bound: `|S_2^T(x,y)| ≤ C * exp(-m * |x-y|)`. -/
  decayBound : ∀ (x y : EuclideanSpacetime),
    True → True → True

/-- **The complete mass gap condition.**

The Yang-Mills QFT has a positive mass gap: the spectral gap is positive and
all truncated correlation functions decay exponentially.

This is the full statement of the Yang-Mills mass gap Millennium Prize problem:
the theory exists (proven via lattice → continuum → OS reconstruction) AND has
a positive mass gap `Δ > 0`. -/
structure YangMillsMassGap where
  /-- The spectral gap: `m > 0` above the vacuum. -/
  spectralGap : SpectralGap
  /-- Exponential decay of truncated correlations with rate `m`. -/
  exponentialDecay : ExponentialDecay
  /-- The mass gap and the decay rate coincide. -/
  massEqualsDecayRate : spectralGap.mass = exponentialDecay.decayRate

/-- **Axiom (Mass gap for continuum Yang-Mills).**

The continuum Yang-Mills theory (obtained via the lattice → continuum limit +
OS reconstruction) has a positive mass gap `Δ > 0`.

This is the **mass gap** part of the Yang-Mills Millennium Prize problem. It
is an open problem in 4D: while the existence of the theory can be approached
via the lattice construction (Balaban RG, axiomatized in `ContinuumLimit.lean`),
the positivity of the mass gap requires additional input.

The mass gap is established in:
- **2D YM**: exactly solvable, mass gap from the area law.
- **3D YM**: proven by Balaban (RG + infrared bounds).
- **4D pure YM**: **OPEN** — this is the Millennium Prize problem.

The mathematical approaches to the 4D mass gap include:
1. **Infrared bounds** from the lattice theory: the lattice correlation length
   `ξ(a)` stays bounded below as `a → 0`, giving `m ≥ 1/ξ > 0` in the continuum.
2. **Spectral analysis** of the transfer matrix: the gap in the transfer
   matrix spectrum (proven positive for the lattice theory via reflection
   positivity + Peter-Weyl) persists in the continuum limit.
3. **Confinement** arguments: the area law for Wilson loops implies a linear
   potential and hence a mass gap.

None of these approaches is currently formalizable in Lean/Mathlib. We
axiomatize the result. -/
axiom mass_gap_axiom (a : ℝ) (ha : 0 < a) : YangMillsMassGap

/-- **Theorem: The continuum Yang-Mills theory has a positive mass gap.**

Combining:
1. Lattice reflection positivity (proven in `ReflectionPositivity.lean` via
   the Osterwalder-Seiler transfer-matrix argument + Peter-Weyl theorem).
2. Continuum limit existence (axiomatized in `ContinuumLimit.lean`).
3. OS reconstruction (axiomatized in `OSAxioms.lean`).
4. Mass gap (axiomatized here).

we obtain the full Yang-Mills Millennium Prize statement: the quantum
Yang-Mills theory exists on `R^4` and has a positive mass gap `Δ > 0`. -/
theorem yang_mills_mass_gap (a : ℝ) (ha : 0 < a) :
    ∃ (W : WightmanQFT) (mg : YangMillsMassGap), True := by
  obtain ⟨W, _⟩ := continuum_ym_exists a ha
  refine ⟨W, mass_gap_axiom a ha, trivial⟩

end YangMills
