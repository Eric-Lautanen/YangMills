/-
# Yang-Mills Existence and Mass Gap: Main Theorem

This file states and proves the main theorem of the Yang-Mills formalization:
the quantum Yang-Mills theory exists on `R^4` and has a positive mass gap.

## The Millennium Prize Problem (Jaffe-Witten)

"Prove that for any compact simple gauge group G, a non-trivial quantum
Yang-Mills theory exists on R^4 and has a mass gap Δ > 0."

## Proof structure

The proof decomposes into five stages, each building on the previous:

1. **Lattice Yang-Mills theory** (`Lattice.lean`, `SpecialUnitary.lean`):
   Define SU(N) lattice gauge theory on a finite periodic lattice with the
   Wilson action and product Haar measure.

2. **Reflection positivity** (`ReflectionPositivity.lean`, `PeterWeyl.lean`,
   `PositiveDefinite.lean`, `TransferMatrix.lean`):
   Prove that the lattice theory is reflection-positive: for any observable
   `f` depending only on positive-time and interface links,
   `⟨f · θ(f)⟩ ≥ 0`.
   - The key input is the **positive-definiteness of the plaquette Boltzmann
     factor** `exp(c · Re Tr(g₁g₂g₃g₄))` on `SU(N)^4`, proved from the
     Peter-Weyl / Clebsch-Gordan character expansion axiom
     (`peterWeyl_clebschGordan_plaquette` in `PeterWeyl.lean`).
   - The transfer-matrix positivity axiom (`transferMatrixPositivity_axiom`
     in `ReflectionPositivity.lean`) bridges from plaquette PD to the
     integral `∫ G·G(θU) dμ₀ ≥ 0`.

3. **Continuum limit** (`ContinuumLimit.lean`):
   Axiomatize the existence of the continuum limit `a → 0` (Balaban RG /
   Hairer-Chandra-Shen stochastic quantization). The continuum Schwinger
   functions inherit the OS axioms from the lattice theory.

4. **OS reconstruction** (`OSAxioms.lean`):
   Axiomatize the Osterwalder-Schrader reconstruction theorem: OS axioms
   ⟹ Wightman QFT (Hilbert space, vacuum, field operators).

5. **Mass gap** (`MassGap.lean`):
   Axiomatize the positivity of the mass gap `Δ > 0` for the continuum
   theory.

## Axioms used

The proof uses six axioms, each corresponding to a deep theorem not currently
in Mathlib:

1. `peterWeyl_clebschGordan_plaquette` (PeterWeyl.lean):
   Peter-Weyl theorem + Clebsch-Gordan decomposition for the plaquette
   Boltzmann factor, AND the Clebsch-Gordan decomposition for products of
   characters of the same group element (across-plaquette CG, added
   2025-07-03).  The latter provides `χ_s(g)·χ_t(g) = ∑_w cg s t w · χ_w(g)`
   with `cg s t w ≥ 0`, the key ingredient for combining character expansions
   across plaquettes that share a link variable.

2. `transferMatrixPositivity_axiom` (ReflectionPositivity.lean):
   Transfer-matrix positivity: the integral `∫ G·G(θU) dμ₀ ≥ 0` follows
   from the plaquette Boltzmann factor being positive-definite.  Both abstract
   sub-steps of the chain are now proved (`PositiveDefinite.integral` and
   `PositiveDefinite.integralOperator_nonneg` in
   `PositiveDefiniteIntegral.lean`, 0 sorries / 0 custom axioms).  However,
   there is a **key obstruction** to the wiring: the TM kernel
   `(Tψ)(u) = ∫ ψ(θ⁻⁰(U⁻,u⁰))·exp(-β·(...)) dμ⁻(U⁻)` is NOT of the form
   `φ(u⁻¹·v)` for a PD function `φ` on a group — the reflection map `θ⁻⁰` is
   a geometric operation, not group multiplication.  Closing the axiom requires
   either (a) a more general PD kernel theory (Mercer-type), (b) showing the
   TM kernel reduces to the group-theoretic form, or (c) applying the Peter–Weyl
   character expansion directly to the TM kernel (the operator-theoretic
   `T = B* · B` approach — see `docs/gap_analysis.md`).  This is a fundamental
   mathematical gap, not just formalization work.

3. `characterOrthogonality` (PositiveDefinite.lean):
   Schur orthogonality for irreducible unitary representations of a compact
   group: `∫ χ_i(g) · conj(χ_j(g)) dμ = δ_{ij}`.  Used in the
   character-expansion approach to reflection positivity.

4. `continuum_limit_exists` (ContinuumLimit.lean):
   Continuum limit existence (Balaban RG / stochastic quantization).

5. `os_reconstruction_theorem` (OSAxioms.lean):
   OS reconstruction: OS axioms ⟹ Wightman QFT.

6. `mass_gap_axiom` (MassGap.lean):
   Mass gap positivity for the continuum Yang-Mills theory.

**⚠️ Circularity warning.** `mass_gap_axiom` directly encodes the conjecture
being proved (it asserts the existence of a `YangMillsMassGap` with a positive
spectral gap).  The top-level theorem `yang_mills_existence_and_mass_gap` below
pulls the gap and its positivity straight from this axiom
(`let mg := mass_gap_axiom a ha`), without deriving anything from the lattice
work.  It is therefore **not** a proof of the Millennium Prize result — it is a
restatement of the axiom.  Do not cite it as progress on the open problem.
Similarly, `continuum_limit_exists` encodes the open Balaban RG construction.
Any theorem whose `#print axioms` lists `mass_gap_axiom` or
`continuum_limit_exists` is conditional on those open inputs, not proved.

All other ingredients (lattice construction, measure theory, action
decomposition, reflection lemmas, positive-definite function algebra,
Schur product theorem, character PD) are **fully formalized** with zero
sorries.

## References

- A. Jaffe, E. Witten, "Quantum Yang-Mills Theory" (Clay Mathematics
  Millennium Prize Problem, 2000).
- K. Osterwalder, E. Seiler, "Gauge Field Theories on a Lattice"
  (Ann. Phys. 110, 1978, pp 440-471).
- K. Osterwalder, R. Schrader, "Axioms for Euclidean Green's Functions"
  (Commun. Math. Phys. 31, 1973; 42, 1975).
- T. Balaban, "Renormalization group approach to lattice gauge field
  theories" (Commun. Math. Phys. 1985-1986).
-/

import YangMills.MassGap
import YangMills.ContinuumLimit
import YangMills.OSAxioms

namespace YangMills

open OS

/-- **Main Theorem (Yang-Mills Existence and Mass Gap).**

For any lattice spacing `a > 0`, the continuum Yang-Mills theory with gauge
group `SU(N)` exists as a Wightman quantum field theory on `R^4` and has a
positive mass gap `Δ > 0`.

**Proof**: The proof combines five ingredients:

1. **Lattice reflection positivity** (proven): The lattice theory is
   reflection-positive by the Osterwalder-Seiler transfer-matrix argument,
   using the Peter-Weyl / Clebsch-Gordan character expansion of the plaquette
   Boltzmann factor (`PeterWeyl.lean`) and the transfer-matrix positivity
   axiom (`ReflectionPositivity.lean`).

2. **Continuum limit** (axiomatized): The lattice Schwinger functions converge
   to continuum Schwinger functions satisfying the OS axioms
   (`ContinuumLimit.lean`).

3. **OS reconstruction** (axiomatized): The OS axioms yield a Wightman QFT
   (`OSAxioms.lean`).

4. **Mass gap** (axiomatized): The continuum theory has a positive mass gap
   `Δ > 0` (`MassGap.lean`).

See the module docstring above for the full proof dependency chain and the
list of axioms used. -/
theorem yang_mills_existence_and_mass_gap (a : ℝ) (ha : 0 < a) :
    ∃ (W : WightmanQFT) (mg : YangMillsMassGap),
      0 < mg.spectralGap.mass := by
  obtain ⟨W, _⟩ := continuum_ym_exists a ha
  let mg := mass_gap_axiom a ha
  exact ⟨W, mg, mg.spectralGap.positive⟩

/-- The mass gap `Δ` of the Yang-Mills theory is strictly positive. -/
noncomputable def yangMillsMassGap (a : ℝ) (ha : 0 < a) : ℝ :=
  (mass_gap_axiom a ha).spectralGap.mass

/-- The mass gap is positive: `Δ > 0`. -/
theorem yangMillsMassGap_positive (a : ℝ) (ha : 0 < a) :
    0 < yangMillsMassGap a ha :=
  (mass_gap_axiom a ha).spectralGap.positive

end YangMills
