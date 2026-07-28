/-
# Positive-Definiteness of the Full Boltzmann Factor

This file promotes the single-plaquette positive-definiteness result
`plaquetteBoltzmannPD_inv` (in `PeterWeyl.lean`) to positive-definiteness of the
plaquette Boltzmann factor as a function on the **full link-variable group**
`LinkVariable (SU N) Λ`.

The key ingredients are:
* `LinkVariable (SU N) Λ` is a group under pointwise multiplication (the product
  group `SU(N)^{Λ × Fin 4}`), via the `Group` instance in `Lattice.lean`.
* `PositiveDefinite.comp_hom` (in `PositiveDefinite.lean`): PD is preserved by
  group homomorphisms.
* `plaquetteBoltzmannPD_inv` (in `PeterWeyl.lean`): the plaquette Boltzmann
  factor with inverse links `exp(c · Re Tr(g₁ g₂ g₃⁻¹ g₄⁻¹))` is PD on
  `SU(N)⁴` (modulo the Peter–Weyl axiom).

The projection homomorphism `plaquetteProjection` extracts the four link
variables around a plaquette from the full link configuration.  Composing
`plaquetteBoltzmannPD_inv` with this projection (via `comp_hom`) gives PD of the
plaquette factor on the full link group.

See `docs/gap_analysis.md` for the status of the full transfer-matrix positivity
wiring.
-/

import YangMills.Lattice
import YangMills.Proofs.PeterWeyl

open Matrix

open scoped ComplexConjugate

namespace YangMills

variable {Λ : Type} [Lattice.AddVector Λ]

/-- The projection homomorphism from the full link-variable group to the four
link variables around a plaquette `(n, μ, ν)`.

The plaquette product is
`U(n,μ) · U(n+e_μ,ν) · U(n+e_μ+e_ν,μ)⁻¹ · U(n+e_ν,ν)⁻¹`,
with inverses on the 3rd and 4th links (orientation reversal).  The projection
extracts the **raw** link values (without inversion); the inverses are applied
inside `plaquetteBoltzmannPD_inv`.

This is a group homomorphism because the group operation on `LinkVariable` is
pointwise, and the group operation on `SU(N)⁴` is componentwise. -/
noncomputable def plaquetteProjection (N : ℕ)
    (n : Λ) (μ ν : Fin 4) :
    Lattice.LinkVariable (SU N) Λ →* ((SU N × SU N) × SU N) × SU N where
  toFun U :=
    ⟨⟨⟨U.value n μ, U.value (Lattice.AddVector.addVector n μ) ν⟩,
        U.value (Lattice.AddVector.addVector (Lattice.AddVector.addVector n μ) ν) μ⟩,
      U.value (Lattice.AddVector.addVector n ν) ν⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The plaquette Boltzmann factor `exp((β/N) · Re Tr(U_∂p))` is
positive-definite on the full link-variable group `LinkVariable (SU N) Λ`.

This is the key promotion step: `plaquetteBoltzmannPD_inv` proves PD on the
four-link product group `SU(N)⁴`, and `PositiveDefinite.comp_hom` with the
projection `plaquetteProjection` promotes it to PD on the full link group.

**Requires** `N ≥ 1` (so `β/N ≥ 0` when `β ≥ 0`) and the Peter–Weyl /
Clebsch–Gordan axiom `peterWeyl_clebschGordan_plaquette`. -/
theorem plaquetteFactorPD (N : ℕ)
    (_hN : 1 ≤ N) (β : ℝ) (hβ : 0 ≤ β)
    (n : Λ) (μ ν : Fin 4) :
    PositiveDefinite
      (fun (U : Lattice.LinkVariable (SU N) Λ) =>
        (Real.exp ((β / (N : ℝ)) *
          (Matrix.trace ((Lattice.plaquetteProduct N U n μ ν : SU N) :
            Matrix (Fin N) (Fin N) ℂ)).re) : ℂ)) := by
  -- The plaquette factor is plaquetteBoltzmannPD_inv composed with the projection.
  have hc : 0 ≤ β / (N : ℝ) := by
    apply div_nonneg hβ
    exact Nat.cast_nonneg _
  have hPD := plaquetteBoltzmannPD_inv N (β / (N : ℝ)) hc
  -- Compose with the projection homomorphism.
  have hcomp := PositiveDefinite.comp_hom (plaquetteProjection N n μ ν) hPD
  -- Show the composition equals the plaquette factor.
  convert hcomp using 1
  ext U
  simp only [plaquetteProjection, Lattice.plaquetteProduct, MonoidHom.coe_mk]
  rfl

/-- The full plaquette contribution `exp(-S_p) = exp(-β) · exp((β/N) · Re Tr(U_∂p))`
is positive-definite on the full link-variable group.

This combines `plaquetteFactorPD` with the constant factor `exp(-β)` (a
non-negative scalar, so `PositiveDefinite.smul_nonneg` applies). -/
theorem plaquetteContributionPD (N : ℕ)
    (hN : 1 ≤ N) (β : ℝ) (hβ : 0 ≤ β)
    (n : Λ) (μ ν : Fin 4) :
    PositiveDefinite
      (fun (U : Lattice.LinkVariable (SU N) Λ) =>
        (Real.exp (-Lattice.plaquetteContribution N β U n μ ν) : ℂ)) := by
  -- exp(-S_p) = exp(-β) · exp((β/N) · Re Tr(U_∂p))
  have hexp_neg_β : 0 ≤ Real.exp (-β) := Real.exp_pos _ |>.le
  have hfactor := plaquetteFactorPD N hN β hβ n μ ν
  -- The constant exp(-β) times the PD plaquette factor is PD.
  have hsmul := PositiveDefinite.smul_nonneg hexp_neg_β hfactor
  -- Show exp(-S_p) = exp(-β) · exp((β/N) · Re Tr(U_∂p))
  convert hsmul using 1
  ext U
  simp only [Lattice.plaquetteContribution]
  -- Split the exponent: -(β·(1 - (1/N)·Re Tr)) = -β + (β/N)·Re Tr
  rw [show -(β * ((1 : ℝ) - (1 / (N : ℝ)) *
            (Matrix.trace ((Lattice.plaquetteProduct N U n μ ν : Matrix (Fin N) (Fin N) ℂ))).re)) =
          (-β) + (β / (N : ℝ)) *
            (Matrix.trace ((Lattice.plaquetteProduct N U n μ ν : Matrix (Fin N) (Fin N) ℂ))).re
        by ring]
  rw [Real.exp_add]
  push_cast
  rfl

/-- The full Boltzmann factor `exp(-S_W)` is positive-definite on the full
link-variable group `LinkVariable (SU N) Λ`.

The Wilson action is a sum of plaquette contributions,
`S_W = ∑_{n,μ,ν} S_p(n,μ,ν)`, so the Boltzmann factor factorises as a product
`exp(-S_W) = ∏_{n,μ,ν} exp(-S_p(n,μ,ν))`.  Each factor is PD on the full link
group by `plaquetteContributionPD`, and a finite product of PD functions on the
same group is PD by `PositiveDefinite.finprod` (the n-ary Schur product
theorem).

**Requires** `N ≥ 1`, `β ≥ 0`, and the Peter–Weyl / Clebsch–Gordan axiom
`peterWeyl_clebschGordan_plaquette` (via `plaquetteContributionPD`). -/
theorem boltzmannFactorPD (N : ℕ)
    (hN : 1 ≤ N) (β : ℝ) (hβ : 0 ≤ β)
    (sites : Finset Λ) :
    PositiveDefinite
      (fun (U : Lattice.LinkVariable (SU N) Λ) =>
        (Real.exp (-Lattice.wilsonActionFinite N β sites U) : ℂ)) := by
  -- The Boltzmann factor is a finite product of plaquette contributions,
  -- indexed by (site, μ, ν) with n ∈ sites and μ, ν ∈ Fin 4.
  have hprod := PositiveDefinite.finprod
    ((sites ×ˢ Finset.univ) ×ˢ (Finset.univ : Finset (Fin 4)))
    (fun p U => Real.exp (-Lattice.plaquetteContribution N β U p.1.1 p.1.2 p.2))
    (fun p _ => plaquetteContributionPD N hN β hβ p.1.1 p.1.2 p.2)
  convert hprod using 1
  ext U
  simp only [Lattice.wilsonActionFinite]
  rw [Finset.prod_product, Finset.prod_product]
  -- Prove the ℝ-level equality, then cast to ℂ.
  have hR : Real.exp (-(∑ n ∈ sites, ∑ μ : Fin 4, ∑ ν : Fin 4,
      Lattice.plaquetteContribution N β U n μ ν)) =
    ∏ n ∈ sites, ∏ μ : Fin 4, ∏ ν : Fin 4,
      Real.exp (-(Lattice.plaquetteContribution N β U n μ ν)) := by
    simp only [← Finset.sum_neg_distrib, Real.exp_sum]
  exact_mod_cast hR
