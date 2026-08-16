/-
# Reflection Positivity: Character Expansion
-/

import YangMills.Proofs.ReflectionPositivity.PlaquetteStructure

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open scoped BigOperators
open MeasureTheory
open Complex
open scoped ComplexConjugate

namespace YangMills
namespace Lattice
/-! ### Step 3: Interface link integral gives δ_{w, trivial}

This is Step 3 of the §8.11.61 plan.  Integrating the interface character factor
`∏_{l ∈ allLinkInt} χ_{w(l)}(U.value l)` over the interface links (with the product
Haar measure) gives `∏_l (if w(l) = σ_0 then 1 else 0)`, i.e. `δ_{w|_int, trivial}`.
This is character orthogonality for the product Haar measure: each interface link
integral `∫ χ_{w(l)}(g) dμ(g) = δ_{w(l), σ_0}` by `integral_repCharacter_trivial`,
and the product measure factors by Fubini (`integral_fintype_prod_eq_prod`).

The key point: with `dependsOnlyOnPositive`, `f` does NOT depend on interface links,
so the interface integral is UNWEIGHTED character orthogonality (no `f` factor).
This is why `dependsOnlyOnPositive` (not the weaker `dependsOnlyOnPosSpatialInterface`)
is needed — see §8.11.61.

Uses `integral_prod_repCharacter_trivial` (PeterWeyl.lean:2435).  Standard axioms
only (propext, Classical.choice, Quot.sound); 0 sorries, 0 custom axioms. -/

lemma interface_char_integral_trivial
    (N T L : ℕ) [NeZero T] [NeZero L]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ) (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (σ_0 : ι) (hσ_0_dims : dims σ_0 = 1) (hσ_0_trivial : ∀ g, (ρ σ_0 g) = 1)
    (w : (PeriodicSite T L × Fin 4) → ι) :
    ∫ (cfg : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)),
      ∏ (l : FiniteLinkIndex (PeriodicSite T L) (interfaceSites T L)),
        repCharacter (ρ (w l.val)) (cfg l)
      ∂ (productHaarMeasure N (PeriodicSite T L) (interfaceSites T L)) =
      ∏ (l : FiniteLinkIndex (PeriodicSite T L) (interfaceSites T L)),
        (if w l.val = σ_0 then (1 : ℂ) else 0) := by
  classical
  -- The Haar measure on SU N (same K as in productHaarMeasure).
  let K : TopologicalSpace.PositiveCompacts (SU N) :=
    ⟨⟨Set.univ, isCompact_univ⟩, by simpa using Set.univ_nonempty (α := SU N)⟩
  set μ : MeasureTheory.Measure (SU N) := MeasureTheory.Measure.haarMeasure K with hμ_def
  -- μ is a probability measure (normalized Haar measure on compact SU N).
  haveI : MeasureTheory.IsProbabilityMeasure μ := by
    constructor
    rw [hμ_def]
    simpa [K] using MeasureTheory.Measure.haarMeasure_self (K₀ := K)
  -- productHaarMeasure = Measure.pi (fun _ => μ) by definition.
  rw [show productHaarMeasure N (PeriodicSite T L) (interfaceSites T L) =
      MeasureTheory.Measure.pi (fun _ : FiniteLinkIndex (PeriodicSite T L) (interfaceSites T L) => μ) from by
    dsimp [productHaarMeasure, μ]]
  -- Apply character orthogonality for product measures.
  exact integral_prod_repCharacter_trivial μ
    (FiniteLinkIndex (PeriodicSite T L) (interfaceSites T L))
    ι dims hDims ρ hU hIrr σ_0 hσ_0_dims hσ_0_trivial
    (fun l => w l.val)

#print axioms interface_char_integral_trivial

/-- **Surjectivity of `plaquetteLinkIdx`**: every link `(n, μ)` appears in at least
one plaquette.  For any link `(n, μ)`, the plaquette `(n, μ, ν)` with `j = 0` gives
`plaquetteLinkIdx (n, μ, ν) 0 = (n, μ)` by definition.

This is the `hlinks_surj` hypothesis needed to apply
`plaquette_product_separable_decomp` (PeterWeyl.lean:1358) to ALL plaquettes. -/
lemma plaquetteLinkIdx_surj (T L : ℕ) [NeZero T] [NeZero L] :
    ∀ (l : PeriodicSite T L × Fin 4),
    ∃ (p : PlaquetteIndex T L) (j : Fin 4), plaquetteLinkIdx T L p j = l := by
  intro ⟨n, μ⟩
  -- The plaquette (n, μ, 0) has plaquetteLinkIdx ... 0 = (n, μ) by definition.
  refine ⟨(n, μ, 0), 0, ?_⟩
  simp [plaquetteLinkIdx]

/-! ### Temporal/spatial split of interface links (L_0 = L_0_temporal ⊔ L_0_spatial)

The interface links at time-0 (`interfaceLinkInt`, a.k.a. `L_0`) split into:
- **Temporal** (μ=0): inverted by the σ reflection (`σ(w) = w⁻¹`).
- **Spatial** (μ≠0): fixed by the σ reflection (`σ(u⁰_s) = u⁰_s`).

This split is the key insight of §8.11.32: expanding the test function `f` in the
Peter-Weyl basis of the temporal links ONLY (keeping spatial links as parameters)
avoids the reorganization obstacle, because the spatial links are the same in both
f-factors (fixed by σ) while the temporal links give a Gram matrix via the triple
product integral (ρ(w⁻¹) = ρ(w)† provides the conjugation). -/

/-- The temporal (time-like, μ=0) links among the time-0 interface links.
Under σ, these are INVERTED: `σ(w) = w⁻¹`. -/
noncomputable def interfaceLinkTemporal (T L : ℕ) [NeZero T] [NeZero L] :
    Finset (InterfaceLink T L) :=
  (interfaceLinkInt T L).filter (fun l => l.val.2 = 0)

/-- The spatial (μ≠0) links among the time-0 interface links.
Under σ, these are FIXED: `σ(u⁰_s) = u⁰_s`. -/
noncomputable def interfaceLinkSpatial (T L : ℕ) [NeZero T] [NeZero L] :
    Finset (InterfaceLink T L) :=
  (interfaceLinkInt T L).filter (fun l => l.val.2 ≠ 0)

/-- Membership in `interfaceLinkTemporal`: time-0 link with μ=0. -/
lemma interfaceLinkTemporal_mem_iff (T L : ℕ) [NeZero T] [NeZero L]
    (l : InterfaceLink T L) :
    l ∈ interfaceLinkTemporal T L ↔ l ∈ interfaceLinkInt T L ∧ l.val.2 = 0 := by
  simp [interfaceLinkTemporal]

/-- Membership in `interfaceLinkSpatial`: time-0 link with μ≠0. -/
lemma interfaceLinkSpatial_mem_iff (T L : ℕ) [NeZero T] [NeZero L]
    (l : InterfaceLink T L) :
    l ∈ interfaceLinkSpatial T L ↔ l ∈ interfaceLinkInt T L ∧ l.val.2 ≠ 0 := by
  simp [interfaceLinkSpatial]

/-- The temporal and spatial links partition the time-0 interface links (L_0). -/
lemma interfaceLinkTemporal_spatial_partition (T L : ℕ) [NeZero T] [NeZero L] :
    Disjoint (interfaceLinkTemporal T L) (interfaceLinkSpatial T L) ∧
    interfaceLinkTemporal T L ∪ interfaceLinkSpatial T L = interfaceLinkInt T L := by
  refine ⟨?_, ?_⟩
  · refine Finset.disjoint_left.mpr (fun l hl hl' => ?_)
    rw [interfaceLinkTemporal_mem_iff] at hl
    rw [interfaceLinkSpatial_mem_iff] at hl'
    exact hl'.2 hl.2
  · ext l
    simp only [Finset.mem_union, interfaceLinkTemporal_mem_iff,
      interfaceLinkSpatial_mem_iff]
    by_cases hμ : l.val.2 = 0 <;> simp [hμ]

/-- The product over `interfaceLinkInt` equals the product over temporal ∪ spatial. -/
lemma prod_interfaceLinkInt_eq_temporal_spatial (T L : ℕ) [NeZero T] [NeZero L]
    {α : Type*} [CommMonoid α] (f : InterfaceLink T L → α) :
    ∏ l ∈ interfaceLinkInt T L, f l =
    (∏ l ∈ interfaceLinkTemporal T L, f l) * (∏ l ∈ interfaceLinkSpatial T L, f l) := by
  have ⟨hdisj, hcover⟩ := interfaceLinkTemporal_spatial_partition T L
  rw [← hcover]
  exact Finset.prod_union hdisj

/-- The product over all plaquettes with an if-condition equals the product over
interface plaquettes only (non-interface terms contribute 1).  This is the
"filter product" step connecting G3 (`exp_neg_beta_wilsonActionOSInterface_eq_prod`)
to the abstract product `∏_{p ∈ InterfacePlaquette} exp(c·Re Tr(...))`. -/
lemma prod_if_interface_eq_prod_subtype (T L : ℕ) [NeZero T] [NeZero L]
    {α : Type*} (f : PlaquetteIndex T L → α) [CommMonoid α] :
    ∏ n : PeriodicSite T L, ∏ μ : Fin 4, ∏ ν : Fin 4,
        (if isInterfacePlaquette T L n μ ν then f (n, μ, ν) else 1) =
    ∏ p : InterfacePlaquette T L, f p.val := by
  classical
  -- Merge the three nested products into one over `PlaquetteIndex T L`.
  -- `simp only` does a bottom-up traversal, so it rewrites the innermost
  -- `∏ μ, ∏ ν` first (→ `∏ q : Fin 4 × Fin 4`) and then `∏ n, ∏ q`
  -- (→ `∏ p : PeriodicSite T L × (Fin 4 × Fin 4)`), producing the
  -- *right-associated* product type `PlaquetteIndex T L`.
  simp only [← Fintype.prod_prod_type']
  -- Now: ∏ p : PlaquetteIndex T L,
  --   (if isInterfacePlaquette T L p.1 p.2.1 p.2.2 then f (p.1, p.2.1, p.2.2) else 1)
  -- Convert the if-product to a filtered product (non-interface terms are 1).
  rw [← Finset.prod_filter]
  -- Now: ∏ p ∈ Finset.univ.filter (isInterfacePlaquette …), f (p.1, p.2.1, p.2.2)
  -- Convert the filtered product to a product over the subtype `InterfacePlaquette`.
  -- (f (p.1, p.2.1, p.2.2) = f p by Prod-eta, and Subtype cond = InterfacePlaquette.)
  exact Finset.prod_subtype _ (fun x => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]) (fun p => f p)

#print axioms prod_if_interface_eq_prod_subtype

/-- **Interface Boltzmann factor as a positive constant times the abstract plaquette
product.** The concrete interface Boltzmann factor `exp(-β·S_int)` equals a positive
constant `C = ∏_{p ∈ InterfacePlaquette} exp(-β²)` times the abstract plaquette product
`∏_{p ∈ InterfacePlaquette} exp((β²/N)·Re Tr(g₀g₁g₂⁻¹g₃⁻¹))`, where the plaquette product
is expressed via the concrete link structures (`interfaceLinkVar`, `interfaceLinkAssign`).

This combines G3 (`exp_neg_beta_wilsonActionOSInterface_eq_prod_abstract`),
`prod_if_interface_eq_prod_subtype` (restrict to interface plaquettes), and
`plaquetteProduct_interface_eq` (concrete→abstract plaquette product).  The constant
`C > 0` is absorbable into normalization.  This is sub-step (ii) of Lemma 2
(`transfer_matrix_integral_reduction`) in
`docs/transfer_matrix_positivity_design.md` §8.8: rewriting the concrete interface
Boltzmann factor into the abstract form that `interface_kernel_character_expansion`
operates on.  Pure algebra — 0 sorries, 0 custom axioms. -/
lemma interface_boltzmann_eq_abstract_product (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L] :
    ∃ (C : ℝ) (hC : 0 < C),
      ∀ (U : LinkVariable (SU N) (PeriodicSite T L)),
      Real.exp (-β * wilsonActionOSInterface N T L β U) =
        C * ∏ p : InterfacePlaquette T L,
          Real.exp ((β * β / N) * Complex.re (Matrix.trace
            ((interfaceLinkVar N T L U (interfaceLinkAssign T L p 0) *
              interfaceLinkVar N T L U (interfaceLinkAssign T L p 1) *
              (interfaceLinkVar N T L U (interfaceLinkAssign T L p 2))⁻¹ *
              (interfaceLinkVar N T L U (interfaceLinkAssign T L p 3))⁻¹ : SU N) :
              Matrix (Fin N) (Fin N) ℂ))) := by
  set C := ∏ p : InterfacePlaquette T L, Real.exp (-(β * β))
  refine ⟨C, ?_, fun U => ?_⟩
  · exact Finset.prod_pos (fun p _ => plaquetteBoltzmann_tm_const_pos β)
  · rw [exp_neg_beta_wilsonActionOSInterface_eq_prod_abstract]
    -- Step 1: rewrite the if-product to a subtype product via prod_if_interface_eq_prod_subtype.
    -- h's LHS is defeq to the goal's LHS (beta + projection reduction); `simp only` handles this.
    have h := prod_if_interface_eq_prod_subtype T L
      (fun p : PlaquetteIndex T L =>
        Real.exp (-(β * β)) *
        Real.exp ((β * β / N) *
          Complex.re (Matrix.trace ((plaquetteProduct N U p.1 p.2.1 p.2.2 :
            Matrix (Fin N) (Fin N) ℂ)))))
    simp only [h]
    -- Step 2: split the product of products.
    rw [Finset.prod_mul_distrib]
    -- Step 3: C = ∏ p, exp(-β²) by `set`, so the first factor is C (closed by rfl below).
    -- Step 4: rewrite plaquetteProduct to the abstract link form in the second factor.
    have h_link : ∏ p : InterfacePlaquette T L,
        Real.exp ((β * β / N) *
          Complex.re (Matrix.trace ((plaquetteProduct N U p.val.1 p.val.2.1 p.val.2.2 :
            Matrix (Fin N) (Fin N) ℂ)))) =
      ∏ p : InterfacePlaquette T L,
        Real.exp ((β * β / N) *
          Complex.re (Matrix.trace
            ((interfaceLinkVar N T L U (interfaceLinkAssign T L p 0) *
              interfaceLinkVar N T L U (interfaceLinkAssign T L p 1) *
              (interfaceLinkVar N T L U (interfaceLinkAssign T L p 2))⁻¹ *
              (interfaceLinkVar N T L U (interfaceLinkAssign T L p 3))⁻¹ : SU N) :
              Matrix (Fin N) (Fin N) ℂ))) := by
      exact Finset.prod_congr rfl (fun p _ => by rw [plaquetteProduct_interface_eq N T L U p])
    rw [h_link]

#print axioms interface_boltzmann_eq_abstract_product

/-- **Character expansion of the concrete interface plaquette product.** Applying
`interface_kernel_character_expansion` (Peter-Weyl / Clebsch-Gordan) to the concrete
lattice, the abstract interface plaquette product
`∏_{p ∈ InterfacePlaquette} exp((β²/N)·Re Tr(g₀g₁g₂⁻¹g₃⁻¹))` (viewed in `ℂ`) admits the
separable character expansion

    ∏_p exp(c·Re Tr(...)) = ∑_w F(w) · Φ_w(U⁺) · Ψ_w(u⁰) · conj(Φ_w(V⁺))

with `F(w) ≥ 0`, where `Φ_w(U⁺) = ∏_{l ∈ L_U} χ_{w(l)}(g_l)`,
`Ψ_w(u⁰) = ∏_{l ∈ L_0} χ_{w(l)}(g_l)`, and the V⁺ factor uses the dual map.
This is sub-step (ii) of Lemma 2 (`transfer_matrix_integral_reduction`):
applying the abstract character expansion to the concrete lattice data.
Uses the `peterWeyl_clebschGordan_plaquette` axiom (count 6); 0 sorries. -/
lemma interface_product_character_expansion (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (hN : 1 ≤ N) :
    ∃ (ι : Type) (hι : Fintype ι) (dims : ι → ℕ)
      (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
      (hU : ∀ i, IsUnitaryRepresentation (ρ i))
      (hMeas : ∀ i, Measurable (repCharacter (ρ i)))
      (dual : ι → ι)
      (F : (InterfaceLink T L → ι) → ℝ) (hF : ∀ w, 0 ≤ F w),
      ∀ (U : LinkVariable (SU N) (PeriodicSite T L)),
      ∏ p : InterfacePlaquette T L,
        (Real.exp ((β * β / N) * Complex.re (Matrix.trace
          ((interfaceLinkVar N T L U (interfaceLinkAssign T L p 0) *
            interfaceLinkVar N T L U (interfaceLinkAssign T L p 1) *
            (interfaceLinkVar N T L U (interfaceLinkAssign T L p 2))⁻¹ *
            (interfaceLinkVar N T L U (interfaceLinkAssign T L p 3))⁻¹ : SU N) :
            Matrix (Fin N) (Fin N) ℂ))) : ℂ) =
        ∑ w : InterfaceLink T L → ι, (F w : ℂ) *
          (∏ l ∈ interfaceLinkPos T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
          (∏ l ∈ interfaceLinkInt T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
          star (∏ l ∈ interfaceLinkNeg T L, repCharacter (ρ (dual (w l))) (interfaceLinkVar N T L U l)) := by
  obtain ⟨ι, hι, dims, ρ, hU, hMeas, hIrr, hDims, σ_0, hσ_0_dims, hσ_0_trivial, coeff, hcoeff, cg, hcg, hcg_decomp, dual, hdual,
      cgME, hcgME_decomp, hcgME_unitary, hcgME_cross_rep,
      Λ, hΛ, dimsΛ, ρΛ, hUΛ, hIrrΛ, hDimsΛ, emb, hemb, μ, hμ,
      cgMEΛ, hcgMEΛ_support, hexp4, hL2, hSchurΛ, hcgMEΛ_parts⟩ :=
    peterWeyl_clebschGordan_plaquette N (β * β / N) (plaquetteBoltzmann_tm_coupling_nonneg N β hN)
  obtain ⟨hSchurΛ_int, hSchurΛ_diag, hSchurΛ_offdiag⟩ := hSchurΛ
  obtain ⟨hcgMEΛ_decomp, hcgMEΛ_unitary, hcgMEΛ_support_zero⟩ := hcgMEΛ_parts
  letI : Fintype ι := hι
  classical
  obtain ⟨F, hF, hF_decomp⟩ := interface_kernel_character_expansion
    ρ hU coeff hcoeff cg hcg hcg_decomp dual hdual
    (β * β / N) (plaquetteBoltzmann_tm_coupling_nonneg N β hN) hexp4
    (InterfacePlaquette T L) (InterfaceLink T L) (interfaceLinkAssign T L)
    (interfaceLinkAssign_surj T L)
    (interfaceLinkPos T L) (interfaceLinkInt T L) (interfaceLinkNeg T L)
    (interfaceLinkPartition_hdisj T L) (interfaceLinkPartition_hcover T L)
  refine ⟨ι, hι, dims, ρ, hU, hMeas, dual, F, hF, fun U => ?_⟩
  exact hF_decomp (interfaceLinkVar N T L U)

#print axioms interface_product_character_expansion

/-- **Plaquette-level character expansion of the interface plaquette product.**

Applying `plaquette_product_single_char_decomp` (product-of-sums) to the
concrete interface plaquettes, the abstract interface plaquette product
`∏_{p ∈ InterfacePlaquette} exp((β²/N)·Re Tr(g₀g₁g₂⁻¹g₃⁻¹))` (viewed in `ℂ`)
admits the **plaquette-level** character expansion

    ∏_p exp(c·Re Tr(gP p)) = ∑_{w : InterfacePlaquette → ι} F(w) · ∏_p χ_{w(p)}(gP p)

with `F(w) = ∏_p coeff_{w(p)} ≥ 0`, where `gP p` is the plaquette product
`g₀·g₁·g₂⁻¹·g₃⁻¹` expressed via the concrete interface links
(`interfaceLinkVar`, `interfaceLinkAssign`).

This is the **plaquette-level** analogue of `interface_product_character_expansion`
(which is link-level: one character per LINK).  Here there is one character per
PLAQUETTE — exactly the form the Lüscher cascade needs: at the plaquette level,
each temporal interface link appears in TWO plaquette characters, so the cascade
(integrating out the temporal link via Schur orthogonality) forces MATCHING
(`w(p₁) = w(p₂)`), not triviality, propagating the constraint across the lattice
and producing constant non-negative coefficients.  See
`docs/transfer_matrix_positivity_design.md` §8.11.81.

Uses `plaquette_boltzmann_character_expansion_single` (uniform `∀ g` single-char
expansion, providing the `hexp1` hypothesis) + `plaquette_product_single_char_decomp`
(product-of-sums).  Both depend only on `peterWeyl_clebschGordan_plaquette`
(axiom count 6, unchanged); 0 sorries. -/
lemma interface_product_plaquette_char_expansion (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (hN : 1 ≤ N) :
    ∃ (ι : Type) (hι : Fintype ι) (dims : ι → ℕ)
      (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
      (hU : ∀ i, IsUnitaryRepresentation (ρ i))
      (hMeas : ∀ i, Measurable (repCharacter (ρ i)))
      (hIrr : ∀ i, IsIrreducible (ρ i))
      (hDims : ∀ i, 0 < dims i)
      (coeff : ι → ℝ) (hcoeff : ∀ s, 0 ≤ coeff s)
      (F : (InterfacePlaquette T L → ι) → ℝ) (hF : ∀ w, 0 ≤ F w),
      ∀ (U : LinkVariable (SU N) (PeriodicSite T L)),
      ∏ p : InterfacePlaquette T L,
        (Real.exp ((β * β / N) * Complex.re (Matrix.trace
          ((interfaceLinkVar N T L U (interfaceLinkAssign T L p 0) *
            interfaceLinkVar N T L U (interfaceLinkAssign T L p 1) *
            (interfaceLinkVar N T L U (interfaceLinkAssign T L p 2))⁻¹ *
            (interfaceLinkVar N T L U (interfaceLinkAssign T L p 3))⁻¹ : SU N) :
            Matrix (Fin N) (Fin N) ℂ))) : ℂ) =
        ∑ w : InterfacePlaquette T L → ι, (F w : ℂ) *
          ∏ p : InterfacePlaquette T L,
            repCharacter (ρ (w p))
              (interfaceLinkVar N T L U (interfaceLinkAssign T L p 0) *
               interfaceLinkVar N T L U (interfaceLinkAssign T L p 1) *
               (interfaceLinkVar N T L U (interfaceLinkAssign T L p 2))⁻¹ *
               (interfaceLinkVar N T L U (interfaceLinkAssign T L p 3))⁻¹) := by
  obtain ⟨ι, hι, dims, ρ, hU, hMeas, hIrr, hDims, coeff, hcoeff, hexp1⟩ :=
    plaquette_boltzmann_character_expansion_single N (β * β / N)
      (plaquetteBoltzmann_tm_coupling_nonneg N β hN)
  letI : Fintype ι := hι
  classical
  refine ⟨ι, hι, dims, ρ, hU, hMeas, hIrr, hDims, coeff, hcoeff,
      (fun w => ∏ p, coeff (w p)), fun w => Finset.prod_nonneg (fun p _ => hcoeff (w p)),
      fun U => ?_⟩
  rw [Finset.prod_congr rfl (fun p _ => hexp1
      (interfaceLinkVar N T L U (interfaceLinkAssign T L p 0) *
        interfaceLinkVar N T L U (interfaceLinkAssign T L p 1) *
        (interfaceLinkVar N T L U (interfaceLinkAssign T L p 2))⁻¹ *
        (interfaceLinkVar N T L U (interfaceLinkAssign T L p 3))⁻¹))]
  rw [Fintype.prod_sum (fun p s => (coeff s : ℂ) * repCharacter (ρ s)
      (interfaceLinkVar N T L U (interfaceLinkAssign T L p 0) *
        interfaceLinkVar N T L U (interfaceLinkAssign T L p 1) *
        (interfaceLinkVar N T L U (interfaceLinkAssign T L p 2))⁻¹ *
        (interfaceLinkVar N T L U (interfaceLinkAssign T L p 3))⁻¹))]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Finset.prod_mul_distrib]
  simp only [Complex.ofReal_prod]

#print axioms interface_product_plaquette_char_expansion

/-- **Combined plaquette-level character expansion of the interface Boltzmann factor.**
Composing `interface_boltzmann_eq_abstract_product` (exp(-β·S_int) = C · ∏_p exp(c·Re Tr(...)))
with `interface_product_plaquette_char_expansion` (∏_p exp(c·Re Tr(...)) = ∑_w F(w)·∏_p χ_{w(p)}(...)),
the interface Boltzmann factor admits the **plaquette-level** character expansion (viewed in ℂ)

    (exp(-β·S_int(U)) : ℂ) = (C : ℂ) · ∑_{w : InterfacePlaquette → ι} F(w) · ∏_p χ_{w(p)}(gP p)

with `C > 0` and `F(w) = ∏_p coeff_{w(p)} ≥ 0`.  This is the plaquette-level analogue of
`interface_boltzmann_character_expansion` (which is link-level).  It is the form the Lüscher
cascade operates on: one character per plaquette, so each temporal link (shared between two
plaquettes) is integrated out via Schur orthogonality forcing matching, not triviality.
Uses `peterWeyl_clebschGordan_plaquette` (axiom count 6, unchanged); 0 sorries. -/
lemma interface_boltzmann_plaquette_char_expansion (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (hN : 1 ≤ N) :
    ∃ (C : ℝ) (hC : 0 < C)
      (ι : Type) (hι : Fintype ι) (dims : ι → ℕ)
      (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
      (hU : ∀ i, IsUnitaryRepresentation (ρ i))
      (hMeas : ∀ i, Measurable (repCharacter (ρ i)))
      (hIrr : ∀ i, IsIrreducible (ρ i))
      (hDims : ∀ i, 0 < dims i)
      (coeff : ι → ℝ) (hcoeff : ∀ s, 0 ≤ coeff s)
      (F : (InterfacePlaquette T L → ι) → ℝ) (hF : ∀ w, 0 ≤ F w),
      ∀ (U : LinkVariable (SU N) (PeriodicSite T L)),
      (Real.exp (-β * wilsonActionOSInterface N T L β U) : ℂ) =
        (C : ℂ) * ∑ w : InterfacePlaquette T L → ι, (F w : ℂ) *
          ∏ p : InterfacePlaquette T L,
            repCharacter (ρ (w p))
              (interfaceLinkVar N T L U (interfaceLinkAssign T L p 0) *
               interfaceLinkVar N T L U (interfaceLinkAssign T L p 1) *
               (interfaceLinkVar N T L U (interfaceLinkAssign T L p 2))⁻¹ *
               (interfaceLinkVar N T L U (interfaceLinkAssign T L p 3))⁻¹) := by
  obtain ⟨C, hC, hC_eq_all⟩ := interface_boltzmann_eq_abstract_product N T L β
  obtain ⟨ι, hι, dims, ρ, hU, hMeas, hIrr, hDims, coeff, hcoeff, F, hF, hF_decomp⟩ :=
    interface_product_plaquette_char_expansion N T L β hN
  letI : Fintype ι := hι
  classical
  refine ⟨C, hC, ι, hι, dims, ρ, hU, hMeas, hIrr, hDims, coeff, hcoeff, F, hF, fun U => ?_⟩
  rw [hC_eq_all U]
  have h := hF_decomp U
  norm_cast at h
  rw [Complex.ofReal_mul, h]

#print axioms interface_boltzmann_plaquette_char_expansion


/-! **Combined character expansion of the interface Boltzmann factor.** Composing
`interface_boltzmann_eq_abstract_product` (exp(-β·S_int) = C · ∏_p exp(c·Re Tr(...)))
with `interface_product_character_expansion` (∏_p exp(c·Re Tr(...)) = ∑_w F(w)·Φ_w·Ψ_w·V_w),
the interface Boltzmann factor admits the character expansion (viewed in ℂ)

    (exp(-β·S_int(U)) : ℂ) = (C : ℂ) · ∑_w F(w) · Φ_w(U) · Ψ_w(U) · V_w(U)

with C > 0 and F(w) ≥ 0, where Φ_w(U) = ∏_{l ∈ L_U} χ_{w(l)}(g_l),
Ψ_w(U) = ∏_{l ∈ L_0} χ_{w(l)}(g_l), V_w(U) = star(∏_{l ∈ L_V} χ_{dual(w(l))}(g_l)),
and g_l = interfaceLinkVar U l.  This is step 3 of sub-step (iii) of Lemma 2
(`transfer_matrix_integral_reduction`): substituting the character expansion
into the transfer matrix inner product. Uses `peterWeyl_clebschGordan_plaquette`
(axiom count 6, unchanged); 0 sorries. -/
lemma interface_boltzmann_character_expansion (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (hN : 1 ≤ N) :
    ∃ (C : ℝ) (hC : 0 < C)
      (ι : Type) (hι : Fintype ι) (dims : ι → ℕ)
      (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
      (hU : ∀ i, IsUnitaryRepresentation (ρ i))
      (hMeas : ∀ i, Measurable (repCharacter (ρ i)))
      (dual : ι → ι)
      (F : (InterfaceLink T L → ι) → ℝ) (hF : ∀ w, 0 ≤ F w),
      ∀ (U : LinkVariable (SU N) (PeriodicSite T L)),
      (Real.exp (-β * wilsonActionOSInterface N T L β U) : ℂ) =
        (C : ℂ) * ∑ w : InterfaceLink T L → ι, (F w : ℂ) *
          (∏ l ∈ interfaceLinkPos T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
          (∏ l ∈ interfaceLinkInt T L, repCharacter (ρ (w l)) (interfaceLinkVar N T L U l)) *
          star (∏ l ∈ interfaceLinkNeg T L, repCharacter (ρ (dual (w l))) (interfaceLinkVar N T L U l)) := by
  -- C = ∏_p exp(-β²) is independent of U; obtain it once (uniform abstract-product form).
  obtain ⟨C, hC, hC_eq_all⟩ := interface_boltzmann_eq_abstract_product N T L β
  -- The character-expansion data (ι, ρ, dual, F) is independent of U (uniform version).
  obtain ⟨ι, hι, dims, ρ, hU, hMeas, dual, F, hF, hF_decomp⟩ :=
    interface_product_character_expansion N T L β hN
  letI : Fintype ι := hι
  classical
  refine ⟨C, hC, ι, hι, dims, ρ, hU, hMeas, dual, F, hF, fun U => ?_⟩
  -- Per-U: combine the abstract-product form with the character expansion.
  rw [hC_eq_all U]
  have h := hF_decomp U
  norm_cast at h
  rw [Complex.ofReal_mul, h]

#print axioms interface_boltzmann_character_expansion

/-! ### Full character expansion (ALL plaquettes)

For the FULL character expansion (§8.11.61), we expand ALL plaquettes (bulk
positive, bulk negative, AND interface) in characters, not just the interface
ones.  This uses the full link partition (`allLinkPos`/`allLinkInt`/`allLinkNeg`)
and `plaquetteLinkIdx` (which assigns the 4 links of each plaquette).  The
result is a character expansion with `F_full(w) ≥ 0` that covers ALL links,
which is the key ingredient for the `dependsOnlyOnPositive` reflection
positivity proof. -/

/-- **Full Boltzmann factor as a positive constant times the abstract plaquette
product.** The full Boltzmann factor `exp(-β·S_W)` equals a positive constant
`C = ∏_{p ∈ PlaquetteIndex} exp(-β²)` times the abstract plaquette product
`∏_{p ∈ PlaquetteIndex} exp((β²/N)·Re Tr(P_p))`, where `P_p` is the plaquette
product `plaquetteProduct N U p.1 p.2.1 p.2.2`.

This is the full-lattice analogue of `interface_boltzmann_eq_abstract_product`
(which covers only interface plaquettes).  It combines
`exp_neg_beta_wilsonActionFinite_eq_prod` (exp-of-sum for the full action) with
`plaquetteContribution_exp_decomp_tm` (per-plaquette Boltzmann decomposition).
The constant `C > 0` is absorbable into normalization.  Pure algebra —
0 sorries, 0 custom axioms. -/
lemma full_boltzmann_eq_abstract_product (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L] :
    ∃ (C : ℝ) (hC : 0 < C),
      ∀ (U : LinkVariable (SU N) (PeriodicSite T L)),
      Real.exp (-β * wilsonActionFinite N β (Finset.univ : Finset (PeriodicSite T L)) U) =
        C * ∏ p : PlaquetteIndex T L,
          Real.exp ((β * β / N) * Complex.re (Matrix.trace
            ((plaquetteProduct N U p.1 p.2.1 p.2.2 : SU N) :
              Matrix (Fin N) (Fin N) ℂ))) := by
  set C := ∏ p : PlaquetteIndex T L, Real.exp (-(β * β))
  refine ⟨C, ?_, fun U => ?_⟩
  · exact Finset.prod_pos (fun p _ => plaquetteBoltzmann_tm_const_pos β)
  · rw [exp_neg_beta_wilsonActionFinite_eq_prod]
    simp only [← Fintype.prod_prod_type']
    simp only [plaquetteContribution_exp_decomp_tm]
    rw [Finset.prod_mul_distrib]

#print axioms full_boltzmann_eq_abstract_product

