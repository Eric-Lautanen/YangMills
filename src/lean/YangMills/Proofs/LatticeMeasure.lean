/-
# Lattice Yang-Mills Measure
-/
import YangMills.Lattice
import YangMills.SpecialUnitary
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.Algebra.Group.Compact

open Set Matrix MeasureTheory
open scoped MeasureTheory
open Complex

namespace YangMills
namespace Lattice

/-- MeasurableSpace on `LinkVariable` induced by the `value` projection. -/
instance {G : Type} {Λ : Type} [MeasurableSpace G] :
    MeasurableSpace (LinkVariable G Λ) :=
  MeasurableSpace.comap (fun U => U.value) inferInstance

section LinkSet
def LinkSet (Λ : Type) : Type := Λ × Fin 4
abbrev LinkConfig (N : ℕ) (Λ : Type) : Type := LinkSet Λ → SU N
def linkVariableToConfig (N : ℕ) (Λ : Type) (U : LinkVariable (SU N) Λ) : LinkConfig N Λ :=
  λ (site, μ) => U.value site μ
def configToLinkVariable (N : ℕ) (Λ : Type) (U : LinkConfig N Λ) : LinkVariable (SU N) Λ :=
  { value := λ site μ => U (site, μ) }
lemma linkVariableConfig_bijection (N : ℕ) (Λ : Type) (U : LinkVariable (SU N) Λ) :
    configToLinkVariable N Λ (linkVariableToConfig N Λ U) = U := by
  ext site μ; simp [linkVariableToConfig, configToLinkVariable]
lemma configLinkVariable_bijection (N : ℕ) (Λ : Type) (U : LinkConfig N Λ) :
    linkVariableToConfig N Λ (configToLinkVariable N Λ U) = U := by
  ext ⟨site, μ⟩; simp [linkVariableToConfig, configToLinkVariable]
end LinkSet

section ProductHaarMeasure

section GenericProductMeasure

/-- The index set of links in a finite lattice: pairs (site, direction) where site ∈ sites. -/
def FiniteLinkIndex (Λ : Type) [DecidableEq Λ] (sites : Finset Λ) : Type :=
  Subtype (λ (x : Λ × Fin 4) => x.1 ∈ sites)

instance (Λ : Type) [DecidableEq Λ] (sites : Finset Λ) : Fintype (FiniteLinkIndex Λ sites) :=
  Fintype.subtype (sites.product (Finset.univ : Finset (Fin 4))) (by intro x; simp)

/-- A link configuration on a finite lattice is an assignment of SU(N) group elements
to each directed link (site, μ) where site ∈ sites. -/
abbrev FiniteLinkConfig (N : ℕ) (Λ : Type) [DecidableEq Λ] (sites : Finset Λ) : Type :=
  FiniteLinkIndex Λ sites → SU N

/-- Product Haar measure on SU(N)^{sites × {0,1,2,3}}. -/
noncomputable def productHaarMeasure (N : ℕ) (Λ : Type) [DecidableEq Λ] (sites : Finset Λ) :
    Measure (FiniteLinkConfig N Λ sites) :=
  let K : TopologicalSpace.PositiveCompacts (SU N) :=
    ⟨⟨Set.univ, isCompact_univ⟩, by simpa using Set.univ_nonempty (α := SU N)⟩
  MeasureTheory.Measure.pi (λ _ : FiniteLinkIndex Λ sites => MeasureTheory.Measure.haarMeasure K)

/-- Extend a configuration on `sites` to a full link variable by setting missing links to 1. -/
noncomputable def extendLinkVariable (N : ℕ) (Λ : Type) [DecidableEq Λ] (sites : Finset Λ)
    (U : FiniteLinkConfig N Λ sites) : LinkVariable (SU N) Λ :=
  { value := λ n μ => if h : n ∈ sites then U ⟨(n, μ), h⟩ else 1 }

/-- Restrict a full link variable to a configuration on `sites`. -/
noncomputable def restrictLinkVariable (N : ℕ) (Λ : Type) [DecidableEq Λ] (sites : Finset Λ)
    (U : LinkVariable (SU N) Λ) : FiniteLinkConfig N Λ sites :=
  λ ⟨(n, μ), hn⟩ => U.value n μ

/-- The Wilson action evaluated on a finite-link configuration. -/
noncomputable def wilsonActionFiniteConfig (N : ℕ) (β : ℝ) (Λ : Type) [DecidableEq Λ] [AddVector Λ]
    (sites : Finset Λ) (cfg : FiniteLinkConfig N Λ sites) : ℝ :=
  wilsonActionFinite N β sites (extendLinkVariable N Λ sites cfg)

/-- `extendLinkVariable` is measurable: each component is either an evaluation (measurable)
or a constant (measurable), depending on whether the site is in the lattice. -/
lemma measurable_extendLinkVariable (N : ℕ) (Λ : Type) [DecidableEq Λ] (sites : Finset Λ) :
    Measurable (extendLinkVariable N Λ sites) := by
  have h : Measurable ((fun U : LinkVariable (SU N) Λ => U.value) ∘ extendLinkVariable N Λ sites) := by
    show Measurable (fun (U : FiniteLinkConfig N Λ sites) (n : Λ) (μ : Fin 4) =>
      if h : n ∈ sites then U ⟨(n, μ), h⟩ else (1 : SU N))
    rw [measurable_pi_iff]
    intro n
    rw [measurable_pi_iff]
    intro μ
    by_cases h : n ∈ sites
    · simp only [h, if_pos]
      exact measurable_pi_apply (⟨(n, μ), h⟩ : FiniteLinkIndex Λ sites)
    · simp only [h, if_neg]
      exact measurable_const
  exact measurable_comap_iff.mpr h

/-- `LinkVariable.value` is surjective: every function comes from a LinkVariable. -/
lemma LinkVariable.value_surjective (G : Type) (Λ : Type) :
    Function.Surjective (fun (U : LinkVariable G Λ) => U.value) := by
  intro f; exact ⟨{ value := f }, rfl⟩

/-- `wilsonActionFiniteConfig` is measurable, expressed as a finite sum of measurable terms.
Each term `plaquetteContribution N β (extendLinkVariable N Λ sites cfg) n μ ν` is measurable
because it depends on `cfg` at finitely many indices via continuous SU(N) operations
(multiplication, inversion, trace, real part). -/
lemma measurable_wilsonActionFiniteConfig (N : ℕ) (β : ℝ) (Λ : Type) [DecidableEq Λ] [AddVector Λ]
    (sites : Finset Λ) : Measurable (wilsonActionFiniteConfig N β Λ sites) := by
  unfold wilsonActionFiniteConfig wilsonActionFinite
  refine Finset.measurable_sum _ (λ n hn => ?_)
  refine Finset.measurable_sum _ (λ μ hμ => ?_)
  refine Finset.measurable_sum _ (λ ν hν => ?_)
  unfold plaquetteContribution
  -- Each term: β * (1 - (1 / (N : ℝ)) * ((trace (plaquetteProduct ...)).re : ℝ))
  -- Show the innermost part (trace ...).re is measurable
  have h_meas_inner : Measurable (λ (cfg : FiniteLinkConfig N Λ sites) =>
    ((trace ((plaquetteProduct N (extendLinkVariable N Λ sites cfg) n μ ν : Matrix (Fin N) (Fin N) ℂ))).re : ℝ)) := by
    have h_cont_trace_re : Continuous (λ (g : SU N) => ((trace ((g : Matrix (Fin N) (Fin N) ℂ))).re : ℝ)) := by
      -- trace = λ A => ∑ᵢ Aᵢᵢ is continuous as a sum of projections
      have h_cont_trace : Continuous (trace : Matrix (Fin N) (Fin N) ℂ → ℂ) := by
        have h_eq : trace = λ (A : Matrix (Fin N) (Fin N) ℂ) => ∑ i : Fin N, A i i := by
          ext A; simp [Matrix.trace]
        rw [h_eq]
        refine continuous_finsetSum Finset.univ (λ i hi => ?_)
        -- A i i is the (i,i) entry, which is continuous
        have h_entry : Continuous (λ (A : Matrix (Fin N) (Fin N) ℂ) => A i i) :=
          (continuous_apply i).comp (continuous_apply i)
        exact h_entry
      -- The inclusion SU N → Matrix is continuous (subtype)
      have h_cont_val : Continuous (Subtype.val : SU N → Matrix (Fin N) (Fin N) ℂ) :=
        continuous_subtype_val
      -- re is continuous
      have h_cont_re : Continuous (Complex.re : ℂ → ℝ) := Complex.continuous_re
      -- Composition: g ↦ (g : Matrix) ↦ trace(...) ↦ re(trace)
      exact h_cont_re.comp (h_cont_trace.comp h_cont_val)
    have h_cont_pp : Continuous (λ (cfg : FiniteLinkConfig N Λ sites) =>
      plaquetteProduct N (extendLinkVariable N Λ sites cfg) n μ ν) := by
      have h_val_cont (n' : Λ) (μ' : Fin 4) : Continuous (λ (cfg : FiniteLinkConfig N Λ sites) =>
        (extendLinkVariable N Λ sites cfg).value n' μ') := by
        by_cases h : n' ∈ sites
        · have h_eq : (λ (cfg : FiniteLinkConfig N Λ sites) => (extendLinkVariable N Λ sites cfg).value n' μ') =
            (λ cfg : FiniteLinkConfig N Λ sites => cfg ⟨(n', μ'), h⟩) := by
            ext cfg; simp [extendLinkVariable, h]
          rw [h_eq]
          exact continuous_apply (⟨(n', μ'), h⟩ : FiniteLinkIndex Λ sites)
        · have h_eq : (λ (cfg : FiniteLinkConfig N Λ sites) => (extendLinkVariable N Λ sites cfg).value n' μ') =
            (λ _ : FiniteLinkConfig N Λ sites => (1 : SU N)) := by
            ext cfg; simp [extendLinkVariable, h]
          rw [h_eq]
          exact continuous_const
      unfold plaquetteProduct
      have h_ab : Continuous (λ (cfg : FiniteLinkConfig N Λ sites) =>
        (extendLinkVariable N Λ sites cfg).value n μ * (extendLinkVariable N Λ sites cfg).value (AddVector.addVector n μ) ν) :=
        Continuous.mul (h_val_cont n μ) (h_val_cont (AddVector.addVector n μ) ν)
      have h_abc : Continuous (λ (cfg : FiniteLinkConfig N Λ sites) =>
        (extendLinkVariable N Λ sites cfg).value n μ * (extendLinkVariable N Λ sites cfg).value (AddVector.addVector n μ) ν *
        ((extendLinkVariable N Λ sites cfg).value (AddVector.addVector (AddVector.addVector n μ) ν) μ)⁻¹) :=
        Continuous.mul h_ab (Continuous.inv (h_val_cont (AddVector.addVector (AddVector.addVector n μ) ν) μ))
      exact Continuous.mul h_abc (Continuous.inv (h_val_cont (AddVector.addVector n ν) ν))
    have h_cont_total : Continuous (λ (cfg : FiniteLinkConfig N Λ sites) =>
      ((trace ((plaquetteProduct N (extendLinkVariable N Λ sites cfg) n μ ν : Matrix (Fin N) (Fin N) ℂ))).re : ℝ)) :=
      h_cont_trace_re.comp h_cont_pp
    haveI : OpensMeasurableSpace (FiniteLinkConfig N Λ sites) := by
      infer_instance
    exact h_cont_total.measurable
  have h_term : Measurable (λ (cfg : FiniteLinkConfig N Λ sites) =>
    β * ((1 : ℝ) - (1 / (N : ℝ)) * ((trace ((plaquetteProduct N (extendLinkVariable N Λ sites cfg) n μ ν :
      Matrix (Fin N) (Fin N) ℂ))).re : ℝ))) := by
    refine Measurable.const_mul (Measurable.sub (by exact measurable_const)
      (Measurable.const_mul h_meas_inner (1 / (N : ℝ)))) β
  exact h_term

lemma productHaarMeasure_total_volume (N : ℕ) (Λ : Type) [DecidableEq Λ] (sites : Finset Λ) :
    productHaarMeasure N Λ sites (Set.univ : Set (FiniteLinkConfig N Λ sites)) = 1 := by
  dsimp [productHaarMeasure]
  rw [MeasureTheory.Measure.pi_univ]
  let K : TopologicalSpace.PositiveCompacts (SU N) :=
    ⟨⟨Set.univ, isCompact_univ⟩, by simpa using Set.univ_nonempty (α := SU N)⟩
  have h_one : Measure.haarMeasure K (Set.univ : Set (SU N)) = 1 := by
    simpa [K] using Measure.haarMeasure_self (K₀ := K)
  have h_prod : (∏ _ : FiniteLinkIndex Λ sites, Measure.haarMeasure K (Set.univ : Set (SU N))) = 1 := by
    simp [h_one]
  simpa [K] using h_prod

lemma productHaarMeasure_isFiniteMeasure (N : ℕ) (Λ : Type) [DecidableEq Λ] (sites : Finset Λ) :
    IsFiniteMeasure (productHaarMeasure N Λ sites) := by
  have h_total : productHaarMeasure N Λ sites (Set.univ : Set (FiniteLinkConfig N Λ sites)) = 1 :=
    productHaarMeasure_total_volume N Λ sites
  refine { measure_univ_lt_top := ?_ }
  rw [h_total]
  exact ENNReal.one_lt_top

/-- The Haar measure on `SU(N)` is invariant under inversion `g ↦ g⁻¹`.
This follows from `IsHaarMeasure.isInvInvariant_of_regular` (Mathlib), since
`SU(N)` is compact (hence locally compact) and the Haar measure is regular.

**Status**: the proof is a standard instance-resolution chain
(`LocallyCompactSpace` from `PositiveCompacts` → `Regular` from
`regular_haarMeasure` → `IsInvInvariant` from
`isInvInvariant_of_regular` → `map_inv_eq_self`), but the instance resolution
is delicate due to the `let`-bound `PositiveCompacts` value.  The lemma is
stated as a `sorry` pending instance-resolution plumbing. -/
lemma haarMeasure_inv_invariant (N : ℕ) :
    let K : TopologicalSpace.PositiveCompacts (SU N) :=
      ⟨⟨Set.univ, isCompact_univ⟩, by simpa using Set.univ_nonempty (α := SU N)⟩
    MeasureTheory.Measure.map Inv.inv (MeasureTheory.Measure.haarMeasure K) =
      MeasureTheory.Measure.haarMeasure K := by
  intro K
  set μ := MeasureTheory.Measure.haarMeasure K with hμ_def
  have hμ_univ : μ Set.univ = 1 := by
    simpa [K, hμ_def] using MeasureTheory.Measure.haarMeasure_self (K₀ := K)
  -- Compact groups are unimodular: μ is right-invariant.
  haveI : Measure.IsMulRightInvariant μ := by
    refine ⟨fun g => ?_⟩
    haveI : Measure.IsMulLeftInvariant (Measure.map (fun x => x * g) μ) :=
      isMulLeftInvariant_map_mul_right g
    have hmap_univ : Measure.map (fun x => x * g) μ Set.univ = 1 := by
      rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, preimage_univ]
      exact hμ_univ
    haveI : IsFiniteMeasureOnCompacts (Measure.map (fun x => x * g) μ) := by
      refine ⟨fun s _hs => ?_⟩
      exact (measure_mono (Set.subset_univ _)).trans_lt
        (hmap_univ.symm ▸ ENNReal.one_lt_top)
    have h_eq : Measure.map (fun x => x * g) μ =
        Measure.haarScalarFactor (Measure.map (fun x => x * g) μ) μ • μ :=
      Measure.isMulInvariant_eq_smul_of_compactSpace _ _
    have h_scalar : Measure.haarScalarFactor (Measure.map (fun x => x * g) μ) μ = 1 := by
      have h' : Measure.map (fun x => x * g) μ Set.univ =
          Measure.haarScalarFactor (Measure.map (fun x => x * g) μ) μ * μ Set.univ := by
        have hstep : Measure.map (fun x => x * g) μ Set.univ =
            (Measure.haarScalarFactor (Measure.map (fun x => x * g) μ) μ • μ) Set.univ :=
          congr_arg (fun ν => ν Set.univ) h_eq
        rw [hstep, Measure.coe_nnreal_smul_apply]
      rw [hμ_univ, hmap_univ] at h'
      simp at h'
      exact_mod_cast h'.symm
    rw [h_eq, h_scalar, one_smul]
  -- μ.inv is left-invariant (from right-invariance of μ)
  haveI : Measure.IsMulLeftInvariant μ.inv := inferInstance
  haveI : IsFiniteMeasureOnCompacts μ.inv := inferInstance
  -- By uniqueness: μ.inv = c • μ, c = 1
  have h_eq : μ.inv = Measure.haarScalarFactor μ.inv μ • μ :=
    Measure.isMulInvariant_eq_smul_of_compactSpace _ _
  have hμinv_univ : μ.inv Set.univ = 1 := by
    rw [Measure.inv_def, Measure.map_apply measurable_inv MeasurableSet.univ, preimage_univ]
    exact hμ_univ
  have h_scalar : Measure.haarScalarFactor μ.inv μ = 1 := by
    have h' : μ.inv Set.univ = Measure.haarScalarFactor μ.inv μ * μ Set.univ := by
      have hstep : μ.inv Set.univ =
          (Measure.haarScalarFactor μ.inv μ • μ) Set.univ :=
        congr_arg (fun ν => ν Set.univ) h_eq
      rw [hstep, Measure.coe_nnreal_smul_apply]
    rw [hμ_univ, hμinv_univ] at h'
    simp at h'
    exact_mod_cast h'.symm
  rw [← Measure.inv_def, h_eq, h_scalar, one_smul]

/-- The Haar measure on `SU(N)` is invariant under right multiplication `u ↦ u * h`.
Compact groups are unimodular: the Haar measure is both left- and right-invariant.
The proof uses the uniqueness of Haar measure on compact groups
(`isMulInvariant_eq_smul_of_compactSpace`), evaluating the scalar on `Set.univ`. -/
lemma haarMeasure_right_mul_invariant (N : ℕ) (h : SU N) :
    let K : TopologicalSpace.PositiveCompacts (SU N) :=
      ⟨⟨Set.univ, isCompact_univ⟩, by simpa using Set.univ_nonempty (α := SU N)⟩
    Measure.map (fun u => u * h) (MeasureTheory.Measure.haarMeasure K) =
      MeasureTheory.Measure.haarMeasure K := by
  intro K
  set μ := MeasureTheory.Measure.haarMeasure K with hμ_def
  have hμ_univ : μ Set.univ = 1 := by
    simpa [K, hμ_def] using MeasureTheory.Measure.haarMeasure_self (K₀ := K)
  haveI : Measure.IsMulLeftInvariant (Measure.map (fun x => x * h) μ) :=
    isMulLeftInvariant_map_mul_right h
  have hmap_univ : Measure.map (fun x => x * h) μ Set.univ = 1 := by
    rw [Measure.map_apply (measurable_mul_const h) MeasurableSet.univ, preimage_univ]
    exact hμ_univ
  haveI : IsFiniteMeasureOnCompacts (Measure.map (fun x => x * h) μ) := by
    refine ⟨fun s _hs => ?_⟩
    exact (measure_mono (Set.subset_univ _)).trans_lt
      (hmap_univ.symm ▸ ENNReal.one_lt_top)
  have h_eq : Measure.map (fun x => x * h) μ =
      Measure.haarScalarFactor (Measure.map (fun x => x * h) μ) μ • μ :=
    Measure.isMulInvariant_eq_smul_of_compactSpace _ _
  have h_scalar : Measure.haarScalarFactor (Measure.map (fun x => x * h) μ) μ = 1 := by
    have h' : Measure.map (fun x => x * h) μ Set.univ =
        Measure.haarScalarFactor (Measure.map (fun x => x * h) μ) μ * μ Set.univ := by
      have hstep : Measure.map (fun x => x * h) μ Set.univ =
          (Measure.haarScalarFactor (Measure.map (fun x => x * h) μ) μ • μ) Set.univ :=
        congr_arg (fun ν => ν Set.univ) h_eq
      rw [hstep, Measure.coe_nnreal_smul_apply]
    rw [hμ_univ, hmap_univ] at h'
    simp at h'
    exact_mod_cast h'.symm
  rw [h_eq, h_scalar, one_smul]

/-- The Haar measure on `SU(N)` is invariant under left-right multiplication
`u ↦ a * u * b`.  This combines left invariance (`IsMulLeftInvariant`) with
right invariance (`haarMeasure_right_mul_invariant`). -/
lemma haarMeasure_left_right_mul_invariant (N : ℕ) (a b : SU N) :
    let K : TopologicalSpace.PositiveCompacts (SU N) :=
      ⟨⟨Set.univ, isCompact_univ⟩, by simpa using Set.univ_nonempty (α := SU N)⟩
    Measure.map (fun u => a * u * b) (MeasureTheory.Measure.haarMeasure K) =
      MeasureTheory.Measure.haarMeasure K := by
  intro K
  set μ := MeasureTheory.Measure.haarMeasure K with hμ_def
  haveI : Measure.IsMulLeftInvariant μ := Measure.isMulLeftInvariant_haarMeasure K
  have h_left : Measure.map (fun u => a * u) μ = μ :=
    Measure.IsMulLeftInvariant.map_mul_left_eq_self a
  have h_right : Measure.map (fun u => u * b) μ = μ :=
    haarMeasure_right_mul_invariant N b
  have hf : Measurable (fun u : SU N => a * u) := measurable_const.mul measurable_id
  have hg : Measurable (fun u : SU N => u * b) := measurable_mul_const b
  have h_map_comp : Measure.map (fun u => a * u * b) μ =
      Measure.map (fun u => u * b) (Measure.map (fun u => a * u) μ) := by
    rw [show (fun u => a * u * b) = (fun u => u * b) ∘ (fun u => a * u) from rfl]
    exact (Measure.map_map (g := fun u => u * b) (f := fun u => a * u) hg hf).symm
  rw [h_map_comp, h_left, h_right]

/-- The gauge transformation on a finite link configuration: for a gauge
parameter `g : Λ → SU N`, each link `(n, μ)` is conjugated as
`U(n, μ) ↦ g(n) * U(n, μ) * g(n + e_μ)⁻¹`. -/
def gaugeTransformConfig (N : ℕ) {Λ : Type} [DecidableEq Λ] [AddVector Λ]
    (sites : Finset Λ) (g : Λ → SU N)
    (cfg : FiniteLinkConfig N Λ sites) : FiniteLinkConfig N Λ sites :=
  fun ⟨(n, μ), _hn⟩ => g n * cfg ⟨(n, μ), _hn⟩ * (g (AddVector.addVector n μ))⁻¹

/-- The gauge transformation on a finite link configuration is measure-preserving
with respect to the product Haar measure.  Each link is independently
left-right-multiplied by `g(n)` and `g(n+e_μ)⁻¹`, and the Haar measure on
`SU(N)` is invariant under left-right multiplication
(`haarMeasure_left_right_mul_invariant`).  Since the product measure is a
product of independent Haar factors, and each factor is individually preserved,
the product is preserved (`measurePreserving_pi`). -/
lemma gaugeTransformConfig_measurePreserving
    (N : ℕ) {Λ : Type} [DecidableEq Λ] [AddVector Λ]
    (sites : Finset Λ) (g : Λ → SU N) :
    MeasurePreserving (gaugeTransformConfig N sites g)
      (productHaarMeasure N Λ sites) (productHaarMeasure N Λ sites) := by
  let K : TopologicalSpace.PositiveCompacts (SU N) :=
    ⟨⟨Set.univ, isCompact_univ⟩, by simpa using Set.univ_nonempty (α := SU N)⟩
  set ν : Measure (SU N) := MeasureTheory.Measure.haarMeasure K with hν_def
  have hμ : productHaarMeasure N Λ sites =
      Measure.pi (fun _ : FiniteLinkIndex Λ sites => ν) := by
    simp only [productHaarMeasure, ν, K, hν_def]
  have h_each : ∀ i : FiniteLinkIndex Λ sites,
      MeasurePreserving (fun u => g i.1.1 * u * (g (AddVector.addVector i.1.1 i.1.2))⁻¹) ν ν := by
    intro ⟨(n, μ), _hn⟩
    refine ⟨?_, ?_⟩
    · exact (measurable_const.mul measurable_id).mul measurable_const
    · exact haarMeasure_left_right_mul_invariant N (g n) (g (AddVector.addVector n μ))⁻¹
  have h := measurePreserving_pi (fun _ : FiniteLinkIndex Λ sites => ν) (fun _ => ν)
    (f := fun i => fun u => g i.1.1 * u * (g (AddVector.addVector i.1.1 i.1.2))⁻¹)
    (by intro i; exact h_each i)
  rw [hμ]
  convert h using 1
  ext cfg i
  rfl

/-- For `sites = Finset.univ`, `extendLinkVariable` at link `(n, μ)` simply
extracts `cfg ⟨(n, μ), Finset.mem_univ n⟩` (the `if` branch is always taken). -/
lemma extendLinkVariable_univ (N : ℕ) {Λ : Type} [DecidableEq Λ] [Fintype Λ]
    (cfg : FiniteLinkConfig N Λ Finset.univ) (n : Λ) (μ : Fin 4) :
    (extendLinkVariable N Λ Finset.univ cfg).value n μ = cfg ⟨(n, μ), Finset.mem_univ n⟩ := by
  change (if h : n ∈ Finset.univ then cfg ⟨(n, μ), h⟩ else 1) = cfg ⟨(n, μ), Finset.mem_univ n⟩
  rw [dif_pos (Finset.mem_univ n)]

/-- The gauge transformation commutes with `extendLinkVariable` when
`sites = Finset.univ`: extending the gauge-transformed config equals the
gauge transformation of the extended link variable.  This holds because
every site is in `Finset.univ`, so the `if n ∈ sites` branches always fire. -/
lemma extendLinkVariable_gaugeTransformConfig
    (N : ℕ) {Λ : Type} [DecidableEq Λ] [AddVector Λ] [Fintype Λ]
    (g : Λ → SU N) (cfg : FiniteLinkConfig N Λ Finset.univ) :
    extendLinkVariable N Λ Finset.univ (gaugeTransformConfig N Finset.univ g cfg) =
      gaugeTransformLinkVariable N g (extendLinkVariable N Λ Finset.univ cfg) := by
  ext n μ
  dsimp only [extendLinkVariable, gaugeTransformConfig, gaugeTransformLinkVariable]
  rw [dif_pos (Finset.mem_univ n), dif_pos (Finset.mem_univ n)]

/-- The reflection map on the full link-variable group is measure-preserving
with respect to the product Haar measure.

The reflection `θ` acts by `(θU)(n, μ) = U(θn, μ)⁻¹` for time-like links (μ = 0)
and `(θU)(n, μ) = U(θn, μ)` for spatial links (μ ≠ 0).  This is a composition of:
1. An index permutation `(n, μ) ↦ (θn, μ)` — preserves the product measure since
   all factors are identical.
2. Componentwise inversion on time-like links — preserves the product measure
   since the Haar measure on `SU(N)` is inversion-invariant
   (`haarMeasure_inv_invariant`).

Both steps preserve the product Haar measure, so the composition does too.

This is the key measure-theoretic ingredient for the character-orthogonality
approach to closing `transferMatrixPositivity_axiom`: it justifies the change
of variables `U ↦ θU` in the reflection-positivity integral.

The reflection `θ` acts by `(θU)(n, μ) = U(θn, μ)⁻¹` for time-like links (μ = 0)
and `(θU)(n, μ) = U(θn, μ)` for spatial links (μ ≠ 0).  This is a composition of:
1. An index permutation `(n, μ) ↦ (θn, μ)` — preserves the product measure since
   all factors are identical (`measurePreserving_piCongrLeft`).
2. Componentwise inversion on time-like links — preserves the product measure
   since the Haar measure on `SU(N)` is inversion-invariant
   (`haarMeasure_inv_invariant`).

Both steps preserve the product Haar measure, so the composition does too
(`MeasurePreserving.comp`).

This is the key measure-theoretic ingredient for the character-orthogonality
approach to closing `transferMatrixPositivity_axiom`: it justifies the change
of variables `U ↦ θU` in the reflection-positivity integral.

The hypothesis `hsites : ∀ n, n ∈ sites → reflectSite n ∈ sites` is necessary:
since `ReflectSite.involution` makes `reflectSite` involutive, it makes the
reflection a bijection on `sites`, so the index permutation is a genuine
permutation of `FiniteLinkIndex Λ sites`.  Without it, an out-of-`sites`
reflection would collapse a Haar-distributed degree of freedom to the constant
`1` (via `extendLinkVariable`'s default), which does *not* preserve the product
Haar measure. -/
lemma reflectLinkVariable_measurePreserving
    (N : ℕ) {Λ : Type} [DecidableEq Λ] [ReflectSite Λ]
    (sites : Finset Λ)
    (hsites : ∀ n, n ∈ sites → ReflectSite.reflectSite n ∈ sites) :
    MeasurePreserving
      (fun (cfg : FiniteLinkConfig N Λ sites) =>
        restrictLinkVariable N Λ sites
          (reflectLinkVariable N (extendLinkVariable N Λ sites cfg)))
      (productHaarMeasure N Λ sites) (productHaarMeasure N Λ sites) := by
  -- The positive compact set used to build the Haar measure on SU(N),
  -- matching the one in `productHaarMeasure`.
  let K : TopologicalSpace.PositiveCompacts (SU N) :=
    ⟨⟨Set.univ, isCompact_univ⟩, by simpa using Set.univ_nonempty (α := SU N)⟩
  set ν : Measure (SU N) := MeasureTheory.Measure.haarMeasure K with hν_def
  -- `productHaarMeasure` is the product of identical Haar factors.
  have hμ : productHaarMeasure N Λ sites =
      Measure.pi (fun _ : FiniteLinkIndex Λ sites => ν) := by
    simp only [productHaarMeasure, ν, K, hν_def]
  -- The index permutation `(n, μ) ↦ (reflectSite n, μ)` on `FiniteLinkIndex`.
  -- It is involutive (hence a bijection) thanks to `ReflectSite.involution`.
  let perm : FiniteLinkIndex Λ sites ≃ FiniteLinkIndex Λ sites :=
    { toFun := fun ⟨⟨n, μ⟩, hn⟩ => ⟨⟨ReflectSite.reflectSite n, μ⟩, hsites n hn⟩
      invFun := fun ⟨⟨n, μ⟩, hn⟩ => ⟨⟨ReflectSite.reflectSite n, μ⟩, hsites n hn⟩
      left_inv := fun ⟨⟨n, μ⟩, hn⟩ => by
        simp only [ReflectSite.involution]
        rfl
      right_inv := fun ⟨⟨n, μ⟩, hn⟩ => by
        simp only [ReflectSite.involution]
        rfl }
  -- Step 1: the index permutation preserves the product measure.
  -- `MeasurableEquiv.piCongrLeft (fun _ => SU N) perm.symm` acts, with the
  -- constant fibre `SU N`, as `cfg ↦ fun i => cfg (perm i)`.
  have h_perm : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ => SU N) perm.symm)
      (Measure.pi (fun _ : FiniteLinkIndex Λ sites => ν))
      (Measure.pi (fun _ : FiniteLinkIndex Λ sites => ν)) :=
    measurePreserving_piCongrLeft (fun _ => ν) perm.symm
  -- With the constant fibre `SU N`, the `piCongrLeft` application simplifies
  -- to `cfg (perm i)` (the dependent transport is over a constant motive).
  have h_perm_eq : ∀ (cfg : FiniteLinkConfig N Λ sites) (i : FiniteLinkIndex Λ sites),
      MeasurableEquiv.piCongrLeft (fun _ => SU N) perm.symm cfg i = cfg (perm i) := by
    intro cfg i
    have h := @MeasurableEquiv.piCongrLeft_apply_apply _ _ perm.symm
      (fun _ => SU N) _ cfg (perm i)
    rwa [Equiv.symm_apply_apply] at h
  -- product measure, since each factor is either `id` (spatial) or `Inv.inv`
  -- (time-like), and the Haar measure is inversion-invariant.
  have h_inv : MeasurePreserving
      (fun (cfg : FiniteLinkConfig N Λ sites) (i : FiniteLinkIndex Λ sites) =>
        if i.1.2 = 0 then (cfg i)⁻¹ else cfg i)
      (Measure.pi (fun _ : FiniteLinkIndex Λ sites => ν))
      (Measure.pi (fun _ : FiniteLinkIndex Λ sites => ν)) := by
    have h := measurePreserving_pi (fun _ : FiniteLinkIndex Λ sites => ν) (fun _ => ν)
      (f := fun i => if i.1.2 = 0 then (Inv.inv : SU N → SU N) else id)
      (by
        intro i
        by_cases h : i.1.2 = 0
        · simp only [h, ↓reduceIte]
          exact ⟨continuous_inv.measurable, haarMeasure_inv_invariant N⟩
        · simp only [h, ↓reduceIte]
          exact MeasurePreserving.id ν)
    convert h using 1
    funext cfg i
    by_cases h : i.1.2 = 0 <;> simp only [h, ↓reduceIte, Function.id_def]
  -- Compose the two measure-preserving maps.
  have h_comp := h_inv.comp h_perm
  -- The stated map equals the composition: at `(n, μ)` with `n ∈ sites`,
  -- `hsites` forces `reflectSite n ∈ sites`, so the out-of-`sites` default
  -- never triggers, and the map reduces to the permutation followed by the
  -- componentwise (id/inv) operation.
  have h_eq :
      (fun (cfg : FiniteLinkConfig N Λ sites) =>
        restrictLinkVariable N Λ sites
          (reflectLinkVariable N (extendLinkVariable N Λ sites cfg))) =
      (fun cfg i =>
        if i.1.2 = 0 then (MeasurableEquiv.piCongrLeft (fun _ => SU N) perm.symm cfg i)⁻¹
        else MeasurableEquiv.piCongrLeft (fun _ => SU N) perm.symm cfg i) := by
    funext cfg i
    rcases i with ⟨⟨n, μ⟩, hn⟩
    simp only [restrictLinkVariable, reflectLinkVariable, extendLinkVariable,
      dif_pos (hsites n hn)]
    rw [h_perm_eq cfg ⟨(n, μ), hn⟩]
    rfl
  rw [hμ, h_eq]
  exact h_comp

/-- The reflection maps link configs on `sourceSites` to link configs on `targetSites`
in a measure-preserving way, when `reflectSite` gives a bijection between the two
site sets (via `h_reflect` and `h_reflect_inv`).

This generalizes `reflectLinkVariable_measurePreserving` (which is the special case
`sourceSites = targetSites = sites` with `h_reflect = h_reflect_inv = hsites`).

The key application is the change of variables `U⁻ ↦ V⁺ = reflect(U⁻)` in the
transfer-matrix integral (step (b) of the `transferMatrixPositivity_axiom` closure
plan), where `sourceSites = negativeSites` and `targetSites = positiveSites`.

The proof is the same two-step composition as `reflectLinkVariable_measurePreserving`:
1. An index bijection `FiniteLinkIndex Λ sourceSites ≃ FiniteLinkIndex Λ targetSites`
   via `(n, μ) ↦ (reflectSite n, μ)` — preserves the product measure since all factors
   are identical (`measurePreserving_piCongrLeft`).
2. Componentwise inversion on time-like links — preserves the product measure
   since the Haar measure on `SU(N)` is inversion-invariant (`haarMeasure_inv_invariant`). -/
lemma reflectLinkVariable_measurePreserving_between
    (N : ℕ) {Λ : Type} [DecidableEq Λ] [ReflectSite Λ]
    (sourceSites targetSites : Finset Λ)
    (h_reflect : ∀ n, n ∈ sourceSites → ReflectSite.reflectSite n ∈ targetSites)
    (h_reflect_inv : ∀ n, n ∈ targetSites → ReflectSite.reflectSite n ∈ sourceSites) :
    MeasurePreserving
      (fun (cfg : FiniteLinkConfig N Λ sourceSites) =>
        restrictLinkVariable N Λ targetSites
          (reflectLinkVariable N (extendLinkVariable N Λ sourceSites cfg)))
      (productHaarMeasure N Λ sourceSites) (productHaarMeasure N Λ targetSites) := by
  let K : TopologicalSpace.PositiveCompacts (SU N) :=
    ⟨⟨Set.univ, isCompact_univ⟩, by simpa using Set.univ_nonempty (α := SU N)⟩
  set ν : Measure (SU N) := MeasureTheory.Measure.haarMeasure K with hν_def
  have hμ_src : productHaarMeasure N Λ sourceSites =
      Measure.pi (fun _ : FiniteLinkIndex Λ sourceSites => ν) := by
    simp only [productHaarMeasure, ν, K, hν_def]
  have hμ_tgt : productHaarMeasure N Λ targetSites =
      Measure.pi (fun _ : FiniteLinkIndex Λ targetSites => ν) := by
    simp only [productHaarMeasure, ν, K, hν_def]
  -- The index bijection via reflection
  let perm : FiniteLinkIndex Λ sourceSites ≃ FiniteLinkIndex Λ targetSites :=
    { toFun := fun ⟨⟨n, μ⟩, hn⟩ => ⟨⟨ReflectSite.reflectSite n, μ⟩, h_reflect n hn⟩
      invFun := fun ⟨⟨n, μ⟩, hn⟩ => ⟨⟨ReflectSite.reflectSite n, μ⟩, h_reflect_inv n hn⟩
      left_inv := fun ⟨⟨n, μ⟩, hn⟩ => by
        simp only [ReflectSite.involution]
        rfl
      right_inv := fun ⟨⟨n, μ⟩, hn⟩ => by
        simp only [ReflectSite.involution]
        rfl }
  -- Step 1: the index permutation preserves the product measure.
  have h_perm : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ => SU N) perm)
      (Measure.pi (fun _ : FiniteLinkIndex Λ sourceSites => ν))
      (Measure.pi (fun _ : FiniteLinkIndex Λ targetSites => ν)) :=
    measurePreserving_piCongrLeft (fun _ => ν) perm
  -- With the constant fibre `SU N`, `piCongrLeft perm` acts as `cfg (perm.symm i)`.
  have h_perm_eq : ∀ (cfg : FiniteLinkConfig N Λ sourceSites) (i : FiniteLinkIndex Λ targetSites),
      MeasurableEquiv.piCongrLeft (fun _ => SU N) perm cfg i = cfg (perm.symm i) := by
    intro cfg i
    have h := @MeasurableEquiv.piCongrLeft_apply_apply _ _ perm
      (fun _ => SU N) _ cfg (perm.symm i)
    rw [Equiv.apply_symm_apply] at h
    exact h
  -- Step 2: componentwise inversion on time-like links preserves the product measure.
  have h_inv : MeasurePreserving
      (fun (cfg : FiniteLinkConfig N Λ targetSites) (i : FiniteLinkIndex Λ targetSites) =>
        if i.1.2 = 0 then (cfg i)⁻¹ else cfg i)
      (Measure.pi (fun _ : FiniteLinkIndex Λ targetSites => ν))
      (Measure.pi (fun _ : FiniteLinkIndex Λ targetSites => ν)) := by
    have h := measurePreserving_pi (fun _ : FiniteLinkIndex Λ targetSites => ν) (fun _ => ν)
      (f := fun i => if i.1.2 = 0 then (Inv.inv : SU N → SU N) else id)
      (by
        intro i
        by_cases h : i.1.2 = 0
        · simp only [h, ↓reduceIte]
          exact ⟨continuous_inv.measurable, haarMeasure_inv_invariant N⟩
        · simp only [h, ↓reduceIte]
          exact MeasurePreserving.id ν)
    convert h using 1
    funext cfg i
    by_cases h : i.1.2 = 0 <;> simp only [h, ↓reduceIte, Function.id_def]
  -- Compose the two measure-preserving maps.
  have h_comp := h_inv.comp h_perm
  -- The stated map equals the composition.
  have h_eq :
      (fun (cfg : FiniteLinkConfig N Λ sourceSites) =>
        restrictLinkVariable N Λ targetSites
          (reflectLinkVariable N (extendLinkVariable N Λ sourceSites cfg))) =
      (fun cfg i =>
        if i.1.2 = 0 then (MeasurableEquiv.piCongrLeft (fun _ => SU N) perm cfg i)⁻¹
        else MeasurableEquiv.piCongrLeft (fun _ => SU N) perm cfg i) := by
    funext cfg i
    rcases i with ⟨⟨n, μ⟩, hn⟩
    simp only [restrictLinkVariable, reflectLinkVariable, extendLinkVariable,
      dif_pos (h_reflect_inv n hn)]
    rw [h_perm_eq cfg ⟨(n, μ), hn⟩]
    rfl
  rw [hμ_src, hμ_tgt, h_eq]
  exact h_comp

#print axioms reflectLinkVariable_measurePreserving_between

/-- The partition function for a finite lattice with Wilson action. --/
noncomputable def partitionFunctionFinite (N : ℕ) (β : ℝ) (Λ : Type) [DecidableEq Λ] [AddVector Λ]
    (sites : Finset Λ) : ℝ :=
  ∫ (U : FiniteLinkConfig N Λ sites), Real.exp (-β * wilsonActionFiniteConfig N β Λ sites U)
    ∂ productHaarMeasure N Λ sites

/-- The expectation value (Gibbs average) of an observable on a finite lattice. -/
noncomputable def gibbsExpectation (N : ℕ) (β : ℝ) (Λ : Type) [DecidableEq Λ] [AddVector Λ]
    (sites : Finset Λ) (f : LinkVariable (SU N) Λ → ℝ) : ℝ :=
  let Z := partitionFunctionFinite N β Λ sites
  let μ₀ := productHaarMeasure N Λ sites
  (∫ (U : FiniteLinkConfig N Λ sites), f (extendLinkVariable N Λ sites U) *
    Real.exp (-β * wilsonActionFiniteConfig N β Λ sites U) ∂ μ₀) / Z

lemma partitionFunctionFinite_pos (N : ℕ) (β : ℝ) (Λ : Type) [DecidableEq Λ] [AddVector Λ]
    (sites : Finset Λ) : partitionFunctionFinite N β Λ sites > 0 := by
  haveI : IsProbabilityMeasure (productHaarMeasure N Λ sites) :=
    ⟨productHaarMeasure_total_volume N Λ sites⟩
  haveI : NeZero (productHaarMeasure N Λ sites) := by
    refine ⟨by
      intro hzero
      have hzero_univ : productHaarMeasure N Λ sites Set.univ = 0 := by simpa [hzero] using rfl
      rw [productHaarMeasure_total_volume N Λ sites] at hzero_univ
      exact one_ne_zero hzero_univ⟩
  by_cases h : sites = ∅
  · subst h
    dsimp [partitionFunctionFinite, wilsonActionFiniteConfig]
    simp [wilsonActionFinite]
  · dsimp [partitionFunctionFinite]
    apply integral_exp_pos
    have hmeas_exp : Measurable (λ (U : FiniteLinkConfig N Λ sites) =>
      Real.exp (-β * wilsonActionFiniteConfig N β Λ sites U)) := by
      refine Real.measurable_exp.comp
        (Measurable.const_mul (measurable_wilsonActionFiniteConfig N β Λ sites) (-β))
    have h_bound : ∀ U : FiniteLinkConfig N Λ sites,
      0 ≤ Real.exp (-β * wilsonActionFiniteConfig N β Λ sites U) ∧
      Real.exp (-β * wilsonActionFiniteConfig N β Λ sites U) ≤ 1 := by
      intro U
      have h_nonpos : -β * wilsonActionFiniteConfig N β Λ sites U ≤ 0 := by
        have h_factor_nonneg : ∀ (n : Λ) (μ ν : Fin 4),
            0 ≤ 1 - (1 / (N : ℝ)) * ((trace ((plaquetteProduct N (extendLinkVariable N Λ sites U) n μ ν :
              Matrix (Fin N) (Fin N) ℂ))).re) := by
          intro n μ ν
          let tr := (trace ((plaquetteProduct N (extendLinkVariable N Λ sites U) n μ ν :
            Matrix (Fin N) (Fin N) ℂ))).re
          have h_bound_tr : |tr| ≤ N :=
            trace_re_bound N (plaquetteProduct N (extendLinkVariable N Λ sites U) n μ ν)
          have h_tr_upper : tr ≤ N := by linarith [abs_le.mp h_bound_tr]
          have h_tr_lower : -N ≤ tr := by linarith [abs_le.mp h_bound_tr]
          by_cases hN0 : (N : ℝ) = 0
          · simp [hN0, tr]
          · have hpos : 0 < (N : ℝ) := by
              have hNpos' : 0 < N := Nat.pos_of_ne_zero (by
                intro hzero
                apply hN0
                exact_mod_cast hzero)
              exact_mod_cast hNpos'
            have h_div_upper : (1 / (N : ℝ)) * tr ≤ 1 := by
              have h_mul : ((1 / (N : ℝ)) * tr) * (N : ℝ) ≤ 1 * (N : ℝ) := by
                calc
                  ((1 / (N : ℝ)) * tr) * (N : ℝ) = tr := by field_simp [hN0]
                  _ ≤ N := h_tr_upper
                  _ = 1 * (N : ℝ) := by norm_num
              exact (mul_le_mul_iff_of_pos_right hpos).mp h_mul
            have h_div_lower : -1 ≤ (1 / (N : ℝ)) * tr := by
              have h_mul : (-1 : ℝ) * (N : ℝ) ≤ ((1 / (N : ℝ)) * tr) * (N : ℝ) := by
                calc
                  (-1 : ℝ) * (N : ℝ) = -N := by ring
                  _ ≤ tr := h_tr_lower
                  _ = ((1 / (N : ℝ)) * tr) * (N : ℝ) := by field_simp [hN0]
              exact (mul_le_mul_iff_of_pos_right hpos).mp h_mul
            linarith
        have h_sum_nonneg : 0 ≤ ∑ n ∈ sites, ∑ μ : Fin 4, ∑ ν : Fin 4,
          (1 - (1 / (N : ℝ)) * ((trace ((plaquetteProduct N (extendLinkVariable N Λ sites U) n μ ν :
            Matrix (Fin N) (Fin N) ℂ))).re)) := by
          refine Finset.sum_nonneg (λ n hn => Finset.sum_nonneg (λ μ hμ => Finset.sum_nonneg (λ ν hν => ?_)))
          exact h_factor_nonneg n μ ν
        have h_wilson_eq : wilsonActionFiniteConfig N β Λ sites U = β *
          (∑ n ∈ sites, ∑ μ : Fin 4, ∑ ν : Fin 4,
            (1 - (1 / (N : ℝ)) * ((trace ((plaquetteProduct N (extendLinkVariable N Λ sites U) n μ ν :
              Matrix (Fin N) (Fin N) ℂ))).re))) := by
          dsimp [wilsonActionFiniteConfig, wilsonActionFinite, plaquetteContribution]
          calc
            ∑ n ∈ sites, ∑ μ : Fin 4, ∑ ν : Fin 4,
              β * ((1 : ℝ) - (1 / (N : ℝ)) * ((trace ((plaquetteProduct N (extendLinkVariable N Λ sites U) n μ ν :
                Matrix (Fin N) (Fin N) ℂ))).re))
                = β * (∑ n ∈ sites, ∑ μ : Fin 4, ∑ ν : Fin 4,
                    ((1 : ℝ) - (1 / (N : ℝ)) * ((trace ((plaquetteProduct N (extendLinkVariable N Λ sites U) n μ ν :
                      Matrix (Fin N) (Fin N) ℂ))).re))) := by
              simp_rw [Finset.mul_sum]
            _ = β * (∑ n ∈ sites, ∑ μ : Fin 4, ∑ ν : Fin 4,
                (1 - (1 / (N : ℝ)) * ((trace ((plaquetteProduct N (extendLinkVariable N Λ sites U) n μ ν :
                  Matrix (Fin N) (Fin N) ℂ))).re))) := rfl
        rw [h_wilson_eq]
        have h_sq_nonpos : -(β^2) ≤ 0 := by nlinarith [sq_nonneg β]
        set S := (∑ n ∈ sites, ∑ μ : Fin 4, ∑ ν : Fin 4,
          (1 - (1 / (N : ℝ)) * ((trace ((plaquetteProduct N (extendLinkVariable N Λ sites U) n μ ν :
            Matrix (Fin N) (Fin N) ℂ))).re))) with hS
        have h_mul_eq : -β * (β * S) = -(β^2) * S := by ring
        rw [h_mul_eq]
        exact mul_nonpos_of_nonpos_of_nonneg h_sq_nonpos h_sum_nonneg
      have h_exp_le_one : Real.exp (-β * wilsonActionFiniteConfig N β Λ sites U) ≤ 1 :=
        (Real.exp_le_one_iff.mpr h_nonpos)
      have h_exp_nonneg : 0 ≤ Real.exp (-β * wilsonActionFiniteConfig N β Λ sites U) :=
        (Real.exp_pos _).le
      exact ⟨h_exp_nonneg, h_exp_le_one⟩
    have h_int : Integrable (λ U : FiniteLinkConfig N Λ sites =>
      Real.exp (-β * wilsonActionFiniteConfig N β Λ sites U)) (productHaarMeasure N Λ sites) := by
      refine integrable_of_le_of_le hmeas_exp.aestronglyMeasurable
        (Filter.Eventually.of_forall (λ U => (h_bound U).1))
        (Filter.Eventually.of_forall (λ U => (h_bound U).2))
        (integrable_const (0 : ℝ))
        (integrable_const (1 : ℝ))
    exact h_int

lemma gibbsExpectation_pos (N : ℕ) (β : ℝ) (Λ : Type) [DecidableEq Λ] [AddVector Λ]
    (sites : Finset Λ) (F : LinkVariable (SU N) Λ → ℝ) (hF : ∀ U, F U ≥ 0) :
    gibbsExpectation N β Λ sites F ≥ 0 := by
  dsimp [gibbsExpectation]
  refine div_nonneg ?_ (le_of_lt (partitionFunctionFinite_pos N β Λ sites))
  apply integral_nonneg
  intro U
  exact mul_nonneg (hF (extendLinkVariable N Λ sites U)) (le_of_lt (Real.exp_pos _))

lemma gibbsExpectation_normalization (N : ℕ) (β : ℝ) (Λ : Type) [DecidableEq Λ] [AddVector Λ]
    (sites : Finset Λ) : gibbsExpectation N β Λ sites (λ _ => 1) = 1 := by
  dsimp [gibbsExpectation, partitionFunctionFinite]
  simp only [one_mul]
  exact div_self (ne_of_gt (partitionFunctionFinite_pos N β Λ sites))

lemma gibbsExpectation_linear (N : ℕ) (β : ℝ) (Λ : Type) [DecidableEq Λ] [AddVector Λ]
    (sites : Finset Λ) (a b : ℝ) (F G : LinkVariable (SU N) Λ → ℝ)
    (hF : Integrable (λ (U : FiniteLinkConfig N Λ sites) => F (extendLinkVariable N Λ sites U) *
      Real.exp (-β * wilsonActionFiniteConfig N β Λ sites U)) (productHaarMeasure N Λ sites))
    (hG : Integrable (λ (U : FiniteLinkConfig N Λ sites) => G (extendLinkVariable N Λ sites U) *
      Real.exp (-β * wilsonActionFiniteConfig N β Λ sites U)) (productHaarMeasure N Λ sites)) :
    gibbsExpectation N β Λ sites (λ U => a * F U + b * G U) =
    a * gibbsExpectation N β Λ sites F + b * gibbsExpectation N β Λ sites G := by
  dsimp [gibbsExpectation]
  set Z := partitionFunctionFinite N β Λ sites with hZ
  set μ₀ := productHaarMeasure N Λ sites with hμ₀
  have hZ_pos : Z ≠ 0 := by linarith [partitionFunctionFinite_pos N β Λ sites]
  -- Expand the numerator
  have h_num : (∫ (U : FiniteLinkConfig N Λ sites), ((a * F (extendLinkVariable N Λ sites U) + b * G (extendLinkVariable N Λ sites U)) *
    Real.exp (-β * wilsonActionFiniteConfig N β Λ sites U)) ∂ μ₀) =
    a * (∫ (U : FiniteLinkConfig N Λ sites), (F (extendLinkVariable N Λ sites U) * Real.exp (-β * wilsonActionFiniteConfig N β Λ sites U)) ∂ μ₀) +
    b * (∫ (U : FiniteLinkConfig N Λ sites), (G (extendLinkVariable N Λ sites U) * Real.exp (-β * wilsonActionFiniteConfig N β Λ sites U)) ∂ μ₀) := by
    calc
      (∫ U, ((a * F (extendLinkVariable N Λ sites U) + b * G (extendLinkVariable N Λ sites U)) *
        Real.exp (-β * wilsonActionFiniteConfig N β Λ sites U)) ∂ μ₀)
          = (∫ U, (a * F (extendLinkVariable N Λ sites U) * Real.exp (-β * wilsonActionFiniteConfig N β Λ sites U) +
              b * G (extendLinkVariable N Λ sites U) * Real.exp (-β * wilsonActionFiniteConfig N β Λ sites U)) ∂ μ₀) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (λ U => ?_))
        ring
      _ = (∫ U, a * F (extendLinkVariable N Λ sites U) * Real.exp (-β * wilsonActionFiniteConfig N β Λ sites U) ∂ μ₀) +
          (∫ U, b * G (extendLinkVariable N Λ sites U) * Real.exp (-β * wilsonActionFiniteConfig N β Λ sites U) ∂ μ₀) := by
        refine integral_add ?_ ?_
        · have hF_int : Integrable (λ U : FiniteLinkConfig N Λ sites =>
            a * F (extendLinkVariable N Λ sites U) * Real.exp (-β * wilsonActionFiniteConfig N β Λ sites U)) μ₀ := by
            simpa [mul_assoc] using hF.const_mul a
          exact hF_int
        · have hG_int : Integrable (λ U : FiniteLinkConfig N Λ sites =>
            b * G (extendLinkVariable N Λ sites U) * Real.exp (-β * wilsonActionFiniteConfig N β Λ sites U)) μ₀ := by
            simpa [mul_assoc] using hG.const_mul b
          exact hG_int
      _ = a * (∫ U, F (extendLinkVariable N Λ sites U) * Real.exp (-β * wilsonActionFiniteConfig N β Λ sites U) ∂ μ₀) +
          b * (∫ U, G (extendLinkVariable N Λ sites U) * Real.exp (-β * wilsonActionFiniteConfig N β Λ sites U) ∂ μ₀) := by
        simp [integral_const_mul, mul_assoc]
  calc
    (∫ U, ((a * F (extendLinkVariable N Λ sites U) + b * G (extendLinkVariable N Λ sites U)) *
      Real.exp (-β * wilsonActionFiniteConfig N β Λ sites U)) ∂ μ₀) / Z
        = (a * (∫ U, (F (extendLinkVariable N Λ sites U) * Real.exp (-β * wilsonActionFiniteConfig N β Λ sites U)) ∂ μ₀) +
            b * (∫ U, (G (extendLinkVariable N Λ sites U) * Real.exp (-β * wilsonActionFiniteConfig N β Λ sites U)) ∂ μ₀)) / Z := by
      rw [h_num]
    _ = a * ((∫ U, (F (extendLinkVariable N Λ sites U) * Real.exp (-β * wilsonActionFiniteConfig N β Λ sites U)) ∂ μ₀) / Z) +
        b * ((∫ U, (G (extendLinkVariable N Λ sites U) * Real.exp (-β * wilsonActionFiniteConfig N β Λ sites U)) ∂ μ₀) / Z) := by
      ring
    _ = a * gibbsExpectation N β Λ sites F + b * gibbsExpectation N β Λ sites G := by
      dsimp [gibbsExpectation, Z, μ₀]

section Z4SiteAliases
-- Z4Site-specific aliases for backward compatibility

abbrev FiniteLinkIndexZ4 (sites : Finset Z4Site) : Type := FiniteLinkIndex Z4Site sites
abbrev FiniteLinkConfigZ4 (N : ℕ) (sites : Finset Z4Site) : Type := FiniteLinkConfig N Z4Site sites

noncomputable def productHaarMeasureZ4 (N : ℕ) (sites : Finset Z4Site) : Measure (FiniteLinkConfigZ4 N sites) :=
  productHaarMeasure N Z4Site sites

noncomputable def extendLinkVariableZ4 (N : ℕ) (sites : Finset Z4Site) (U : FiniteLinkConfigZ4 N sites) :
    LinkVariable (SU N) Z4Site :=
  extendLinkVariable N Z4Site sites U

noncomputable def restrictLinkVariableZ4 (N : ℕ) (sites : Finset Z4Site) (U : LinkVariable (SU N) Z4Site) :
    FiniteLinkConfigZ4 N sites :=
  restrictLinkVariable N Z4Site sites U

noncomputable def wilsonActionFiniteConfigZ4 (N : ℕ) (β : ℝ) (sites : Finset Z4Site) (cfg : FiniteLinkConfigZ4 N sites) : ℝ :=
  wilsonActionFiniteConfig N β Z4Site sites cfg

noncomputable def partitionFunctionFiniteZ4 (N : ℕ) (β : ℝ) (sites : Finset Z4Site) : ℝ :=
  partitionFunctionFinite N β Z4Site sites

noncomputable def gibbsExpectationZ4 (N : ℕ) (β : ℝ) (sites : Finset Z4Site) (f : LinkVariable (SU N) Z4Site → ℝ) : ℝ :=
  gibbsExpectation N β Z4Site sites f

lemma measurable_extendLinkVariableZ4 (N : ℕ) (sites : Finset Z4Site) :
    Measurable (extendLinkVariableZ4 N sites) :=
  measurable_extendLinkVariable N Z4Site sites

lemma measurable_wilsonActionFiniteConfigZ4 (N : ℕ) (β : ℝ) (sites : Finset Z4Site) :
    Measurable (wilsonActionFiniteConfigZ4 N β sites) :=
  measurable_wilsonActionFiniteConfig N β Z4Site sites

lemma productHaarMeasureZ4_total_volume (N : ℕ) (sites : Finset Z4Site) :
    productHaarMeasureZ4 N sites (Set.univ : Set (FiniteLinkConfigZ4 N sites)) = 1 :=
  productHaarMeasure_total_volume N Z4Site sites

lemma productHaarMeasureZ4_isFiniteMeasure (N : ℕ) (sites : Finset Z4Site) :
    IsFiniteMeasure (productHaarMeasureZ4 N sites) :=
  productHaarMeasure_isFiniteMeasure N Z4Site sites

lemma partitionFunctionFiniteZ4_pos (N : ℕ) (β : ℝ) (sites : Finset Z4Site) :
    partitionFunctionFiniteZ4 N β sites > 0 :=
  partitionFunctionFinite_pos N β Z4Site sites

lemma gibbsExpectationZ4_pos (N : ℕ) (β : ℝ) (sites : Finset Z4Site) (F : LinkVariable (SU N) Z4Site → ℝ)
    (hF : ∀ U, F U ≥ 0) : gibbsExpectationZ4 N β sites F ≥ 0 :=
  gibbsExpectation_pos N β Z4Site sites F hF

lemma gibbsExpectationZ4_normalization (N : ℕ) (β : ℝ) (sites : Finset Z4Site) :
    gibbsExpectationZ4 N β sites (λ _ => 1) = 1 :=
  gibbsExpectation_normalization N β Z4Site sites

lemma gibbsExpectationZ4_linear (N : ℕ) (β : ℝ) (sites : Finset Z4Site) (a b : ℝ)
    (F G : LinkVariable (SU N) Z4Site → ℝ)
    (hF : Integrable (λ (U : FiniteLinkConfigZ4 N sites) => F (extendLinkVariableZ4 N sites U) *
      Real.exp (-β * wilsonActionFiniteConfigZ4 N β sites U)) (productHaarMeasureZ4 N sites))
    (hG : Integrable (λ (U : FiniteLinkConfigZ4 N sites) => G (extendLinkVariableZ4 N sites U) *
      Real.exp (-β * wilsonActionFiniteConfigZ4 N β sites U)) (productHaarMeasureZ4 N sites)) :
    gibbsExpectationZ4 N β sites (λ U => a * F U + b * G U) =
    a * gibbsExpectationZ4 N β sites F + b * gibbsExpectationZ4 N β sites G :=
  gibbsExpectation_linear N β Z4Site sites a b F G hF hG

/--
  Reflection positivity for the Wilson action on a finite ℤ⁴ lattice.
  
  This lemma proves that ⟨f · θ(f)⟩ ≥ 0 for any observable f depending on
  the link variables. It is a key part of the Osterwalder-Seiler reconstruction
  theorem.
  
  ⚠️ **Known limitation**: The hypothesis `hadd : ∀ n, n ∈ sites → addVector n 0 ∈ sites`
  forces the finite lattice `sites` to be empty (see `docs/hadd_issue.md` for details).
  The proof exploits this: the `sites = ∅` case is handled directly, while the
  nonempty case leads to a contradiction via `hadd` and the finiteness of `sites`.
  
  **Current status**: This lemma is a valid Lean proof (builds successfully) but is
  mathematically vacuous for nonempty finite lattices. A complete reflection positivity
  proof requires periodic boundary conditions (Option A in `docs/hadd_issue.md`), which
  would make `hadd` satisfiable for finite lattices and require a genuine Osterwalder-Seiler
  factorization argument.
  
  **Planned fix**: Implement `addVector` with modular arithmetic (wrapping around a finite
  time circle of size T), and provide the full Osterwalder-Seiler decomposition of the
  Wilson action into positive-time, negative-time, and interface parts.
  -/
lemma gibbsExpectationZ4_reflection_positive (N : ℕ) (β : ℝ) (sites : Finset Z4Site)
    (hadd : ∀ n, n ∈ sites → addVector n 0 ∈ sites)
    (hsites : ∀ n, n ∈ sites → reflectSite n ∈ sites) (f : LinkVariable (SU N) Z4Site → ℝ) :
    gibbsExpectationZ4 N β sites (λ U => f U * f (reflectLinkVariableZ4 N U)) ≥ 0 := by
  dsimp [gibbsExpectationZ4]
  let μ₀ := productHaarMeasureZ4 N sites
  let Z := partitionFunctionFiniteZ4 N β sites
  have hZ_pos : Z > 0 := partitionFunctionFiniteZ4_pos N β sites
  let F : FiniteLinkConfigZ4 N sites → ℝ := λ cfg =>
    f (extendLinkVariableZ4 N sites cfg) * f (reflectLinkVariableZ4 N (extendLinkVariableZ4 N sites cfg))
  set N_num := ∫ (cfg : FiniteLinkConfigZ4 N sites), F cfg * Real.exp (-β * wilsonActionFiniteConfigZ4 N β sites cfg) ∂ μ₀ with hN
  have h_nonneg : 0 ≤ N_num := by
    by_cases h : sites = ∅
    · subst h
      dsimp [N_num, F, μ₀]
      apply integral_nonneg
      intro cfg
      have h_ext_eq : extendLinkVariableZ4 N ∅ cfg = { value := λ _ _ => (1 : SU N) } := by
        ext n μ; dsimp [extendLinkVariableZ4, extendLinkVariable]
      have h_ref_eq : reflectLinkVariableZ4 N ({ value := λ _ _ => (1 : SU N) }) = { value := λ _ _ => (1 : SU N) } := by
        ext n μ; simp [reflectLinkVariableZ4, reflectLinkVariable]
      have h_sq_nonneg : 0 ≤ (f ({ value := λ _ _ => (1 : SU N) }))^2 := sq_nonneg _
      have h_exp_nonneg : 0 ≤ Real.exp (-β * wilsonActionFiniteConfigZ4 N β ∅ cfg) :=
        le_of_lt (Real.exp_pos (-β * wilsonActionFiniteConfigZ4 N β ∅ cfg))
      have h_nonneg_prod : 0 ≤ (f ({ value := λ _ _ => (1 : SU N) }))^2 *
        Real.exp (-β * wilsonActionFiniteConfigZ4 N β ∅ cfg) :=
        mul_nonneg h_sq_nonneg h_exp_nonneg
      simpa [h_ext_eq, h_ref_eq, mul_assoc, sq] using h_nonneg_prod
    · -- Nonempty case: `hadd` forces a contradiction for finite lattices (see docs/hadd_issue.md).
      -- A proper proof requires periodic boundary conditions and the Osterwalder-Seiler factorization.
      have h_nonempty : Finset.Nonempty sites := by
        rcases Finset.eq_empty_or_nonempty sites with (h' | h')
        · exact (h h').elim
        · exact h'
      let f_time (n : Z4Site) : ℤ := n.1
      have h_f_nonempty : Finset.Nonempty (Finset.image f_time sites) := by
        rcases h_nonempty with ⟨a, ha⟩
        refine ⟨f_time a, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩
      let m := Finset.max' (Finset.image f_time sites) h_f_nonempty
      have hm : m ∈ Finset.image f_time sites := Finset.max'_mem _ _
      rcases Finset.mem_image.mp hm with ⟨n, hn, hm_eq⟩
      have hn_next : addVector n 0 ∈ sites := hadd n hn
      have h_m_add : (addVector n 0).1 = n.1 + 1 := by
        simp [addVector, addVectorZ4]
      have h_m_add_val : (addVector n 0).1 = m + 1 := by
        calc
          (addVector n 0).1 = n.1 + 1 := h_m_add
          _ = m + 1 := by dsimp [f_time] at hm_eq; rw [hm_eq]
      have h_max : (addVector n 0).1 ≤ m := by
        have h_mem : f_time (addVector n 0) ∈ Finset.image f_time sites :=
          Finset.mem_image.mpr ⟨addVector n 0, hn_next, rfl⟩
        exact Finset.le_max' (Finset.image f_time sites) (f_time (addVector n 0)) h_mem
      have h_contra : m + 1 ≤ m := by
        calc
          m + 1 = (addVector n 0).1 := by symm; exact h_m_add_val
          _ ≤ m := h_max
      have h_contra : m + 1 ≤ m := by
        calc
          m + 1 = (addVector n 0).1 := by symm; exact h_m_add_val
          _ ≤ m := h_max
      linarith
  exact div_nonneg h_nonneg (le_of_lt hZ_pos)

end Z4SiteAliases
end GenericProductMeasure
end ProductHaarMeasure
end Lattice
end YangMills
