/-
# Reflection Positivity: Plaquette Structure
-/

import YangMills.Proofs.ReflectionPositivity.OSDecomposition

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open scoped BigOperators
open MeasureTheory
open Complex
open scoped ComplexConjugate

namespace YangMills
namespace Lattice
/-! ### G3: Interface plaquette enumeration

The third piece of the concrete↔abstract bridge (§8.11 of
`docs/transfer_matrix_positivity_design.md`): restrict the product to
*interface* plaquettes only.  The interface action `S_OS_int` is defined as
`∑ (if isInterface then S_p else 0)`, so `exp(-β·S_int) = ∏ (if isInterface
then exp(-β·S_p) else 1)` by exp-of-sum + if-splitting.  Non-interface
plaquettes contribute a factor of 1, so the product is effectively over
interface plaquettes only.  Pure algebra — 0 sorries, 0 custom axioms. -/

/-- The interface plaquette predicate: a plaquette `(n, μ, ν)` is an "interface
plaquette" iff its four corners do NOT all have positive signed time AND do NOT
all have negative signed time (i.e., the corners straddle the time interface).
This matches the condition in `wilsonActionOSInterface`.  Defined as an
abbreviation so it unfolds to the inline condition (matching the `Decidable`
instance used by `wilsonActionOSInterface`). -/
abbrev isInterfacePlaquette (T L : ℕ) [NeZero T] [NeZero L]
    (n : PeriodicSite T L) (μ ν : Fin 4) : Prop :=
  ¬ (signedTime T n.time > 0 ∧ signedTime T (addVectorPeriodic T L n μ).time > 0 ∧
     signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time > 0 ∧
     signedTime T (addVectorPeriodic T L n ν).time > 0) ∧
  ¬ (signedTime T n.time < 0 ∧ signedTime T (addVectorPeriodic T L n μ).time < 0 ∧
     signedTime T (addVectorPeriodic T L (addVectorPeriodic T L n μ) ν).time < 0 ∧
     signedTime T (addVectorPeriodic T L n ν).time < 0)

/-- `wilsonActionOSInterface` equals the sum over all plaquettes with the
interface predicate as the if-condition.  This is by definition (the condition
in `wilsonActionOSInterface` is exactly `isInterfacePlaquette`). -/
lemma wilsonActionOSInterface_eq (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) :
    wilsonActionOSInterface N T L β U =
    ∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4,
      (if isInterfacePlaquette T L n μ ν then plaquetteContribution N β U n μ ν else 0) := by
  unfold wilsonActionOSInterface isInterfacePlaquette
  rfl

/-- The interface action is uniformly bounded: `|S_int| ≤ #(PeriodicSite T L)·32·|β|`.

Each plaquette contribution satisfies `|plaquetteContribution| ≤ 2|β|`
(`plaquetteContribution_bounded`), and the interface action is a sum of at most
`#(PeriodicSite T L)·16` such terms (the `if isInterfacePlaquette` selects a subset).
This gives `|S_int| ≤ #(PeriodicSite T L)·16·2|β| = #(PeriodicSite T L)·32·|β|`.

This is ingredient 2 of the integrability discharge (design doc §8.11.10): it
provides a uniform upper bound on `|S_int|`, hence a positive lower bound
`exp(-β·S_int) ≥ exp(-|β|·#(PeriodicSite T L)·32·|β|) > 0`. 0 sorries, 0 custom axioms. -/
lemma wilsonActionOSInterface_bounded (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) :
    |wilsonActionOSInterface N T L β U| ≤ (Fintype.card (PeriodicSite T L) * 32) * |β| := by
  rw [wilsonActionOSInterface_eq]
  -- Each term is bounded: |if c then pc else 0| ≤ 2|β|
  have h_bound : ∀ n μ ν,
      |(if isInterfacePlaquette T L n μ ν then plaquetteContribution N β U n μ ν else 0)| ≤
        2 * |β| := by
    intro n μ ν
    by_cases h : isInterfacePlaquette T L n μ ν
    · rw [if_pos h]; exact plaquetteContribution_bounded N β U n μ ν
    · rw [if_neg h]; simp
  -- Upper bound: each term ≤ 2|β|
  have h_upper : ∀ n μ ν,
      (if isInterfacePlaquette T L n μ ν then plaquetteContribution N β U n μ ν else 0) ≤
        2 * |β| := fun n μ ν => (abs_le.mp (h_bound n μ ν)).2
  -- Lower bound: each term ≥ -(2|β|)
  have h_lower : ∀ n μ ν,
      -(2 * |β|) ≤
        (if isInterfacePlaquette T L n μ ν then plaquetteContribution N β U n μ ν else 0) :=
    fun n μ ν => (abs_le.mp (h_bound n μ ν)).1
  -- S ≤ ∑ n μ ν 2|β|
  have h_S_upper : (∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4,
      (if isInterfacePlaquette T L n μ ν then plaquetteContribution N β U n μ ν else 0)) ≤
    ∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4, 2 * |β| := by
    apply Finset.sum_le_sum; intro n _
    apply Finset.sum_le_sum; intro μ _
    apply Finset.sum_le_sum; intro ν _
    exact h_upper n μ ν
  -- -(∑ n μ ν 2|β|) ≤ S
  have h_S_lower : (∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4, -(2 * |β|)) ≤
    (∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4,
      (if isInterfacePlaquette T L n μ ν then plaquetteContribution N β U n μ ν else 0)) := by
    apply Finset.sum_le_sum; intro n _
    apply Finset.sum_le_sum; intro μ _
    apply Finset.sum_le_sum; intro ν _
    exact h_lower n μ ν
  -- Constant sums
  have h_const : (∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4, 2 * |β|) =
      (Fintype.card (PeriodicSite T L) * 32) * |β| := by
    have h_ν : ∑ ν : Fin 4, (2 * |β| : ℝ) = 8 * |β| := by
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; ring
    have h_μ : ∑ μ : Fin 4, (8 * |β| : ℝ) = 32 * |β| := by
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; ring
    have h_n : ∑ n : PeriodicSite T L, (32 * |β| : ℝ) =
        Fintype.card (PeriodicSite T L) * (32 * |β|) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [h_ν, h_μ, h_n]; ring
  have h_const_neg : (∑ n : PeriodicSite T L, ∑ μ : Fin 4, ∑ ν : Fin 4, -(2 * |β|)) =
      -((Fintype.card (PeriodicSite T L) * 32) * |β|) := by
    have h_ν : ∑ ν : Fin 4, (-(2 * |β|) : ℝ) = -(8 * |β|) := by
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; ring
    have h_μ : ∑ μ : Fin 4, (-(8 * |β|) : ℝ) = -(32 * |β|) := by
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; ring
    have h_n : ∑ n : PeriodicSite T L, (-(32 * |β|) : ℝ) =
        -(Fintype.card (PeriodicSite T L) * (32 * |β|)) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    rw [h_ν, h_μ, h_n]; ring
  -- |S| ≤ C
  rw [h_const] at h_S_upper
  rw [h_const_neg] at h_S_lower
  exact abs_le.mpr ⟨h_S_lower, h_S_upper⟩

#print axioms wilsonActionOSInterface_bounded

/-- The interface Boltzmann factor `exp(-β·S_int)` is bounded below by a positive
constant independent of `U`:

    exp(-|β|·#(PeriodicSite T L)·32·|β|) ≤ exp(-β·S_int(U))

This follows from `wilsonActionOSInterface_bounded` (`|S_int| ≤ C`) and the
monotonicity of `exp`: `-β·S_int ≥ -|β·S_int| ≥ -|β|·C`, so
`exp(-β·S_int) ≥ exp(-|β|·C) > 0`.

This is the key ingredient for the domination argument in the integrability
discharge (design doc §8.11.10): it provides a uniform positive lower bound
`m = exp(-|β|·C) > 0` on `exp(-β·S_int)`, allowing division by this factor to
deduce integrability of `ψ(merge)·exp(-β·S⁺(merge)/2)` from the integrability
of the full integrand `ψ(merge)·exp(-β·(S⁺(u)/2 + S⁺(merge)/2 + S_int(U)))`.
0 sorries, 0 custom axioms. -/
lemma exp_neg_beta_wilsonActionOSInterface_lower_bound (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) :
    Real.exp (-|β| * ((Fintype.card (PeriodicSite T L) * 32) * |β|)) ≤
      Real.exp (-β * wilsonActionOSInterface N T L β U) := by
  apply Real.exp_le_exp.mpr
  have h_bound := wilsonActionOSInterface_bounded N T L β U
  have h_abs : |β * wilsonActionOSInterface N T L β U| ≤
      |β| * ((Fintype.card (PeriodicSite T L) * 32) * |β|) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h_bound (abs_nonneg _)
  have h_le : β * wilsonActionOSInterface N T L β U ≤
      |β| * ((Fintype.card (PeriodicSite T L) * 32) * |β|) := by
    have h_self : β * wilsonActionOSInterface N T L β U ≤
        |β * wilsonActionOSInterface N T L β U| := le_abs_self _
    linarith
  linarith

#print axioms exp_neg_beta_wilsonActionOSInterface_lower_bound

/-- **G3: exp-of-sum for the interface action.** The interface Boltzmann factor
`exp(-β·S_int)` factorises as a product of per-plaquette factors, where only
interface plaquettes contribute (non-interface plaquettes contribute 1):

    exp(-β·S_int) = ∏_{n,μ,ν} (if isInterfacePlaquette then exp(-β·S_p) else 1)

This is the exp-of-sum = product-of-exps identity applied to
`wilsonActionOSInterface_eq`, combined with if-splitting
(`exp(-β·(if c then x else 0)) = if c then exp(-β·x) else 1`).  Pure algebra —
0 sorries, 0 custom axioms. -/
lemma exp_neg_beta_wilsonActionOSInterface_eq_prod (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) :
    Real.exp (-β * wilsonActionOSInterface N T L β U) =
    ∏ n : PeriodicSite T L, ∏ μ : Fin 4, ∏ ν : Fin 4,
      (if isInterfacePlaquette T L n μ ν then
        Real.exp (-β * plaquetteContribution N β U n μ ν) else 1) := by
  rw [wilsonActionOSInterface_eq]
  simp only [Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro n _
  apply Finset.prod_congr rfl
  intro μ _
  apply Finset.prod_congr rfl
  intro ν _
  split_ifs
  · rfl
  · simp [Real.exp_zero]

/-- **G3 composed with G2: the interface Boltzmann factor as a product of
abstract plaquette Boltzmann factors.** Combining
`exp_neg_beta_wilsonActionOSInterface_eq_prod` (G3) with
`plaquetteContribution_exp_decomp_tm` (G2), the interface Boltzmann factor
`exp(-β·S_int)` equals a product of `exp(c·Re Tr(P_p))` factors (with `c = β²/N
≥ 0`) over interface plaquettes, times a positive constant `exp(-β²)` per
interface plaquette:

    exp(-β·S_int) = ∏_{n,μ,ν} (if isInterface then exp(-β²)·exp((β²/N)·Re Tr(P_p)) else 1)

The non-interface terms are 1, so this is effectively a product over interface
plaquettes only.  The `exp(-β²)` factors are a positive constant absorbable into
normalization.  This is the form that `interface_kernel_character_expansion`
operates on (with `c = β²/N`).  Pure algebra — 0 sorries, 0 custom axioms. -/
lemma exp_neg_beta_wilsonActionOSInterface_eq_prod_abstract (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) :
    Real.exp (-β * wilsonActionOSInterface N T L β U) =
    ∏ n : PeriodicSite T L, ∏ μ : Fin 4, ∏ ν : Fin 4,
      (if isInterfacePlaquette T L n μ ν then
        Real.exp (-(β * β)) *
        Real.exp ((β * β / N) *
          Complex.re (Matrix.trace ((plaquetteProduct N U n μ ν : Matrix (Fin N) (Fin N) ℂ))))
        else 1) := by
  rw [exp_neg_beta_wilsonActionOSInterface_eq_prod]
  apply Finset.prod_congr rfl
  intro n _
  apply Finset.prod_congr rfl
  intro μ _
  apply Finset.prod_congr rfl
  intro ν _
  split_ifs with h
  · rw [plaquetteContribution_exp_decomp_tm]
  · rfl

#print axioms wilsonActionOSInterface_eq
#print axioms exp_neg_beta_wilsonActionOSInterface_eq_prod
#print axioms exp_neg_beta_wilsonActionOSInterface_eq_prod_abstract

/-! ### Concrete link/plaquette structures for the character expansion

These definitions set up the concrete combinatorial data needed to apply the
abstract `interface_kernel_character_expansion` (in `PeterWeyl.lean`) to the
concrete periodic lattice.  This is sub-step (i) of Lemma 2
(`transfer_matrix_integral_reduction`) in
`docs/transfer_matrix_positivity_design.md` §8.8: identifying the link
partition `L = L_U ⊔ L_0 ⊔ L_V` (U⁺/u⁰/V⁺ links) for the concrete lattice.

All definitions and lemmas here are pure combinatorics — 0 sorries, 0 custom
axioms. -/

/-- The j-th link of a plaquette `(n, μ, ν)`.  The four links of the plaquette
product `U(n,μ) · U(n+e_μ,ν) · U(n+e_μ+e_ν,μ)⁻¹ · U(n+e_ν,ν)⁻¹` are:
  - j=0: `(n, μ)`           — the link `U(n, μ)`
  - j=1: `(n+e_μ, ν)`       — the link `U(n+e_μ, ν)`
  - j=2: `(n+e_μ+e_ν, μ)`   — the link `U(n+e_μ+e_ν, μ)`, **inverted** in the product
  - j=3: `(n+e_ν, ν)`       — the link `U(n+e_ν, ν)`, **inverted** in the product
This matches the definition of `plaquetteProduct` in `Lattice.lean`. -/
def plaquetteLinkIdx (T L : ℕ) [NeZero T] [NeZero L]
    (p : PlaquetteIndex T L) (j : Fin 4) : PeriodicSite T L × Fin 4 :=
  match j with
  | 0 => (p.1, p.2.1)
  | 1 => (addVectorPeriodic T L p.1 p.2.1, p.2.2)
  | 2 => (addVectorPeriodic T L (addVectorPeriodic T L p.1 p.2.1) p.2.2, p.2.1)
  | 3 => (addVectorPeriodic T L p.1 p.2.2, p.2.2)

/-- The plaquette product equals the product of link variables at the four
plaquette links (with the 3rd and 4th inverted).  This connects the concrete
`plaquetteProduct` to the abstract form
`g(links p 0)·g(links p 1)·g(links p 2)⁻¹·g(links p 3)⁻¹` that
`interface_kernel_character_expansion` operates on. -/
lemma plaquetteProduct_eq_linkIdx (N T L : ℕ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) (p : PlaquetteIndex T L) :
    plaquetteProduct N U p.1 p.2.1 p.2.2 =
    U.value (plaquetteLinkIdx T L p 0).1 (plaquetteLinkIdx T L p 0).2 *
    U.value (plaquetteLinkIdx T L p 1).1 (plaquetteLinkIdx T L p 1).2 *
    (U.value (plaquetteLinkIdx T L p 2).1 (plaquetteLinkIdx T L p 2).2)⁻¹ *
    (U.value (plaquetteLinkIdx T L p 3).1 (plaquetteLinkIdx T L p 3).2)⁻¹ := by
  unfold plaquetteLinkIdx plaquetteProduct
  rfl

/-- Interface plaquettes as a subtype of `PlaquetteIndex`. -/
abbrev InterfacePlaquette (T L : ℕ) [NeZero T] [NeZero L] : Type :=
  {p : PlaquetteIndex T L // isInterfacePlaquette T L p.1 p.2.1 p.2.2}

noncomputable instance (T L : ℕ) [NeZero T] [NeZero L] : Fintype (InterfacePlaquette T L) := by
  classical
  exact inferInstanceAs (Fintype {p : PlaquetteIndex T L //
    isInterfacePlaquette T L p.1 p.2.1 p.2.2})

instance (T L : ℕ) [NeZero T] [NeZero L] : DecidableEq (InterfacePlaquette T L) :=
  inferInstanceAs (DecidableEq {p : PlaquetteIndex T L //
    isInterfacePlaquette T L p.1 p.2.1 p.2.2})

/-- The Finset of all links appearing in at least one interface plaquette. -/
noncomputable def interfacePlaqLinkFinset (T L : ℕ) [NeZero T] [NeZero L] :
    Finset (PeriodicSite T L × Fin 4) :=
  (Finset.univ : Finset (InterfacePlaquette T L × Fin 4)).image
    (fun x => plaquetteLinkIdx T L x.1.val x.2)

/-- The type of links appearing in interface plaquettes (subtype).  This is the
concrete `L` for `interface_kernel_character_expansion`: by construction, every
link in this type appears in at least one interface plaquette, so the
surjectivity hypothesis `hlinks_surj` holds. -/
abbrev InterfaceLink (T L : ℕ) [NeZero T] [NeZero L] : Type :=
  {l : PeriodicSite T L × Fin 4 // l ∈ interfacePlaqLinkFinset T L}

noncomputable instance (T L : ℕ) [NeZero T] [NeZero L] : Fintype (InterfaceLink T L) := by
  classical
  exact inferInstanceAs (Fintype {l : PeriodicSite T L × Fin 4 //
    l ∈ interfacePlaqLinkFinset T L})

instance (T L : ℕ) [NeZero T] [NeZero L] : DecidableEq (InterfaceLink T L) :=
  inferInstanceAs (DecidableEq {l : PeriodicSite T L × Fin 4 //
    l ∈ interfacePlaqLinkFinset T L})

/-- The link assignment `InterfacePlaquette → Fin 4 → InterfaceLink`.  Maps each
plaquette `p` and index `j` to the j-th link of `p`, packaged as an
`InterfaceLink` (with the proof that it appears in an interface plaquette). -/
def interfaceLinkAssign (T L : ℕ) [NeZero T] [NeZero L]
    (p : InterfacePlaquette T L) (j : Fin 4) : InterfaceLink T L :=
  ⟨plaquetteLinkIdx T L p.val j, by
    simp only [interfacePlaqLinkFinset, Finset.mem_image, Finset.mem_univ, true_and,
      Prod.exists, exists_prop]
    exact ⟨p, j, rfl⟩⟩

/-- The link assignment is surjective: every `InterfaceLink` arises as some
plaquette's j-th link.  This is the `hlinks_surj` hypothesis for
`interface_kernel_character_expansion`. -/
lemma interfaceLinkAssign_surj (T L : ℕ) [NeZero T] [NeZero L] :
    ∀ l : InterfaceLink T L, ∃ p j, interfaceLinkAssign T L p j = l := by
  intro l
  have hl : l.val ∈ interfacePlaqLinkFinset T L := l.prop
  simp only [interfacePlaqLinkFinset, Finset.mem_image, Finset.mem_univ, true_and,
    Prod.exists, exists_prop] at hl
  obtain ⟨p, j, hj⟩ := hl
  refine ⟨p, j, ?_⟩
  simp only [interfaceLinkAssign, Subtype.mk_eq_mk, hj]

/-- Extract the link variable `U(n, μ)` from a full configuration at an
`InterfaceLink` `l = (n, μ)`. -/
def interfaceLinkVar (N T L : ℕ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) (l : InterfaceLink T L) : SU N :=
  U.value l.val.1 l.val.2

/-- `interfaceLinkVar · l` is measurable in `U` (a coordinate projection from `U.value`). -/
lemma measurable_interfaceLinkVar (N T L : ℕ) [NeZero T] [NeZero L]
    (l : InterfaceLink T L) :
    Measurable (fun (U : LinkVariable (SU N) (PeriodicSite T L)) => interfaceLinkVar N T L U l) := by
  dsimp [interfaceLinkVar]
  have h_value_map : Measurable (fun (U : LinkVariable (SU N) (PeriodicSite T L)) => U.value) :=
    comap_measurable (fun (U : LinkVariable (SU N) (PeriodicSite T L)) => U.value)
  have h_at_n : Measurable (fun (f : PeriodicSite T L → Fin 4 → SU N) => f l.val.1) :=
    measurable_pi_apply l.val.1
  have h_at_n_μ : Measurable (fun (f : Fin 4 → SU N) => f l.val.2) :=
    measurable_pi_apply l.val.2
  exact h_at_n_μ.comp (h_at_n.comp h_value_map)

/-- The plaquette product of an interface plaquette equals the abstract form
`g(links p 0)·g(links p 1)·g(links p 2)⁻¹·g(links p 3)⁻¹` where `g` extracts
link variables via `interfaceLinkVar`. -/
lemma plaquetteProduct_interface_eq (N T L : ℕ) [NeZero T] [NeZero L]
    (U : LinkVariable (SU N) (PeriodicSite T L)) (p : InterfacePlaquette T L) :
    plaquetteProduct N U p.val.1 p.val.2.1 p.val.2.2 =
    interfaceLinkVar N T L U (interfaceLinkAssign T L p 0) *
    interfaceLinkVar N T L U (interfaceLinkAssign T L p 1) *
    (interfaceLinkVar N T L U (interfaceLinkAssign T L p 2))⁻¹ *
    (interfaceLinkVar N T L U (interfaceLinkAssign T L p 3))⁻¹ := by
  unfold interfaceLinkVar interfaceLinkAssign
  exact plaquetteProduct_eq_linkIdx N T L U p.val

/-- The positive-time links among the interface links (`L_U`). -/
noncomputable def interfaceLinkPos (T L : ℕ) [NeZero T] [NeZero L] :
    Finset (InterfaceLink T L) :=
  (Finset.univ : Finset (InterfaceLink T L)).filter
    (fun l => signedTime T l.val.1.time > 0)

/-- The interface (time-0) links among the interface links (`L_0`). -/
noncomputable def interfaceLinkInt (T L : ℕ) [NeZero T] [NeZero L] :
    Finset (InterfaceLink T L) :=
  (Finset.univ : Finset (InterfaceLink T L)).filter
    (fun l => signedTime T l.val.1.time = 0)

/-- The negative-time links among the interface links (`L_V`). -/
noncomputable def interfaceLinkNeg (T L : ℕ) [NeZero T] [NeZero L] :
    Finset (InterfaceLink T L) :=
  (Finset.univ : Finset (InterfaceLink T L)).filter
    (fun l => signedTime T l.val.1.time < 0)

/-- Trichotomy of `signedTime`: exactly one of `> 0`, `= 0`, `< 0` holds. -/
lemma signedTime_trichotomy (T : ℕ) (t : ZMod T) :
    signedTime T t > 0 ∨ signedTime T t = 0 ∨ signedTime T t < 0 := by
  omega

/-- The three link sets are pairwise disjoint and cover all interface links. -/
lemma interfaceLinkPartition_disjoint_cover (T L : ℕ) [NeZero T] [NeZero L] :
    Disjoint (interfaceLinkPos T L) (interfaceLinkInt T L) ∧
    Disjoint (interfaceLinkPos T L ∪ interfaceLinkInt T L) (interfaceLinkNeg T L) ∧
    interfaceLinkPos T L ∪ interfaceLinkInt T L ∪ interfaceLinkNeg T L = Finset.univ := by
  refine ⟨?_, ?_, ?_⟩
  · -- Disjoint pos int
    refine Finset.disjoint_left.mpr (fun l hl hl' => ?_)
    rw [interfaceLinkPos, Finset.mem_filter] at hl
    rw [interfaceLinkInt, Finset.mem_filter] at hl'
    obtain ⟨_, hpos⟩ := hl
    obtain ⟨_, hint⟩ := hl'
    rw [hint] at hpos
    exact lt_irrefl _ hpos
  · -- Disjoint (pos ∪ int) neg
    refine Finset.disjoint_left.mpr (fun l hl hl' => ?_)
    rw [interfaceLinkNeg, Finset.mem_filter] at hl'
    obtain ⟨_, hneg⟩ := hl'
    rcases Finset.mem_union.mp hl with h | h
    · rw [interfaceLinkPos, Finset.mem_filter] at h
      obtain ⟨_, hpos⟩ := h
      exact lt_irrefl _ (lt_of_lt_of_le hpos (le_of_lt hneg))
    · rw [interfaceLinkInt, Finset.mem_filter] at h
      obtain ⟨_, hint⟩ := h
      rw [hint] at hneg
      exact lt_irrefl _ hneg
  · -- Cover
    ext l
    simp only [interfaceLinkPos, interfaceLinkInt, interfaceLinkNeg, Finset.mem_union,
      Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    rcases signedTime_trichotomy T l.val.1.time with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

/-- The partition in the form required by `interface_kernel_character_expansion`:
`hdisj : Disjoint L_U L_0 ∧ Disjoint (L_U ∪ L_0) L_V`. -/
lemma interfaceLinkPartition_hdisj (T L : ℕ) [NeZero T] [NeZero L] :
    Disjoint (interfaceLinkPos T L) (interfaceLinkInt T L) ∧
    Disjoint (interfaceLinkPos T L ∪ interfaceLinkInt T L) (interfaceLinkNeg T L) :=
  ⟨interfaceLinkPartition_disjoint_cover T L |>.1,
   interfaceLinkPartition_disjoint_cover T L |>.2.1⟩

/-- The partition in the form required by `interface_kernel_character_expansion`:
`hcover : L_U ∪ L_0 ∪ L_V = Finset.univ`. -/
lemma interfaceLinkPartition_hcover (T L : ℕ) [NeZero T] [NeZero L] :
    interfaceLinkPos T L ∪ interfaceLinkInt T L ∪ interfaceLinkNeg T L = Finset.univ :=
  interfaceLinkPartition_disjoint_cover T L |>.2.2

/-! ### Full link partition (ALL links, not just interface links)

For the FULL character expansion (§8.11.61), we need to partition ALL links
(`PeriodicSite T L × Fin 4`) into positive (L_U), interface (L_0), and negative
(L_V) sets, and prove that `plaquetteLinkIdx` is surjective (every link appears
in at least one plaquette).  This is the key infrastructure for applying
`plaquette_product_separable_decomp` (PeterWeyl.lean:1358) to ALL plaquettes. -/

/-- All links at positive-time sites (`L_U` for the full expansion). -/
noncomputable def allLinkPos (T L : ℕ) [NeZero T] [NeZero L] :
    Finset (PeriodicSite T L × Fin 4) :=
  (Finset.univ : Finset (PeriodicSite T L × Fin 4)).filter
    (fun l => signedTime T l.1.time > 0)

/-- All links at interface (time-0) sites (`L_0` for the full expansion). -/
noncomputable def allLinkInt (T L : ℕ) [NeZero T] [NeZero L] :
    Finset (PeriodicSite T L × Fin 4) :=
  (Finset.univ : Finset (PeriodicSite T L × Fin 4)).filter
    (fun l => signedTime T l.1.time = 0)

/-- All links at negative-time sites (`L_V` for the full expansion). -/
noncomputable def allLinkNeg (T L : ℕ) [NeZero T] [NeZero L] :
    Finset (PeriodicSite T L × Fin 4) :=
  (Finset.univ : Finset (PeriodicSite T L × Fin 4)).filter
    (fun l => signedTime T l.1.time < 0)

/-- The three full link sets are pairwise disjoint and cover all links. -/
lemma allLinkPartition_disjoint_cover (T L : ℕ) [NeZero T] [NeZero L] :
    Disjoint (allLinkPos T L) (allLinkInt T L) ∧
    Disjoint (allLinkPos T L ∪ allLinkInt T L) (allLinkNeg T L) ∧
    allLinkPos T L ∪ allLinkInt T L ∪ allLinkNeg T L = Finset.univ := by
  refine ⟨?_, ?_, ?_⟩
  · refine Finset.disjoint_left.mpr (fun l hl hl' => ?_)
    rw [allLinkPos, Finset.mem_filter] at hl
    rw [allLinkInt, Finset.mem_filter] at hl'
    obtain ⟨_, hpos⟩ := hl
    obtain ⟨_, hint⟩ := hl'
    rw [hint] at hpos
    exact lt_irrefl _ hpos
  · refine Finset.disjoint_left.mpr (fun l hl hl' => ?_)
    rw [allLinkNeg, Finset.mem_filter] at hl'
    obtain ⟨_, hneg⟩ := hl'
    rcases Finset.mem_union.mp hl with h | h
    · rw [allLinkPos, Finset.mem_filter] at h
      obtain ⟨_, hpos⟩ := h
      exact lt_irrefl _ (lt_of_lt_of_le hpos (le_of_lt hneg))
    · rw [allLinkInt, Finset.mem_filter] at h
      obtain ⟨_, hint⟩ := h
      rw [hint] at hneg
      exact lt_irrefl _ hneg
  · ext l
    simp only [allLinkPos, allLinkInt, allLinkNeg, Finset.mem_union,
      Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    rcases signedTime_trichotomy T l.1.time with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

/-- The full partition in the form required by `interface_kernel_character_expansion`:
`hdisj : Disjoint L_U L_0 ∧ Disjoint (L_U ∪ L_0) L_V`. -/
lemma allLinkPartition_hdisj (T L : ℕ) [NeZero T] [NeZero L] :
    Disjoint (allLinkPos T L) (allLinkInt T L) ∧
    Disjoint (allLinkPos T L ∪ allLinkInt T L) (allLinkNeg T L) :=
  ⟨allLinkPartition_disjoint_cover T L |>.1,
   allLinkPartition_disjoint_cover T L |>.2.1⟩

/-- The full partition in the form required by `interface_kernel_character_expansion`:
`hcover : L_U ∪ L_0 ∪ L_V = Finset.univ`. -/
lemma allLinkPartition_hcover (T L : ℕ) [NeZero T] [NeZero L] :
    allLinkPos T L ∪ allLinkInt T L ∪ allLinkNeg T L = Finset.univ :=
  allLinkPartition_disjoint_cover T L |>.2.2

/-! ### Bridge lemmas: full link partition ↔ site partition

These lemmas connect the FULL link-based partition (`allLinkPos`/`allLinkInt`/`allLinkNeg`,
used by the full character expansion) with the SITE-based partition
(`positiveSites`/`interfaceSites`/`negativeSites`, used by the measure factorization
in `TransferMatrix.lean` via `measure_factorization'`).  A link `(n, μ)` is in
`allLinkPos` iff its base site `n` is in `positiveSites`, etc.  This compatibility
is needed for step 3 (interface link integral) and step 4 (positive/negative link
integral) of the §8.11.61 plan.  All 0 sorries, 0 custom axioms. -/

lemma allLinkPos_mem_iff (T L : ℕ) [NeZero T] [NeZero L]
    (l : PeriodicSite T L × Fin 4) :
    l ∈ allLinkPos T L ↔ l.1 ∈ positiveSites T L := by
  simp only [allLinkPos, Finset.mem_filter, Finset.mem_univ, true_and, positiveSites]

lemma allLinkInt_mem_iff (T L : ℕ) [NeZero T] [NeZero L]
    (l : PeriodicSite T L × Fin 4) :
    l ∈ allLinkInt T L ↔ l.1 ∈ interfaceSites T L := by
  simp only [allLinkInt, Finset.mem_filter, Finset.mem_univ, true_and, interfaceSites]

lemma allLinkNeg_mem_iff (T L : ℕ) [NeZero T] [NeZero L]
    (l : PeriodicSite T L × Fin 4) :
    l ∈ allLinkNeg T L ↔ l.1 ∈ negativeSites T L := by
  simp only [allLinkNeg, Finset.mem_filter, Finset.mem_univ, true_and, negativeSites]

#print axioms allLinkPos_mem_iff
#print axioms allLinkPos_mem_iff
#print axioms allLinkInt_mem_iff
#print axioms allLinkNeg_mem_iff

/-! ### Product conversion: Finset over link partition ↔ Fintype over FiniteLinkIndex

These lemmas convert a product over the Finset `allLinkPos`/`allLinkInt`/`allLinkNeg`
(used by the character expansion) to a product over the Fintype
`FiniteLinkIndex (PeriodicSite T L) (positiveSites/interfaceSites/negativeSites)`
(used by the measure factorization).  This is the key bridge for step 3 (interface link
integral) and step 4 (positive/negative link integral): it allows applying
`integral_prod_repCharacter_trivial` (PeterWeyl.lean:2435), which works for product
measures on Fintype-indexed function types, to the character factors in the expansion.
All 0 sorries, 0 custom axioms. -/

lemma prod_allLinkPos_eq_prod_finiteLinkIndex (T L : ℕ) [NeZero T] [NeZero L]
    {α : Type*} [CommMonoid α] (f : (PeriodicSite T L × Fin 4) → α) :
    ∏ l ∈ allLinkPos T L, f l =
    ∏ (l : FiniteLinkIndex (PeriodicSite T L) (positiveSites T L)), f l.val :=
  Finset.prod_subtype (allLinkPos T L) (allLinkPos_mem_iff T L) f

lemma prod_allLinkInt_eq_prod_finiteLinkIndex (T L : ℕ) [NeZero T] [NeZero L]
    {α : Type*} [CommMonoid α] (f : (PeriodicSite T L × Fin 4) → α) :
    ∏ l ∈ allLinkInt T L, f l =
    ∏ (l : FiniteLinkIndex (PeriodicSite T L) (interfaceSites T L)), f l.val :=
  Finset.prod_subtype (allLinkInt T L) (allLinkInt_mem_iff T L) f

lemma prod_allLinkNeg_eq_prod_finiteLinkIndex (T L : ℕ) [NeZero T] [NeZero L]
    {α : Type*} [CommMonoid α] (f : (PeriodicSite T L × Fin 4) → α) :
    ∏ l ∈ allLinkNeg T L, f l =
    ∏ (l : FiniteLinkIndex (PeriodicSite T L) (negativeSites T L)), f l.val :=
  Finset.prod_subtype (allLinkNeg T L) (allLinkNeg_mem_iff T L) f

#print axioms prod_allLinkPos_eq_prod_finiteLinkIndex
#print axioms prod_allLinkInt_eq_prod_finiteLinkIndex
#print axioms prod_allLinkNeg_eq_prod_finiteLinkIndex

