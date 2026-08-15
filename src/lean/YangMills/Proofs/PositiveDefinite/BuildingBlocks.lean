/-
# Positive Definite: Building Blocks and SU(N)
-/

import YangMills.Proofs.PositiveDefinite.ProductGroup

open Finset
open Complex
open Filter
open Matrix
open MeasureTheory
open scoped ComplexConjugate
open scoped ComplexOrder

namespace YangMills
/-! ## Building blocks for the full Boltzmann factor

These lemmas are the abstract ingredients needed to promote the single-plaquette
positive-definiteness result `plaquetteBoltzmannPD` (in `PeterWeyl.lean`) to
positive-definiteness of the *full* Wilson Boltzmann factor
`exp(-β · S_W)` on the entire link-variable group `SU(N)^{#links}`.

* `PositiveDefinite.comp_mulEquiv`: positive-definiteness is preserved by group
  isomorphisms.  This lets one permute / rearrange the factors of a product group
  (e.g. place four plaquette links at arbitrary positions among all links).
* `PositiveDefinite.fst` / `.snd`: a positive-definite function on one factor,
  viewed as a function on a product group that ignores the other factor, is
  positive-definite.  This lets one regard a single-plaquette factor (which
  depends on only four links) as a function on the full link group.
* `PositiveDefinite.finprod`: a finite product of positive-definite functions on
  the same group is positive-definite (the n-ary Schur product theorem).  This
  combines the individual (extended) plaquette factors into the full Boltzmann
  factor `∏_p exp(β · Re Tr(U_{∂p}))`.
-/

section BuildingBlocks

variable {G H : Type*} [Group G] [Group H]

/-- Positive-definiteness is preserved by group isomorphisms: if `e : G ≃* H`
is a group isomorphism and `φ : H → ℂ` is positive-definite, then
`φ ∘ e : G → ℂ` is positive-definite.  The proof regroups the quadratic form by
the image of `e` using `PositiveDefinite.sum_nonneg_of_map`. -/
lemma PositiveDefinite.comp_mulEquiv (e : G ≃* H) {φ : H → ℂ}
    (hφ : PositiveDefinite φ) : PositiveDefinite (fun g => φ (e g)) := by
  intro s c
  have hkey := hφ.sum_nonneg_of_map s e c
  have hsum_eq : (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * φ (e (i⁻¹ * j))) =
      (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * φ ((e i)⁻¹ * e j)) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    rw [MulEquiv.map_mul, MulEquiv.map_inv]
  rw [hsum_eq]
  exact hkey

/-- Positive-definiteness is preserved by group homomorphisms: if `f : G →* H`
is a group homomorphism and `φ : H → ℂ` is positive-definite, then
`φ ∘ f : G → ℂ` is positive-definite.  This generalizes `comp_mulEquiv` from
isomorphisms to arbitrary homomorphisms (e.g. coordinate projections from a
product group to a sub-product).  The proof regroups the quadratic form by the
image of `f` using `PositiveDefinite.sum_nonneg_of_map`. -/
lemma PositiveDefinite.comp_hom (f : G →* H) {φ : H → ℂ}
    (hφ : PositiveDefinite φ) : PositiveDefinite (fun g => φ (f g)) := by
  intro s c
  have hkey := hφ.sum_nonneg_of_map s f c
  have hsum_eq : (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * φ (f (i⁻¹ * j))) =
      (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * φ ((f i)⁻¹ * f j)) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    rw [MonoidHom.map_mul, MonoidHom.map_inv]
  rw [hsum_eq]
  exact hkey

/-- A positive-definite function on `G`, regarded as a function on `G × H` that
ignores the `H`-component, is positive-definite on `G × H`. -/
lemma PositiveDefinite.fst {φ : G → ℂ} (hφ : PositiveDefinite φ) :
    PositiveDefinite (fun (p : G × H) => φ p.1) := by
  have h := PositiveDefinite.prod hφ (@PositiveDefinite.one H _)
  convert h using 1
  ext p; simp

/-- A positive-definite function on `H`, regarded as a function on `G × H` that
ignores the `G`-component, is positive-definite on `G × H`. -/
lemma PositiveDefinite.snd {ψ : H → ℂ} (hψ : PositiveDefinite ψ) :
    PositiveDefinite (fun (p : G × H) => ψ p.2) := by
  have h := PositiveDefinite.prod (@PositiveDefinite.one G _) hψ
  convert h using 1
  ext p; simp

/-- A finite product of positive-definite functions on the same group is
positive-definite (the n-ary Schur product theorem). -/
lemma PositiveDefinite.finprod {ι : Type*} (s : Finset ι) (f : ι → G → ℂ)
    (hf : ∀ i ∈ s, PositiveDefinite (f i)) :
    PositiveDefinite (fun g => ∏ i ∈ s, f i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [PositiveDefinite.one]
  | insert x s hx ih =>
    have hPDx : PositiveDefinite (f x) := hf x (Finset.mem_insert_self x s)
    have hPDs : PositiveDefinite (fun g => ∏ i ∈ s, f i g) :=
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have heq : (fun g => ∏ i ∈ insert x s, f i g) =
        fun g => f x g * ∏ i ∈ s, f i g := by
      funext g; rw [Finset.prod_insert hx]
    rw [heq]
    exact PositiveDefinite.mul hPDx hPDs

end BuildingBlocks

section SU_N

open Matrix

lemma conjTranspose_eq_inv (N : ℕ) (g : SU N) :
    ((g : Matrix (Fin N) (Fin N) ℂ)ᴴ) = (g : Matrix (Fin N) (Fin N) ℂ)⁻¹ := by
  have h_unitary : (g : Matrix (Fin N) (Fin N) ℂ) * ((g : Matrix (Fin N) (Fin N) ℂ)ᴴ) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp g.property.1)
  exact (Matrix.inv_eq_right_inv h_unitary).symm

noncomputable def fundamentalCharacter (N : ℕ) (g : SU N) : ℂ :=
  Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)

lemma fundamentalCharacter_positiveDefinite (N : ℕ) :
    PositiveDefinite (fundamentalCharacter N) := by
  intro s c
  have h_nonneg_sq : ∀ (M : Matrix (Fin N) (Fin N) ℂ), 0 ≤ Matrix.trace (Mᴴ * M) := by
    intro M
    have : Matrix.trace (Mᴴ * M) = (∑ i : Fin N, (Mᴴ * M) i i : ℂ) := by
      simp [Matrix.trace]
    rw [this]
    refine Finset.sum_nonneg (λ i _ => ?_)
    have : (Mᴴ * M) i i = ∑ k : Fin N, conj (M k i) * M k i := by
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [this]
    refine Finset.sum_nonneg (λ k _ => ?_)
    have : 0 ≤ conj (M k i) * M k i := by
      rw [← Complex.normSq_eq_conj_mul_self]
      have h_nonneg_sq_val : 0 ≤ Complex.normSq (M k i) := Complex.normSq_nonneg _
      rw [Complex.nonneg_iff]
      constructor
      · simpa using h_nonneg_sq_val
      · simp
    exact this
  have dummy : True := trivial
  have h_tr_eq : Matrix.trace (
      ((∑ g ∈ s, (conj (c g) : ℂ) • ((g : SU N) : Matrix (Fin N) (Fin N) ℂ))ᴴ) *
      (∑ g ∈ s, (conj (c g) : ℂ) • ((g : SU N) : Matrix (Fin N) (Fin N) ℂ))) =
      (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * fundamentalCharacter N (i⁻¹ * j)) :=
    calc
      Matrix.trace (((∑ g ∈ s, (conj (c g) : ℂ) • ((g : SU N) : Matrix (Fin N) (Fin N) ℂ))ᴴ) * (∑ g ∈ s, (conj (c g) : ℂ) • ((g : SU N) : Matrix (Fin N) (Fin N) ℂ)))
          = Matrix.trace ((∑ i ∈ s, (c i : ℂ) • (((i : SU N) : Matrix (Fin N) (Fin N) ℂ)⁻¹)) * (∑ j ∈ s, (conj (c j) : ℂ) • ((j : SU N) : Matrix (Fin N) (Fin N) ℂ))) := by
        simp [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_star, conjTranspose_eq_inv N]
      _ = Matrix.trace (∑ i ∈ s, ∑ j ∈ s, ((c i : ℂ) * (conj (c j) : ℂ)) • (((i : SU N) : Matrix (Fin N) (Fin N) ℂ)⁻¹ * ((j : SU N) : Matrix (Fin N) (Fin N) ℂ))) := by
        simp [Finset.sum_mul, Finset.mul_sum, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, mul_assoc, mul_comm, mul_left_comm]
        try rw [Finset.sum_comm]
        try simp [mul_comm, mul_left_comm, mul_assoc]
      _ = ∑ i ∈ s, ∑ j ∈ s, ((c i : ℂ) * (conj (c j) : ℂ)) * Matrix.trace (((i : SU N) : Matrix (Fin N) (Fin N) ℂ)⁻¹ * ((j : SU N) : Matrix (Fin N) (Fin N) ℂ)) := by
        simp [Matrix.trace_smul]
      _ = (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * fundamentalCharacter N (i⁻¹ * j)) := by
        have h_val_inv (g : SU N) : ((g : SU N) : Matrix (Fin N) (Fin N) ℂ)⁻¹ = ((g⁻¹ : SU N) : Matrix (Fin N) (Fin N) ℂ) := by
          calc
            ((g : SU N) : Matrix (Fin N) (Fin N) ℂ)⁻¹ = ((g : SU N) : Matrix (Fin N) (Fin N) ℂ)ᴴ :=
              (conjTranspose_eq_inv N g).symm
            _ = star ((g : SU N) : Matrix (Fin N) (Fin N) ℂ) := rfl
            _ = ((g⁻¹ : SU N) : Matrix (Fin N) (Fin N) ℂ) := by
              have h_star_eq_inv : (star (g : SU N) : SU N) = g⁻¹ := Matrix.star_eq_inv (A := g)
              simpa using congrArg Subtype.val h_star_eq_inv
        simp [fundamentalCharacter, h_val_inv, mul_comm, mul_left_comm]
  have h_trace_nonneg : 0 ≤ Matrix.trace (((∑ g ∈ s, (conj (c g) : ℂ) • ((g : SU N) : Matrix (Fin N) (Fin N) ℂ))ᴴ) * (∑ g ∈ s, (conj (c g) : ℂ) • ((g : SU N) : Matrix (Fin N) (Fin N) ℂ))) :=
    h_nonneg_sq ((∑ g ∈ s, (conj (c g) : ℂ) • ((g : SU N) : Matrix (Fin N) (Fin N) ℂ)) : Matrix (Fin N) (Fin N) ℂ)
  rw [← h_tr_eq]
  exact h_trace_nonneg

lemma PositiveDefinite.conj {G : Type*} [Group G] {φ : G → ℂ} (hφ : PositiveDefinite φ) :
    PositiveDefinite (λ g => conj (φ g)) := by
  intro s c
  have h := hφ s (λ g => conj (c g))
  -- h: ∑ conj(c i) * conj(conj(c j)) * φ(i⁻¹ * j) ≥ 0
  have h_simp : (∑ i ∈ s, ∑ j ∈ s, conj (c i) * c j * φ (i⁻¹ * j)) ≥ 0 := by
    simpa [star_star] using h
  rcases Complex.nonneg_iff.mp h_simp with ⟨h_re, h_im⟩
  have h_im_zero : (∑ i ∈ s, ∑ j ∈ s, conj (c i) * c j * φ (i⁻¹ * j)).im = 0 := h_im.symm
  have h_conj_eq : conj (∑ i ∈ s, ∑ j ∈ s, conj (c i) * c j * φ (i⁻¹ * j)) =
      (∑ i ∈ s, ∑ j ∈ s, conj (c i) * c j * φ (i⁻¹ * j)) :=
    (Complex.conj_eq_iff_im.mpr h_im_zero)
  have h_target : (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * conj (φ (i⁻¹ * j))) =
      conj (∑ i ∈ s, ∑ j ∈ s, conj (c i) * c j * φ (i⁻¹ * j)) := by
    simp [map_sum, mul_comm, mul_left_comm]
  rw [h_target, h_conj_eq]
  exact h_simp

lemma reTrace_positiveDefinite (N : ℕ) :
    PositiveDefinite (λ (g : SU N) => ((Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re : ℂ)) := by
  have h_trace_re_eq : ∀ (g : SU N), ((Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re : ℂ) =
      (fundamentalCharacter N g + conj (fundamentalCharacter N g)) / 2 := by
    intro g
    calc
      ((Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re : ℂ) =
        ((fundamentalCharacter N g).re : ℂ) := by simp [fundamentalCharacter]
      _ = (fundamentalCharacter N g + conj (fundamentalCharacter N g)) / 2 := by
        rw [Complex.re_eq_add_conj]
  have h_scaled : PositiveDefinite (λ (g : SU N) => (fundamentalCharacter N g + conj (fundamentalCharacter N g)) / 2) := by
    have h_sum : PositiveDefinite (λ g : SU N => fundamentalCharacter N g + conj (fundamentalCharacter N g)) :=
      PositiveDefinite.add (fundamentalCharacter_positiveDefinite N) (PositiveDefinite.conj (fundamentalCharacter_positiveDefinite N))
    have h_half_nonneg : (0 : ℝ) ≤ 1/2 := by norm_num
    have h_smul := PositiveDefinite.smul_nonneg h_half_nonneg h_sum
    simpa [div_eq_inv_mul, smul_eq_mul] using h_smul
  simpa [h_trace_re_eq] using h_scaled

lemma exp_reTrace_positiveDefinite (N : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    PositiveDefinite (λ (g : SU N) => (Real.exp (c * ((Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re : ℝ)) : ℂ)) := by
  set h : SU N → ℝ := fun g => (Matrix.trace (g : Matrix (Fin N) (Fin N) ℂ)).re
  set f : SU N → ℂ := fun g => (h g : ℂ)
  have hf : PositiveDefinite f := by
    have := reTrace_positiveDefinite N
    convert this using 1
  set S : ℕ → SU N → ℂ := fun n g =>
    ∑ k ∈ Finset.range n, ((c ^ k / k.factorial : ℝ) : ℂ) * ((f ^ k) g)
  have hS_PD : ∀ n, PositiveDefinite (S n) := by
    intro n
    induction n with
    | zero => simp [S, Finset.sum_empty]; exact PositiveDefinite.zero
    | succ n ih =>
      have hterm : PositiveDefinite (λ g => ((c ^ n / n.factorial : ℝ) : ℂ) * ((f ^ n) g)) := by
        apply PositiveDefinite.smul_nonneg
        · exact div_nonneg (pow_nonneg hc n) (Nat.cast_nonneg _)
        · exact PositiveDefinite.pow hf n
      have hadd : PositiveDefinite (λ g => S n g + ((c ^ n / n.factorial : ℝ) : ℂ) * ((f ^ n) g)) :=
        PositiveDefinite.add ih hterm
      have heq : S (n + 1) = (λ g => S n g + ((c ^ n / n.factorial : ℝ) : ℂ) * ((f ^ n) g)) := by
        funext g
        simp only [S, Finset.sum_range_succ]
      rw [heq]
      exact hadd
  have hS_tendsto : ∀ g, Tendsto (fun n => S n g) atTop (nhds ((Real.exp (c * h g)) : ℂ)) := by
    intro g
    have hexp : HasSum (fun k => (c * h g) ^ k / k.factorial) (Real.exp (c * h g)) := by
      have := NormedSpace.expSeries_div_hasSum_exp (c * h g)
      rwa [← Real.exp_eq_exp_ℝ] at this
    have hT_tendsto : Tendsto (fun n => ∑ k ∈ Finset.range n, (c * h g) ^ k / k.factorial) atTop
        (nhds (Real.exp (c * h g))) := hexp.tendsto_sum_nat
    have hSeq : ∀ n, S n g = ((∑ k ∈ Finset.range n, (c * h g) ^ k / k.factorial : ℝ) : ℂ) := by
      intro n
      simp only [S, f, h, Pi.pow_apply, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_div,
        Complex.ofReal_sum, mul_pow, mul_div_assoc, div_mul_eq_mul_div]
    rw [show (fun n => S n g) = (fun n =>
        ↑(∑ k ∈ Finset.range n, (c * h g) ^ k / k.factorial)) from by funext n; exact hSeq n]
    exact (Complex.continuous_ofReal.tendsto _).comp hT_tendsto
  exact PositiveDefinite.tendsto hS_PD hS_tendsto

end SU_N
