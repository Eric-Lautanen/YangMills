# Yang-Mills Millennium Prize — Lean 4 Formalization

A Lean 4 formalization effort around the mathematical foundations of quantum
Yang-Mills theory, undertaken with the long-term goal of a formally verified
proof of the Yang-Mills existence and mass gap conjecture (Clay Millennium
Prize Problem).

**Status as of this update: the Millennium Prize theorem is NOT proved.**
The top-level statement currently depends on an axiom
(`mass_gap_axiom`) that is logically equivalent to the conjecture itself.
Any derivation from that axiom is circular and should not be read as
progress on the open problem. See "Status of the Millennium Prize Theorem"
below before reading anything else in this document.

> **Maintenance note:** this README must be kept in sync with the actual
> Lean source on every session that touches the proof state (new lemmas,
> new axioms, new sorries, sorries closed, axioms removed). Do not let
> claims here drift ahead of — or behind — what `lake build` and
> `#print axioms` actually report. See "Keeping this README honest" at the
> bottom.

---

## Status of the Millennium Prize Theorem

**Not proved.** The formalization currently rests on **six** axioms (not
four — `MassGapProof.lean`'s module docstring says "four axioms" and then
lists five; that docstring needs fixing too), one of which (`mass_gap_axiom`)
directly encodes the conjecture being proved. Any theorem chain that
terminates in this axiom is not a proof of anything new — it is a
restatement.

| Axiom | Declared in | What it stands in for | Status / concern |
|---|---|---|---|
| `peterWeyl_clebschGordan_plaquette` | `PeterWeyl.lean` | Peter–Weyl theorem + Clebsch–Gordan decomposition for the plaquette Boltzmann factor **and** for products of characters of the same group element (across-plaquette CG) **and** dual (contragredient) representations | Neither is in Mathlib. Defensible as a cited external theorem *if* correctly applied — needs audit. The axiom was **strengthened** (2026-07-03 session) to also provide the CG decomposition `χ_s(g)·χ_t(g) = ∑_w cg s t w · χ_w(g)` with `cg s t w ≥ 0` (Littlewood–Richardson), which is the key ingredient for combining character expansions across plaquettes that share a link variable. The axiom was **further strengthened** (2026-07-30 session) to also provide a dual map `dual : ι → ι` with `χ_{dual(i)}(g) = conj(χ_i(g))` (the contragredient representation has conjugate character), which is needed to handle inverted links in the plaquette product (`χ(g⁻¹) = conj(χ(g)) = χ_{dual}(g)` by `repCharacter_inv`). Two new lemmas proved from the strengthened axiom (0 sorries, 0 custom axioms): `charProduct_PD` (product of two chars is PD via CG) and `charProduct_finset_decomp` (finite product of chars of the same element decomposes as a non-negative-weighted sum of single characters via iterated CG). |
| `transferMatrixPositivity_axiom` | `ReflectionPositivity.lean` (**confirmed** — not a `sorry`, and not in `TransferMatrix.lean` despite `Overview.lean` implying otherwise) | Positivity of `∫ G(U)·G(θU) dμ₀` for the periodic-lattice transfer matrix | Docstring gives a real justification chain (plaquette PD ⇒ transfer matrix positive ⇒ integral nonnegative). All abstract sub-steps are now proved (see "Suggested next step" below). The clean factorization `osG_thetaG_factorization` (0 sorries, 0 axioms) shows the axiom is equivalent to `∫ f(U)·f(θU)·exp(-β S_W(U)) dμ ≥ 0`. The full Boltzmann factor `exp(-β S_W)` is proved PD on the full link group by `boltzmannFactorPD` (modulo Peter–Weyl). **Key obstruction**: this integral is NOT the standard PD quadratic form `∫∫ f(g)·conj(f(h))·K(g⁻¹h) dμ dμ ≥ 0` (which follows from PD-ness of `K` and is proved as `integralOperator_nonneg`). It is a *single* integral `∫ f(g)·f(θg)·K(g) dμ` with the geometric reflection `θ` and `K` evaluated at `g` (not `g⁻¹h`). PD-ness of `K` does not imply this is non-negative; the Peter–Weyl character expansion of `K` and character orthogonality are needed to decompose the integrand into `|Fourier coefficients|²`. This is a fundamental mathematical gap, not just formalization work. |
| `os_reconstruction_theorem` | `OSAxioms.lean` | Osterwalder–Schrader reconstruction (OS axioms ⇒ Wightman QFT) | Established published math, not in Mathlib. Only sound to invoke on objects that actually satisfy the OS axioms — depends on the continuum limit existing (see next row). |
| `continuum_limit_exists` | `ContinuumLimit.lean` | Existence of the lattice a→0 continuum limit (Balaban RG / stochastic quantization) | **This axiom *is* the open mathematical core of the problem.** Not a placeholder for something routine — it's the thing nobody has proved. |
| `mass_gap_axiom` | `MassGap.lean` | Positivity of the continuum mass gap | **This is the conjecture itself.** `yang_mills_existence_and_mass_gap` in `MassGapProof.lean` pulls the gap and its positivity directly from this axiom (`let mg := mass_gap_axiom a ha`) without deriving anything from the lattice work — the clearest concrete illustration of the circularity in the codebase. Must not be used in any theorem claimed as a "proof" of the Millennium Prize result. |
| `characterOrthogonality` | `PositiveDefinite.lean` | Schur orthogonality for irreducible unitary representations of a compact group | Not in Mathlib. The **Great Orthogonality Theorem**: `∫ χ_λ(g)·conj(χ_μ(g)) dμ = δ_{λμ}` for normalized Haar measure. This is the key ingredient needed to turn the Peter–Weyl character expansion of the Boltzmann factor into the `|Fourier coefficient|²` decomposition of the reflection-positivity integral. Defensible as a cited external theorem. |

Any file, comment, or summary claiming the top-level theorem is "proved"
while it depends on `mass_gap_axiom` is wrong and should be corrected.

### Suggested next step: wire the abstract lemmas into the lattice setup to close `transferMatrixPositivity_axiom`

Unlike the other four axioms, this one looks achievable with what's already
built. Its docstring lays out the chain: the plaquette Boltzmann factor is
positive-definite (`plaquetteBoltzmannPD`, proved modulo the Peter–Weyl
axiom) ⟹ the transfer matrix built from it is a positive operator ⟹ the
integral is nonnegative. All abstract sub-steps are now proved:

1. `PositiveDefinite.integral` — an integral average of PD functions is PD
   (closes "integrate out interior links ⟹ PD kernel").
2. `PositiveDefinite.integralOperator_nonneg` — a PD kernel on a compact
   group defines a positive integral operator
   (`∫∫ f(x)·conj(f(y))·K(x⁻¹y) dμ dμ ≥ 0`; closes "PD kernel ⟹ positive
   operator").  The proof approximates the integral by Riemann sums and
   controls the error via uniform continuity on `G × G`.
3. `PositiveDefiniteKernel.integralOperator_nonneg` — the **Mercer-type**
   generalization: a continuous Mercer-PD kernel on a compact space (no group
   structure needed) defines a positive integral operator.  This removes the
   group-structure requirement that obstructs the group-theoretic version.
4. `boltzmannFactorPD` (`BoltzmannFactor.lean`) — the **full Boltzmann factor**
   `exp(-β S_W) = ∏ exp(-S_p)` is PD on the full link-variable group, via
   `plaquetteContributionPD` (each plaquette factor PD by `comp_hom` from
   `plaquetteBoltzmannPD_inv`) and `PositiveDefinite.finprod` (n-ary Schur
   product).  0 sorries, 0 axioms beyond Peter–Weyl.
5. `osG_thetaG_factorization` (`ReflectionPositivity.lean`) — the clean
   algebraic identity `osG(U)·osG(θU) = f(U)·f(θU)·exp(-β S_W(U))`, showing
   the axiom is equivalent to `∫ f(U)·f(θU)·exp(-β S_W) dμ ≥ 0`.  0 sorries,
   0 axioms.

All are 0 sorries, 0 custom axioms (only Peter–Weyl for the plaquette PD).
The **remaining** work is the fundamental mathematical gap: the integral
`∫ f(U)·f(θU)·exp(-β S_W) dμ` is NOT the standard PD quadratic form
`∫∫ f(g)·conj(f(h))·K(g⁻¹h) dμ dμ ≥ 0` — it is a single integral with the
geometric reflection `θ` and `K` evaluated at `g` (not `g⁻¹h`).  PD-ness of
`K` does not imply this is non-negative; the Peter–Weyl character expansion
of `K` and character orthogonality are needed to decompose the integrand
into `|Fourier coefficients|²`.  Closing it, even leaving
`peterWeyl_clebschGordan_plaquette` as an axiom, would be a genuine reduction
in the codebase's assumption count (six axioms → five).

### The character-orthogonality path to closing `transferMatrixPositivity_axiom`

The newly added `characterOrthogonality` axiom (in `PositiveDefinite.lean`)
provides the key missing ingredient for the reflection-positivity argument.
The path is:

1. The full Boltzmann factor `K = exp(-β S_W)` has a Peter–Weyl character
   expansion `K = ∑_λ a_λ χ_λ` with `a_λ ≥ 0` (axiomatized by
   `peterWeyl_clebschGordan_plaquette`, applied plaquette-by-plaquette and
   multiplied via `boltzmannFactorPD`).
2. The reflection-positivity integral `∫ f(U)·f(θU)·K(U) dμ` (shown
   equivalent to the axiom by `osG_thetaG_factorization`) becomes, after
   substituting the character expansion, a sum of terms
   `∑_λ a_λ · ∫ f(U)·f(θU)·χ_λ(U) dμ`.
3. Using the reflection symmetry of the Haar measure (`μ(θA) = μ(A)`) and
   character orthogonality (`characterOrthogonality`), each term
   `∫ f(U)·f(θU)·χ_λ(U) dμ` can be rewritten as `|∫ f(U)·χ_λ(U) dμ|² ≥ 0`
   (a squared Fourier coefficient).
4. Since `a_λ ≥ 0` and `|·|² ≥ 0`, the entire sum is non-negative.

Steps 1–2 are already formalized (`boltzmannFactorPD`,
`osG_thetaG_factorization`).  Step 3 requires the `characterOrthogonality`
axiom (now added) plus the reflection-invariance of the Haar measure
(`μ(θA) = μ(A)`, which follows from the Haar measure being invariant under
all measure-preserving maps, including the reflection `θ`).  Step 4 is
trivial algebra.  The remaining formalization work is the concrete wiring
of steps 3–4 into the lattice-gauge-theory setup.

**Precise analysis (2026-06-29 session):** the naive path above (steps 1–4
at the level of the full Boltzmann factor) does NOT work directly, because
`χ_λ(θU) ≠ conj(χ_λ(U))` in general — the reflection `θ` is not group
inversion.  The correct approach works at the level of the **transfer matrix
kernel** `K_TM(u, U⁻)`, which must decompose as
`∑_λ a_λ Φ_λ(u) · conj(Φ_λ(θ⁻⁰(U⁻, u⁰)))` with `a_λ ≥ 0`.  The change of
variables `U⁻ ↦ θ⁻⁰(U⁻, u⁰)` (measure-preserving by
`reflectLinkVariable_measurePreserving`) then turns the integral into a sum
of `|Fourier coefficients|² ≥ 0`.  The key obstruction to formalizing this
kernel decomposition is that the interface Boltzmann factor is a **product
of multiple plaquette factors**, and combining their character expansions
requires the **Clebsch–Gordan decomposition** for products of characters of
the same link variable — not currently axiomatized.  See
`docs/gap_analysis.md` for the full analysis.

**Further analysis (2026-07-02 session):** a detailed investigation of whether
the abstract lemma `character_expansion_positivity` (proved 2026-07-01, 0
sorries, 0 axioms) can be directly wired into the lattice setup revealed
**three interconnected obstructions** that prevent direct application:

1. **`θ⁻⁰` depends on both `x` and `y`.**  The lemma requires `θ : Y → X` (a
   function of `y` only), but `θ⁻⁰(U⁻, u⁰)` depends on `u⁰`, which is part of
   `x = u = (u⁺, u⁰)`.
2. **The pushforward of `μ⁻` by `θ⁻⁰(·, u⁰)` is singular.**  Even generalized
   to allow `x`-dependent `θ`, the pushforward is `μ⁺ × δ_{σ(u⁰)}` (a point
   mass at the reflected interface config), NOT the full `μ⁺⁰ = μ⁺ × μ⁰`.
   The change of variables gives an integral over a slice, not the full space.
3. **The `σ` reflection on interface time-like links.**  The reflection
   inverts interface time-like links (`g ↦ g⁻¹`), causing `χ(g)²` instead of
   `|χ(g)|²` in the separable form.  The result would be
   `∑ a_i ∫ A_i(u⁰) conj(A_i(σ(u⁰))) dμ⁰(u⁰)`, which is NOT necessarily
   non-negative.

**Conclusion:** `character_expansion_positivity` is NOT the right scaffold for
the lattice case.  The correct approach (from the Osterwalder–Seiler proof) is
the **operator-theoretic** argument: show the transfer matrix `T = B* · B` for
some operator `B` defined via the character expansion (Peter–Weyl + CG), then
`⟨g, Tg⟩ = ‖Bg‖² ≥ 0`.  This requires (a) a Clebsch–Gordan axiom for products
of characters of the same group element, and (b) the full combinatorial wiring
of the interface plaquette expansion.  See `docs/gap_analysis.md` §"Precise
analysis of why `character_expansion_positivity` does NOT directly apply" for
the full analysis.

**Progress (2026-07-03 session):** Step (a) is now complete.  The
`peterWeyl_clebschGordan_plaquette` axiom has been **strengthened** to also
provide the Clebsch–Gordan decomposition for character products:
`χ_s(g)·χ_t(g) = ∑_w cg s t w · χ_w(g)` with `cg s t w ≥ 0` (Littlewood–
Richardson).  This is the "across-plaquette" CG that was identified as the key
missing ingredient — it allows combining character expansions when the same
link variable appears in multiple plaquettes.  Two new lemmas proved from the
strengthened axiom (0 sorries, 0 custom axioms — verified by `#print axioms`):
`charProduct_PD` (product of two chars is PD via CG) and
`charProduct_finset_decomp` (finite product of chars of the same element
decomposes as a non-negative-weighted sum of single characters via iterated
CG).  Two further lemmas proved from the strengthened axiom (0 sorries, 0
custom axioms — verified by `#print axioms`): `charSum_product_decomp`
(product of two non-negative-weighted char sums decomposes as a
non-negative-weighted char sum via CG) and `charSum_finprod_decomp` (finite
product of non-negative-weighted char sums decomposes as a
non-negative-weighted char sum via iterated CG).  The axiom count remains
**six** (the strengthening enriches an existing axiom, it does not add a new
one).  Step (b) — formalizing the operator `B` and showing `T = B* · B` —
remains the major formalization effort.

## What is actually proved (no sorry, no axiom)

### SU(N) and general algebra
- `CompactSpace (SU N)`, `SecondCountableTopology (SU N)`
- `trace_commutator_zero`, `trace_mul_rotate`, `trace_unitary_conj_invariant`,
  `trace_sq_invariant`, `jacobi_identity`
- `adjointAction_preserves_trace_sq`, `adjointAction_preserves_skewHermitian`,
  `adjointAction_preserves_traceless`
- `lagrangian_gauge_invariant`

### Positive-definite function algebra
- `PositiveDefinite.add`, `.smul_nonneg`, `.conj_inv`, `.zero`, `.one`
- `PositiveDefinite.mul` (Schur product theorem / Hadamard product of PSD
  matrices)
- `PositiveDefinite.pow`, `.tendsto`, `.prod`, `.sum`, `.sum'`
- `repCharacter_positiveDefinite`, `fundamentalCharacter_positiveDefinite`,
  `reTrace_positiveDefinite`
- `IsUnitaryRepresentation`, `repCharacter`, `repCharacter_inv`
  (`χ(g⁻¹) = conj(χ(g))`)
- `IsIrreducible` — a unitary representation is irreducible if the only
  invariant subspaces are `{0}` and the whole space
- `characterOrthogonality` (axiom) — Schur orthogonality for irreducible
  unitary representations of a compact group: `∫ χ_λ·conj(χ_μ) dμ = δ_{λμ}`
  for normalized Haar measure.  Not in Mathlib; the key ingredient for the
  `|Fourier coefficient|²` decomposition of the reflection-positivity integral.
- `exp_reTrace_positiveDefinite` (single-link Boltzmann factor; proved
  unconditionally via the power-series / `PositiveDefinite.tendsto` argument —
  no axiom)
- `plaquetteBoltzmannPD` (depends on the `peterWeyl_clebschGordan_plaquette`
  axiom above — flagged, not unconditional)
- `plaquetteBoltzmannPD_inv` (`PeterWeyl.lean`) — the plaquette Boltzmann
  factor with inverse links `exp(c·Re Tr(g₁ g₂ g₃⁻¹ g₄⁻¹))` is PD on
  `SU(N)⁴` (the version needed for the actual lattice plaquette product;
  depends on the Peter–Weyl axiom)
- `charProduct_PD` (`PeterWeyl.lean`) — the product of two characters of the
  *same* group element `χ_s(g)·χ_t(g)` is PD, via the Clebsch–Gordan
  decomposition `χ_s·χ_t = ∑_w cg s t w · χ_w` with `cg s t w ≥ 0` (provided
  by the strengthened `peterWeyl_clebschGordan_plaquette` axiom).  0 sorries,
  0 custom axioms beyond Peter–Weyl.  Verified by `#print axioms` (only
  `propext`, `Classical.choice`, `Quot.sound`).
- `charProduct_finset_decomp` (`PeterWeyl.lean`) — a finite product of
  characters of the same group element `∏_{i ∈ s} χ_i(g)` decomposes as a
  non-negative-weighted sum of single characters `∑_w coeff w · χ_w(g)` with
  `coeff w ≥ 0`, via iterated Clebsch–Gordan.  This is the key algebraic
  ingredient for the transfer-matrix kernel decomposition: when a single link
  variable appears in multiple interface plaquettes, the product of the
  character expansions produces a product of characters of that link, which
  this lemma reduces to a single non-negative sum.  0 sorries, 0 custom axioms
  beyond Peter–Weyl.  Verified by `#print axioms` (only `propext`,
  `Classical.choice`, `Quot.sound`).
- `charSum_product_decomp` (`PeterWeyl.lean`) — the product of two
  non-negative-weighted sums of characters `(∑_a c1 a · χ_a) · (∑_b c2 b · χ_b)`
  decomposes as a non-negative-weighted sum of single characters
  `∑_w coeff w · χ_w` with `coeff w = ∑_{a,b} c1 a · c2 b · cg a b w ≥ 0`,
  via Clebsch–Gordan.  This is the key algebraic ingredient for combining
  character expansions across plaquettes that share a link variable.  0 sorries,
  0 custom axioms beyond Peter–Weyl.  Verified by `#print axioms` (only
  `propext`, `Classical.choice`, `Quot.sound`).
- `charSum_finprod_decomp` (`PeterWeyl.lean`) — a finite product of
  non-negative-weighted sums of characters
  `∏_{a ∈ s} (∑_w f a w · χ_w(g))` decomposes as a non-negative-weighted sum
  of single characters `∑_w coeff w · χ_w(g)` with `coeff w ≥ 0`, via iterated
  Clebsch–Gordan (induction on `s` using `charSum_product_decomp`).  This is
  the key lemma for the interface Boltzmann factor decomposition: after
  collecting characters by link variable, each link's contribution is a
  non-negative-weighted sum of characters, and this lemma shows the product
  over all links is again a non-negative-weighted sum of characters.  0
  sorries, 0 custom axioms beyond Peter–Weyl.  Verified by `#print axioms`
  (only `propext`, `Classical.choice`, `Quot.sound`).
- `charSum_product_link_decomp` (`PeterWeyl.lean`) — the product of per-link
  non-negative-weighted character sums `∏_l (∑_w f l w · χ_w(g_l))` decomposes
  as a non-negative-weighted sum of products of characters
  `∑_{w : L → ι} F(w) · ∏_l χ_{w(l)}(g_l)` with `F(w) = ∏_l f l (w l) ≥ 0`.
  This is the "product of sums = sum of products" identity (`Fintype.prod_sum`),
  applied to character sums.  It is the key ingredient for the interface
  Boltzmann factor decomposition: after the per-link CG reduction (via
  `charSum_finprod_decomp`), each link's contribution is a non-negative-weighted
  character sum, and this lemma shows the product over all links is again a
  non-negative-weighted sum of products of characters — i.e., a separable
  decomposition of the full Boltzmann factor.  0 sorries, 0 custom axioms
  beyond Peter–Weyl.  Verified by `#print axioms` (only `propext`,
  `Classical.choice`, `Quot.sound`).
- `charProduct_finset_decomp'` (`PeterWeyl.lean`) — generalized CG
  decomposition for a product of characters indexed by a finset of *appearances*
  `A` via `appChar : A → ι`: `∏_{a ∈ s} χ_{appChar(a)}(g) = ∑_w coeff w · χ_w(g)`
  with `coeff w ≥ 0`.  This handles the case where the same character index
  appears multiple times (e.g., when a link variable appears in multiple
  plaquettes with the same representation index).  0 sorries, 0 custom axioms
  beyond Peter–Weyl.  Verified by `#print axioms` (only `propext`,
  `Classical.choice`, `Quot.sound`).
- `charProduct_link_separable_decomp` (`PeterWeyl.lean`) — per-term separable
  decomposition: a product of characters grouped by link
  `∏_l (∏_{a ∈ S_l} χ_{charIdx l a}(g_l))` decomposes as a non-negative-weighted
  sum of products of single characters `∑_w F(w) · ∏_l χ_{w(l)}(g_l)` with
  `F(w) ≥ 0`.  This is the key algebraic ingredient for the interface Boltzmann
  factor decomposition: after expanding the product of plaquette factors
  (product of sums = sum of products), each term is a product of characters
  grouped by link, and this lemma shows each such term has a separable character
  decomposition with non-negative coefficients.  0 sorries, 0 custom axioms
  beyond Peter–Weyl.  Verified by `#print axioms` (only `propext`,
  `Classical.choice`, `Quot.sound`).
- `charProduct_mixed_finset_decomp'` (`PeterWeyl.lean`) — mixed-conjugation CG
  decomposition: a product of characters with mixed conjugation (some `χ(g)`,
  some `conj(χ(g))`) of the same group element decomposes as a non-negative-
  weighted sum of single characters `∑_w coeff w · χ_w(g)` with `coeff w ≥ 0`.
  The dual map converts `conj(χ)` to `χ_{dual}`, allowing `charProduct_finset_decomp'`
  to combine them.  This is the key lemma for the interface Boltzmann factor
  decomposition with inverted links.  0 sorries, 0 custom axioms beyond Peter–Weyl.
  Verified by `#print axioms` (only `propext`, `Classical.choice`, `Quot.sound`).
- `charProduct_mixed_link_separable_decomp` (`PeterWeyl.lean`) — per-term
  separable decomposition with mixed conjugation: a product of characters (some
  conjugated, some not) grouped by link decomposes as a non-negative-weighted sum
  of products of single (unconjugated) characters `∑_w F(w) · ∏_l χ_{w(l)}(g_l)`
  with `F(w) ≥ 0`.  This is the key algebraic ingredient for the interface
  Boltzmann factor decomposition with inverted links: after expanding the
  product of plaquette factors, each term is a product of characters (some
  conjugated from inverted links) grouped by link, and this lemma shows each
  such term has a separable character decomposition with non-negative
  coefficients, with all conjugation resolved via the dual map.  0 sorries,
  0 custom axioms beyond Peter–Weyl.  Verified by `#print axioms` (only
  `propext`, `Classical.choice`, `Quot.sound`).
  `LinkVariable (SU N) Λ`, via `plaquetteContributionPD` (each plaquette
  factor PD by `comp_hom` from `plaquetteBoltzmannPD_inv`) and
  `PositiveDefinite.finprod` (n-ary Schur product).  0 sorries, 0 axioms
  beyond Peter–Weyl.
- `osG_thetaG_factorization` (`ReflectionPositivity.lean`) — the clean
  algebraic identity `osG(U)·osG(θU) = f(U)·f(θU)·exp(-β S_W(U))`, showing
  `transferMatrixPositivity_axiom` is equivalent to
  `∫ f(U)·f(θU)·exp(-β S_W) dμ ≥ 0`.  0 sorries, 0 axioms.
- `PositiveDefinite.integral` (`PositiveDefiniteIntegral.lean`) — the
  *continuous* analogue of `PositiveDefinite.sum`: an integral average of
  positive-definite functions is positive-definite.  Verified by
  `#print axioms` to depend on no custom axiom (only `propext`,
  `Classical.choice`, `Quot.sound`), 0 sorries.  This closes the "integrate out
  interior links ⟹ the resulting kernel is PD" step of the transfer-matrix
  positivity argument.
- `PositiveDefinite.integralOperator_nonneg` (`PositiveDefiniteIntegral.lean`)
  — for a compact group `G` with probability measure `μ`, a continuous PD
  function `φ`, and a continuous `f`, `∫∫ f(x)·conj(f(y))·φ(x⁻¹y) dμ dμ ≥ 0`.
  The proof approximates the integral by Riemann sums (each non-negative by
  `PositiveDefinite.sum_nonneg_of_map`) and controls the error via uniform
  continuity on `G × G`.  Verified by `#print axioms` to depend on no custom
  axiom, 0 sorries.  This closes the "PD kernel ⟹ positive integral operator"
  step.  Together with `PositiveDefinite.integral`, both abstract sub-steps of
  the transfer-matrix positivity chain are now proved; the remaining work is
  the concrete wiring into the lattice-gauge-theory setup.
- `PositiveDefiniteKernel` (`PositiveDefiniteIntegral.lean`) — Mercer-type
  PD kernel (no group structure needed): `K : X → X → ℂ` with
  `∑ c_i ·conj(c_j)·K(x_i, x_j) ≥ 0` for every finite set and coefficients.
  Building blocks (all 0 sorries, 0 axioms): `PositiveDefiniteKernel.conj_symm`
  (Hermitian symmetry), `.one` (constant-one kernel), `.mul` (Schur/Hadamard
  product theorem), `.smul_nonneg`, `.finprod` (n-ary Schur product), `.comp`
  (PD preserved by composition with `f : X → Y`), `.continuous_comp`
  (continuity preserved by composition), `.sum_nonneg_of_map` (non-injective
  index map), and `PositiveDefinite.toPositiveDefiniteKernel` (group-PD →
  Mercer-PD).
- `PositiveDefiniteKernel.integralOperator_nonneg`
  (`PositiveDefiniteIntegral.lean`) — the Mercer-type generalization: a
  continuous Mercer-PD kernel on a compact space (no group structure needed)
  defines a positive integral operator
  `∫∫ f(x)·conj(f(y))·K(x, y) dμ dμ ≥ 0`.  0 sorries, 0 custom axioms.
- `character_expansion_positivity` and `character_expansion_nonneg`
  (`PositiveDefiniteIntegral.lean`) — the **abstract character-expansion
  scaffold** for the reflection-positivity argument.  If a kernel
  `K : X → Y → ℂ` has a finite separable decomposition
  `K(x, y) = ∑_i a_i · Φ_i(x) · conj(Φ_i(θ y))` with `θ` measure-preserving
  (`θ_*ν = μ`), then for real-valued `f`:
  `∫∫ f(x)·f(θ y)·K(x, y) dν dμ = ∑_i a_i · ‖∫ f·Φ_i dμ‖²` (the identity), and
  with `a_i ≥ 0` this is non-negative (the corollary).  No group structure, no
  character orthogonality — only the measure-preserving change of variables and
  `f` real-valued.  This is the abstract scaffold that the concrete Peter–Weyl
  character expansion of the transfer-matrix kernel would plug into; it does
  **not** close `transferMatrixPositivity_axiom` (which requires showing the TM
  kernel has the required separable decomposition — the Clebsch–Gordan gap).
  Verified by `#print axioms` (only `propext`, `Classical.choice`,
  `Quot.sound`), 0 sorries, 0 custom axioms.

**Two independent verification checks were performed on both lemmas:**
1. **`#print axioms`** — confirms no hidden axiom or `sorry` in the dependency
   tree (only `propext`, `Classical.choice`, `Quot.sound`).  This catches
   *undeclared assumptions* but would not catch a subtly wrong-but-compiling
   argument.
2. **Independent code review** — the full proof scripts (lines 78–153 for
   `integral`, lines 172–378 for `integralOperator_nonneg`) were read
   line-by-line and checked for logical soundness: the Fubini swap, the
   a.e.-non-negativity of the PD quadratic-form integrand, the Riemann-sum
   construction, the uniform-continuity error bound, and the final
   `Complex.nonneg_iff` split.  This confirms the *logic* is sound, not just
   that the kernel accepted it.

These are complementary: a clean `#print axioms` alone would not have caught
a wrong-but-still-compiling argument, and a code review alone would not have
caught a silently-introduced axiom.  Both were done.

**Mathlib-absence verification.** Both `PositiveDefinite.integral` and
`PositiveDefinite.integralOperator_nonneg` were checked against the current
Mathlib version (pinned in `lake-manifest.json`) and confirmed **absent** via
multiple independent search angles:

- `PositiveDefinite` as a bare identifier does not exist anywhere in Mathlib
  (the matrix/quadratic-form positive-definiteness machinery Mathlib does have
  — `Matrix.PosDef`, `PosSemidef`, etc. — never touches Haar measure anywhere
  in the codebase; `grep` for the intersection returns zero files).
- Loogle search `IsCompact _ -> _ -> 0 ≤ _` over all 126 declarations
  mentioning both `IsCompact` and `LE.le` returns **no matches** — a genuine
  negative from the search index, not a grep miss.
- Loogle search `0 ≤ ∫ _, _ ∂_` returns 13 hits, every one of which is
  generic integral-nonnegativity from a pointwise-nonnegative integrand
  (`integral_nonneg`, `setIntegral_nonneg`, AE-equality lemmas).  Nothing
  group-theoretic, nothing kernel-based, nothing resembling "PD kernel ⟹
  positive operator."
- Related concepts (Godement's theorem on positive-definite functions,
  Bochner theorem for groups, unitary-representation character machinery,
  convolution on compact groups) are likewise not present under those names.

This is a multi-angle confirmation that these two lemmas are genuinely new to
Mathlib, not a rediscovery of existing infrastructure.  The framing is
therefore "confirmed absent from Mathlib as of this Mathlib version," not
"might be reusable Mathlib-adjacent infrastructure" — a stronger, citable
claim if this work is ever upstreamed.

**Key Mathlib API names verified against pinned version.** The proof of
`integralOperator_nonneg` depends on two non-trivial Mathlib lemmas whose
names were checked against the pinned Mathlib commit
(`3bc2a1801c2416549ba5ba0b3f5728a28b87e7d9`, Lean v4.33) to catch
toolchain-drift breakage proactively:

- `measureReal_prod_prod` — confirmed present in
  `Mathlib/MeasureTheory/Measure/Prod.lean` (as
  `_root_.MeasureTheory.measureReal_prod_prod`).
- `finite_cover_balls_of_compact` — confirmed present in
  `Mathlib/Topology/MetricSpace/Pseudo/Basic.lean` (with alias
  `IsCompact.finite_cover_balls`).

Both names match the current Mathlib; `lake build
YangMills.Proofs.PositiveDefiniteIntegral` succeeds with 0 errors.  This
file is **not** in the toolchain-drift-breakage risk category.

### Lattice action and reflection lemmas
- `reflectSite_involution`, `reflection_involution`
- `total_wilson_action_decomposition_z4` (S_W = S_W⁺ + S_W⁻ + S_W⁰)
- `neg_action_reflection_z4`, `interface_action_reflection_symmetric_z4`,
  `wilsonActionFiniteConfig_reflection_invariant`
- Periodic-site variants: `signedTime_neg`, `plaquette_classification`,
  `total_decomposition_os_periodic`, etc.
- `trace_plaquetteProduct_reflect_ss/_ts/_st/_tt`
- `neg_action_reflection_os_periodic`,
  `interface_action_reflection_symmetric_os_periodic`

### Measure theory
- `productHaarMeasure`, `IsProbabilityMeasure` instance
- `measurable_extendLinkVariable`, `measurable_wilsonActionFiniteConfig`
- `partitionFunctionFinite_pos` — **proved for both empty and nonempty
  sites** (earlier README versions incorrectly listed the nonempty case as
  a sorry — confirmed fixed, this entry corrects that)
- `gibbsExpectation_pos`, `gibbsExpectation_normalization`
- `gibbsExpectation_linear` — **proved, with integrability hypotheses
  added to the interface** (earlier README versions listed this as
  in-progress without hypotheses — confirmed this was resolved by adding
  the hypotheses, not by proving the false unconditional statement)
- `measurable_plaquetteContribution`,
  `measurable_wilsonActionOSPositive/Negative/Interface`
- `measure_factorization'` (μ₀ ≅ μ⁺ × μ⁻ × μ⁰, proved via `MeasurePreserving`)
  — verified by `#print axioms` (only `propext, Classical.choice, Quot.sound`),
  0 sorries, under the current Lean v4.33 toolchain.
- `haarMeasure_inv_invariant` (`LatticeMeasure.lean`) — the Haar measure on
  `SU(N)` is invariant under inversion `g ↦ g⁻¹`, i.e.
  `map Inv.inv (haarMeasure K) = haarMeasure K`.  **Proved** (0 sorries, 0
  custom axioms — verified by `#print axioms`: only `propext`,
  `Classical.choice`, `Quot.sound`).  The proof uses the standard
  compact-group unimodularity argument: `haarMeasure K` is right-invariant
  (compact groups are unimodular — `map (· * g) μ` is left-invariant and a
  probability measure, so by `isMulInvariant_eq_smul_of_compactSpace` it
  equals `haarScalarFactor • μ` with the scalar forced to `1` by
  `μ univ = 1`), hence `μ.inv` is left-invariant
  (`inv.instIsMulLeftInvariant`), and again by uniqueness `μ.inv = μ` since
  both are probability measures.  This is a known Mathlib fact, not a new
  result; the formalization work was the namespace/identifier plumbing
  (`Measure.map` vs `Matrix.map` shadowing, `Measure.haarScalarFactor`,
  `Measure.isMulInvariant_eq_smul_of_compactSpace`) and avoiding the
  dependent-rewrite motive failure when evaluating the scalar smul at
  `Set.univ` (via `congr_arg (fun ν => ν Set.univ) h_eq`).
- `reflectLinkVariable_measurePreserving` (`LatticeMeasure.lean`) — the
  reflection map `θ` on the full link-variable group is measure-preserving
  w.r.t. the product Haar measure.  **Proved** (0 sorries, 0 custom axioms —
  verified by `#print axioms`: only `propext`, `Classical.choice`,
  `Quot.sound`).  The statement carries the necessary hypothesis
  `hsites : ∀ n, n ∈ sites → reflectSite n ∈ sites` (which, since
  `ReflectSite.involution` makes `reflectSite` involutive, makes the
  reflection a bijection on `sites`).  The proof composes two
  measure-preserving maps via `MeasurePreserving.comp`: (1) the index
  permutation `(n, μ) ↦ (reflectSite n, μ)` preserves the product measure
  by `measurePreserving_piCongrLeft` (all factors are identical); (2)
  componentwise inversion on time-like links (μ = 0) preserves the product
  measure by `measurePreserving_pi` + `haarMeasure_inv_invariant` (spatial
  links use `MeasurePreserving.id`).  This is the key measure-theoretic
  ingredient for the character-orthogonality approach to closing
  `transferMatrixPositivity_axiom`.

### Transfer matrix
- `reflectToPosInterface`, `transferMatrixCorrect`, `G`, `g_posInterface`
  (definitions)
- `G_thetaG_factorization_clean`, `G_thetaG_factorization`
- `osG_thetaG_factorization` (`ReflectionPositivity.lean`) — the clean
  algebraic identity `osG(U)·osG(θU) = f(U)·f(θU)·exp(-β S_W(U))`,
  showing `transferMatrixPositivity_axiom` is equivalent to
  `∫ f(U)·f(θU)·exp(-β S_W) dμ ≥ 0`.  0 sorries, 0 axioms.
- `integral_G_thetaG_eq_inner_g_Tg` — the key identity linking the
  reflected Gibbs expectation to the transfer-matrix inner product;
  verified by `#print axioms` (only `propext, Classical.choice,
  Quot.sound`), 0 sorries, under the current Lean v4.33 toolchain.
- `measurable_G`, `integrand_measurable`, `measurable_reflectLinkVariable`
- `measure_factorization'` in `TransferMatrix.lean` —
  measure-preserving equivalence between the full lattice measure and the
  positive/negative/interface factorization. Verified by `#print axioms`
  (only `propext, Classical.choice, Quot.sound`), 0 sorries, under the
  current Lean v4.33 toolchain.

## Known incomplete / incorrect items

1. **Vacuous proof (`hadd` issue).** `gibbsExpectationZ4_reflection_positive`
   for the nonempty finite-lattice case only goes through because the
   `hadd` hypothesis (closure under forward time translation) forces
   `sites = ∅` on a finite lattice, making the "proof" true by
   contradiction rather than by establishing the actual inequality. **This
   is not a real theorem for any nonempty lattice.** Fix options: switch
   to periodic boundary conditions so `hadd` is satisfiable on a nonempty
   finite lattice, prove the nonempty case directly without `hadd`, or move
   to an infinite lattice. Until fixed, do not cite this lemma as
   establishing reflection positivity for any actual configuration.

2. **Periodic-lattice reflection positivity is unresolved — status now
   confirmed precisely.** `gibbsExpectationPeriodic_reflection_positive`
   closes via `exact transferMatrixPositivity_axiom ...`, a genuine `axiom`
   declared in `ReflectionPositivity.lean` (not a `sorry`, and not in
   `TransferMatrix.lean`). All of the algebraic and measure-theoretic
   bookkeeping around it — including `integral_G_thetaG_eq_inner_g_Tg`,
   `measure_factorization'`, and the clean factorization
   `osG_thetaG_factorization` — is fully proved; the axiom is the only gap.
   The clean factorization shows the axiom is equivalent to
   `∫ f(U)·f(θU)·exp(-β S_W) dμ ≥ 0`, and `boltzmannFactorPD` proves the
   Boltzmann factor `exp(-β S_W)` is PD on the full link group (modulo
   Peter–Weyl).  **However**, this integral is NOT the standard PD quadratic
   form that `integralOperator_nonneg` addresses — it is a single integral
   with the geometric reflection `θ` and `K` evaluated at `g` (not `g⁻¹h`).
   PD-ness of `K` does not imply non-negativity; the Peter–Weyl character
   expansion + the newly added `characterOrthogonality` axiom (Schur
   orthogonality) are needed to decompose the integrand into
   `|Fourier coefficients|²`.  See the "character-orthogonality path" above.

3. **Systematic audit for vacuous proofs not yet done.** The `hadd` pattern
   (item 1) is a known instance of a broader risk: any proof that goes
   through via deriving a false/unsatisfiable hypothesis rather than
   proving the stated claim. A full pass checking every top-level theorem
   (e.g. via `#print axioms` plus manual inspection for
   contradiction-derivation patterns) has not yet been completed.

4. **Repo hygiene (addressed).** The empty `Coq/` and `Z3/`
   placeholder directories and the stale `TransferMatrix_FIXED.lean.lf` /
   `TransferMatrix.lean.lf` intermediate-version files have been removed
   (they remain recoverable from git history). `TransferMatrix.lean` has
   unusual whitespace suggesting post-processing artifacts.
   `proofs/attempts.jsonl` is raw AI proof-attempt log output and is
   retained as a record of verification attempts; it is not part of the
   build.

5. **`Overview.lean` was stale (fixed).** It previously undersold:
   it claimed `integral_G_thetaG_eq_inner_g_Tg` "is not yet formalized" (false —
   it's proved, verified by `#print axioms`) and referenced a
   `transferMatrixCorrect_positive` lemma "currently sorry" that does not exist
   under that name (the real gap is the differently-named
   `transferMatrixPositivity_axiom` axiom, in `ReflectionPositivity.lean`).
   Both documents are now updated to match the source; the
   same continuous-maintenance discipline applies going forward.

6. **`TransferMatrix.lean` toolchain-drift build break — FIXED.** The
   repo's `lean-toolchain` was `v4.32.0-rc1` but `lake-manifest.json` pins
   a Mathlib commit requiring `v4.33.0-rc1`; `lake build` auto-bumps the
   toolchain and rebuilds.  Several `simp`-based proofs in
   `TransferMatrix.lean` (subtype-coercion goals in `measure_factorization'`
   and the bijectivity/equiv lemmas) no longer closed under the new `simp`
   normal form.  This was **toolchain drift**, not a logical error.  All
   break sites have been fixed this session; `TransferMatrix.lean` now
   builds cleanly under v4.33, and `#print axioms` on
   `measure_factorization'` and `integral_G_thetaG_eq_inner_g_Tg` confirms
   they depend only on `propext, Classical.choice, Quot.sound` (no custom
   axiom, 0 sorries).  The full `lake build` succeeds.

## Project structure

```
YangMills/
├── src/
│   ├── lean/
│   │   ├── YangMills.lean
│   │   └── YangMills/
│   │       ├── Overview.lean
│   │       ├── SpecialUnitary.lean
│   │       ├── OSAxioms.lean
│   │       ├── GaugeTheory.lean
│   │       ├── Lattice.lean
│   │       ├── MassGap.lean
│   │       ├── ContinuumLimit.lean      # invokes continuum_limit_exists
│   │       ├── MassGapProof.lean        # invokes mass_gap_axiom — see status warning above
│   │       └── Proofs/
│   │           ├── BasicLemmas.lean
│   │           ├── GaugeInvariance.lean
│   │           ├── JacobiIdentity.lean
│   │           ├── LatticeMeasure.lean
│   │           ├── PeterWeyl.lean               # Peter–Weyl axiom, plaquetteBoltzmannPD(_inv)
│   │           ├── PositiveDefinite.lean       # PD function algebra (add, mul, prod, finprod, …)
│   │           ├── PositiveDefiniteIntegral.lean  # PD.integral, integralOperator_nonneg, Mercer-PD kernels
│   │           ├── BoltzmannFactor.lean        # boltzmannFactorPD (full Boltzmann factor is PD)
│   │           ├── ReflectionPositivity.lean   # transferMatrixPositivity_axiom, osG_thetaG_factorization
│   │           ├── TransferMatrix.lean         # transferMatrixCorrect, integral_G_thetaG_eq_inner_g_Tg
│   │           └── MassGapProof.lean
├── proofs/                             # attempts.jsonl — raw AI proof-attempt log, not part of build
├── verify/                             # verification scripts (lean.bat, coq.bat, z3.bat, …)
├── docs/
├── literature/
├── lakefile.lean
├── lean-toolchain
└── README.md
```

## Building

```bash
curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh
cd YangMills
lake build
```

To check what a given theorem actually depends on:

```
#print axioms YourTheoremName
```

Run this on every top-level theorem before describing it as proved.

## Key design decisions

- Euclidean formulation via Osterwalder–Schrader axioms rather than
  Minkowski Wightman axioms directly, to use reflection positivity and
  stochastic methods.
- Lattice discretization as a bridge between finite approximations and
  continuum QFT (Wilson's lattice gauge theory).
- Four-corner plaquette classification for the Wilson action decomposition,
  to make the reflection symmetry identities hold.
- `SU(N)` for general N ≥ 2 via Mathlib's `Matrix.specialUnitaryGroup`.

## Keeping this README (and `Overview.lean`) honest

Documentation drift in this project is not a one-time bug, it's a recurring
pattern, and it goes in **both directions**: this README has previously
reported sorries as open that had been closed, and reported lemmas as
complete without noting the axioms they secretly depended on;
`Overview.lean` previously reported a fully-proved
lemma (`integral_G_thetaG_eq_inner_g_Tg`) as unformalized and referenced a
`sorry`'d lemma by a name that doesn't match anything in the actual
codebase (both now fixed). Treat both documents as equally prone to drift
and equally in need of upkeep:

- Every session that changes proof state must update the "What is actually
  proved" / "Known incomplete" sections of this README **and** the
  corresponding status notes in `Overview.lean`, in the same session, not
  later.
- Never describe a theorem as proved without having run
  `#print axioms` on it in that session.
- Never describe the top-level Millennium Prize theorem as proved, nearly
  proved, or as making progress, while `mass_gap_axiom` (or anything
  equivalent to the conjecture) remains in its dependency tree.
- When a module docstring (e.g. `MassGapProof.lean`'s "the proof uses four
  axioms") states a count or fact about the codebase, verify that count
  against the actual source in the same session — the axiom count there is
  currently wrong (says four, lists five; the actual count is now six with
  the addition of `characterOrthogonality`).
- If a claim in this README or `Overview.lean` can't be verified against
  current source in under a few minutes, mark it `[UNVERIFIED — recheck]`
  rather than leaving a confident-sounding but possibly stale statement in
  place.

## Mathlib candidate packaging

Three general-purpose results (Mercer-type positive-definite kernels and two
group-theoretic PD lemmas) have been extracted into standalone,
Yang-Mills-free files for independent review by Mathlib maintainers. They
are pure group/measure/kernel theory, verified by `#print axioms` to depend
only on `propext`, `Classical.choice`, `Quot.sound` (0 `sorry`, 0 custom
axiom). See **`MATHLIB_SUBMISSION.md`** at the repo root for the full
summary, absence-verification report, and reproduction steps. The standalone
files are:

- `PositiveDefiniteKernelMathlibCandidate.lean` (repo root) — **priority
  candidate**: Mercer-type PD kernels (no group structure), including
  `PositiveDefiniteKernel.integralOperator_nonneg` and the full building-block
  suite (`.conj_symm`, `.one`, `.mul`, `.smul_nonneg`, `.finprod`, `.comp`,
  `.continuous_comp`, `.sum_nonneg_of_map`, `toPositiveDefiniteKernel`).
- `PositiveDefiniteMathlibCandidate.lean` (repo root) — group-theoretic PD
  functions: `PositiveDefinite.integral` and
  `PositiveDefinite.integralOperator_nonneg`.

A search of external repositories found `Vilin97/lean-pool` contains
`IsPositiveDefinite` (same group-PD concept, different API), which is noted
for reviewer awareness in `MATHLIB_SUBMISSION.md`. The Mercer-type
`PositiveDefiniteKernel` has no known duplicate anywhere checked.

These results are unrelated to the (unsolved) Yang-Mills mass-gap difficulty
and are offered as standalone infrastructure.

## References

See `literature/survey.md` and `docs/strategy.md`.

## License

Academic use. No warranty.
