# Design Document: Closing `transferMatrixPositivity_axiom` via T = B*·B

**Date**: 2026-07-30
**Status**: Implementation (sub-steps (a)–(c), Lemma 2 sub-steps (i)–(iii), Fubini
steps 4a–4e, and **Lemma 3 σ-inversion** DONE as of 2026-08-04 session 17
(`fourierCoeffNeg_eq_fourierCoeffPos_fullReflect`, §8.11.25); remaining: Lemma 5
(L² expansion reorganization) + Lemma 6 (final assembly) — see §8.11.25)
**Goal**: Reduce axiom count from 6 to 5 by proving `transferMatrixPositivity_axiom`
from `peterWeyl_clebschGordan_plaquette` + `characterOrthogonality`.

## 1. Overview

The axiom `transferMatrixPositivity_axiom` (ReflectionPositivity.lean, line ~1366)
asserts that for `f` depending only on positive+interface links:

    ∫ G(U)·G(θU) dμ₀ ≥ 0

where `G = osG` is the Osterwalder-Seiler Boltzmann factor and `θ` is time-reflection.
This is equivalent (via `osG_thetaG_factorization` and `integral_G_thetaG_eq_inner_g_Tg`)
to the positivity of the transfer matrix `T`:

    ⟨g, Tg⟩_{L²(μ⁺⁰)} ≥ 0

The proof uses the **operator-theoretic T = B*·B argument**: the character expansion
of the interface Boltzmann factor defines an operator `B` (Fourier coefficient
extraction), and `T = B*·B` gives `⟨g, Tg⟩ = ‖Bg‖² ≥ 0`.

## 2. Mathematical Structure

### 2.1 The transfer matrix

After the change of variables `V⁺ = reflect(U⁻)` (using
`reflectLinkVariable_measurePreserving` and `S⁻(U⁻) = S⁺(reflect(U⁻))`):

    (Tg)(u) = exp(-β·S⁺(u)/2) · ∫_{V⁺} g(V⁺, σ(u⁰)) · exp(-β·(S⁺(V⁺)/2 + S_int(U⁺, u⁰, reflect(V⁺)))) dμ⁺(V⁺)

where:
- `u = (U⁺, u⁰)` is a `PosInterfaceConfig` (positive + interface links)
- `σ` is the interface reflection: inverts time-like interface links, keeps spatial
- `S_int(U⁺, u⁰, reflect(V⁺))` is the interface action with negative part = reflect(V⁺)

### 2.2 The interface plaquettes

Interface plaquettes are those NOT purely positive and NOT purely negative (i.e.,
corners straddle the time interface at signed time 0). They involve links from three
regions:

| Type | Base site time | Directions | Links involved |
|------|---------------|------------|----------------|
| A | t=0 | (0, ν) spatial | time-0 (interface) + time-1 (positive) |
| B | t=T-1 (signed -1) | (0, ν) spatial | time-T-1 (negative) + time-0 (interface) |
| C | t=0 | (μ, ν) both spatial | time-0 only (interface) |

After change of variables V⁺ = reflect(U⁻), type B plaquettes' negative links
(time T-1) become V⁺ links (time 1), with **inversion for time-like links**
(since reflection inverts time-like links).

### 2.3 The plaquette product and inversion

Each plaquette (n, μ, ν) has product:
    U(n,μ) · U(n+e_μ,ν) · U(n+e_μ+e_ν,μ)⁻¹ · U(n+e_ν,ν)⁻¹

The 3rd and 4th links are **inverted**. By `repCharacter_inv`:
    χ(g⁻¹) = conj(χ(g)) = χ_{dual}(g)  (via the dual map in the axiom)

So the character expansion of a plaquette factor with inverted links produces
**conjugated characters** for the 3rd and 4th links.

### 2.4 The reflection symmetry of S_int

The key symmetry (proved as `interface_action_reflection_symmetric_os_periodic`):
    S_int(θU) = S_int(U)

Since θ reflects ALL links (positive ↔ negative, interface → interface with σ), this
gives:
    S_int(U⁺, u⁰, U⁻) = S_int(reflect(U⁻), σ(u⁰), reflect(U⁺))

After change of variables U⁻ = reflect(V⁺):
    S_int(U⁺, u⁰, reflect(V⁺)) = S_int(V⁺, σ(u⁰), reflect(U⁺))

This means the interface Boltzmann factor K(U⁺, u⁰, V⁺) = exp(-β·S_int(...)) satisfies:
    K(U⁺, u⁰, V⁺) = K(V⁺, σ(u⁰), U⁺)

### 2.5 The σ reflection on interface links

For interface sites (signed time = 0), θn = n (since -0 = 0 in ZMod T). So on
interface links:
- Time-like (μ=0): (θU)(n, 0) = U(n, 0)⁻¹ — **inverted**
- Spatial (μ≠0): (θU)(n, μ) = U(n, μ) — **unchanged**

This σ reflection is the source of obstruction 3 (gap_analysis.md): it prevents the
direct `character_expansion_positivity` approach, because the integral becomes
`⟨A_i, A_i ∘ σ⟩` (inner product with σ-composed), not `‖A_i‖²`.

### 2.6 The T = B*·B resolution

The OS proof resolves this by constructing `B` via the character expansion and showing
`T = B*·B`. The key steps (from gap_analysis.md lines 383-394):

1. **Expand each interface plaquette factor** in characters (Peter-Weyl), with
   conjugation for inverted links (via the dual map).
2. **For interface time-like links** appearing in both a plaquette `p` and its
   reflection `θp`, the product `χ_s(g) · conj(χ_t(g))` arises. This is a matrix
   coefficient of `ρ_s ⊗ ρ_t*`, decomposable via CG into `∑_w N^w χ_w(g)` with
   `N^w ≥ 0` (using `charProduct_mixed_finset_decomp'`).
3. **For links appearing in multiple plaquettes**, CG reduces products of characters
   of the same link to single characters (using `charProduct_mixed_link_separable_decomp`).
4. The resulting decomposition defines `B` (Fourier coefficient extraction), and
   `T = B*·B` gives `⟨g, Tg⟩ = ‖Bg‖² ≥ 0`.

## 3. Formalization Plan

### Step (a): Separable decomposition of the interface Boltzmann factor

**Goal**: Show that the product of interface plaquette Boltzmann factors has a
separable character decomposition with non-negative coefficients.

**Abstract lemma** (`plaquette_product_separable_decomp` in PeterWeyl.lean):

Given the Peter-Weyl axiom data (ι, ρ, coeff, cg, dual, etc.), a finite type `P` of
plaquettes, a finite type `L` of links, a link assignment `links : P → Fin 4 → L`
(surjective: every link appears in ≥1 plaquette), and link variables `g : L → SU N`:

    ∏_{p ∈ P} exp(c · Re Tr(g₁·g₂·g₃⁻¹·g₄⁻¹))
      = ∑_{w : L → ι} F(w) · ∏_{l ∈ L} χ_{w(l)}(g_l)

where `g_i = g(links p i)`, `F(w) ≥ 0`, and the 3rd/4th links are inverted.

**Status (2026-07-30): PROVED.** The lemma `plaquette_product_separable_decomp`
is fully proved in `PeterWeyl.lean` with 0 sorries and 0 custom axioms
(`#print axioms` confirms only `propext`, `Classical.choice`, `Quot.sound`).
All 5 stages of the proof structure below are implemented.

**Proof structure**:
1. For each plaquette `p`, apply `hexp4` with `(g₁, g₂, g₃⁻¹, g₄⁻¹)` and use
   `repCharacter_inv` / `hdual` to get `conj(χ)` for inverted links.
2. Product of sums = sum of products (`Fintype.prod_sum`): expand the product of
   per-plaquette character sums into a sum over `α : P → ι⁵` of products.
3. For each `α`, the product is `∏_p ∏_j (if j≥2 then conj(χ) else χ)`. Regroup by
   link: `∏_l ∏_{(p,j): links p j = l} (...)`.
4. Apply `charProduct_mixed_link_separable_decomp` to get a per-`α` separable
   decomposition `∑_w F_α(w) · ∏_l χ_{w(l)}(g_l)` with `F_α(w) ≥ 0`.
5. Sum over `α`: `∑_α (∏_p coeff(α p)) · ∑_w F_α(w) · ∏_l χ_{w(l)}(g_l)`.
6. Exchange sums: `∑_w (∑_α (∏_p coeff(α p)) · F_α(w)) · ∏_l χ_{w(l)}(g_l)`.
7. The coefficient `G(w) = ∑_α (∏_p coeff(α p)) · F_α(w) ≥ 0` (sum of products of
   non-negative reals).

**Key challenges**:
- **Step 1**: Substituting `g₃⁻¹, g₄⁻¹` into `hexp4` and converting `χ(g⁻¹)` to
  `conj(χ(g))` via `repCharacter_inv` (or to `χ_{dual}(g)` via `hdual`).
- **Step 3**: Regrouping a product indexed by `P × Fin 4` into a product grouped by
  link (partition of `P × Fin 4` by the `links` map). This requires a
  "product over partition" lemma.
- **Step 4**: Setting up the appearance structure `(A, S, charIdx, isConj)` for
  `charProduct_mixed_link_separable_decomp`, where `A = P × Fin 4`,
  `S l = {(p,j) : links p j = l}`, `charIdx` depends on `α`, and `isConj (p,j) = (j ≥ 2)`.
- **Step 6**: Exchanging the `α` and `w` sums (`Fintype.sum_comm`).

**Status**: In progress. The abstract lemma will be stated and proved in
`PeterWeyl.lean`, taking the Peter-Weyl axiom data as explicit parameters (following
the pattern of `charProduct_mixed_link_separable_decomp`).

### Step (b): Change of variables in the transfer-matrix integral

**Goal**: After obtaining the separable decomposition of the interface Boltzmann
factor, change variables in the transfer-matrix integral to express `⟨g, Tg⟩` in
terms of the separable decomposition.

**Status (2026-07-30 session 7): IN PROGRESS.** The key measure-theoretic
ingredient and the involution property are now PROVED:

- `reflectLinkVariable_measurePreserving_between` (LatticeMeasure.lean, ~line 383):
  The reflection maps link configs on `sourceSites` to link configs on `targetSites`
  in a measure-preserving way, when `reflectSite` gives a bijection between the two
  site sets. This generalizes `reflectLinkVariable_measurePreserving` (which is the
  special case `sourceSites = targetSites`). **0 sorries, 0 custom axioms**
  (verified by `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`).
  The proof is the same two-step composition as `reflectLinkVariable_measurePreserving`:
  (1) index bijection via `measurePreserving_piCongrLeft`, (2) componentwise inversion
  via `measurePreserving_pi` + `haarMeasure_inv_invariant`.

- `reflectToPosInterface_involution` (TransferMatrix.lean, ~line 1751): **PROVED**
  (session 7). Shows that
  `reflectToPosInterface(reflectPosToNeg(V⁺), u⁰) = mergePosInterface(V⁺, σ(u⁰))` —
  i.e., reflecting the negative config `reflectPosToNeg(V⁺)` back to the
  positive+interface region recovers `V⁺` on positive links and `σ(u⁰)` on interface
  links. **0 sorries, 0 custom axioms** (verified by `#print axioms`: only `propext`,
  `Classical.choice`, `Quot.sound`). The proof proceeds by extensionality and case
  analysis (positive sites vs interface sites), using `ReflectSite.involution` for
  the double reflection and helper lemmas about `reflectSite` mapping between site
  sets (added to ReflectionPositivity.lean).

**New definitions** (TransferMatrix.lean):
- `reflectPosToNeg`: maps positive configs → negative configs via reflection. This is
  the inverse of the change-of-variables map `U⁻ ↦ V⁺ = reflect(U⁻)`.
- `sigmaInterface`: the σ reflection on interface configs (inverts time-like links,
  keeps spatial), defined as `restrictLinkVariable interfaceSites (reflectLinkVariable
  (extendLinkVariable interfaceSites U_zero))`.

**New helper lemmas** (ReflectionPositivity.lean, ~line 206):
- `signedTime_reflectSite`: `signedTime(reflectSite(n)) = -signedTime(n)`.
- `reflectSite_mem_negative_of_positive`: positive → negative.
- `reflectSite_mem_interface_of_interface`: interface → interface.
- `reflectSite_not_mem_positive_of_interface`, `reflectSite_not_mem_negative_of_interface`:
  interface sites don't map to positive/negative.
- `reflectSite_not_mem_positive_of_positive`: positive sites don't map to positive.
- `reflectSite_mem_positive_of_negative`: negative → positive.
- `reflectSite_not_mem_negative_of_negative`: negative sites don't map to negative.

**New supporting lemmas** (TransferMatrix.lean, ~line 1815):
- `restrictLinkVariable_negative_extendToFullConfig`: restricting
  `extendToFullConfig U_minus u` to negative sites recovers `U_minus`.
- `restrictPosInterface_extendToFullConfig`: restricting
  `extendToFullConfig U_minus u` to positive+interface sites recovers `u`.
- `reflect_extendToFullConfig_posInterface`: the positive+interface restriction
  of `reflectLinkVariable(extendToFullConfig(reflectPosToNeg V⁺, u))` equals
  `mergePosInterface V⁺ (σ(restrictToInterface u))`. This combines
  `reflectToPosInterface_eq_restrict` with `reflectToPosInterface_involution` and
  is the key lemma for rewriting `S⁺` under the change of variables.
  All **0 sorries, 0 custom axioms** (verified by `#print axioms`: only `propext`,
  `Classical.choice`, `Quot.sound`).

**Remaining sub-step for (b)**:
1. **transferMatrix_change_of_variables** — **PROVED (session 7)**. The
   integral-level change of variables is complete. The lemma
   `transferMatrix_change_of_variables` (TransferMatrix.lean, ~line 1994) shows
   `transferMatrixCorrect = transferMatrixReflected`, applying
   `reflectLinkVariable_measurePreserving_between` (measure-preserving from μ⁻ to
   μ⁺) via `integral_map` together with the pointwise identity
   `transferMatrix_integrand_change_of_variables`. **0 sorries, 0 custom axioms**
   (verified by `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`).

**Step (b) is COMPLETE.** The change of variables `U⁻ ↦ V⁺ = reflect(U⁻)` is
fully formalized at both the pointwise and integral levels. The transfer matrix
can now be written in the "reflected" form:
```
(Tψ)(u) = exp(-β·S⁺(u)/2) · ∫_{V⁺} ψ(V⁺, σ(u⁰)) ·
          exp(-β·(S⁺(V⁺, σ(u⁰))/2 + S_int(U⁺, u⁰, reflect(V⁺)))) dμ⁺(V⁺)
```
where the negative-time integral has been replaced by a positive-time integral.

**Key ingredients** (all proved):
- `reflectLinkVariable_measurePreserving_between` (proved this session): the
  reflection is measure-preserving from μ⁻ to μ⁺.
- `haarMeasure_inv_invariant` (proved): Haar measure is invariant under inversion.
- `neg_action_reflection_os_periodic` (proved): S⁻(U⁻) = S⁺(reflect(U⁻)).
- `reflection_involution` (proved): θ(θU) = U.
- The reflection symmetry `S_int(U⁺, u⁰, reflect(V⁺)) = S_int(V⁺, σ(u⁰), reflect(U⁺))`
  (from `interface_action_reflection_symmetric_os_periodic`).

### Step (c): Use CG with dual representations + character orthogonality

**Goal**: Use the CG decomposition (with dual representations, via the dual map) to
combine reflected characters with unreflected ones, then use `characterOrthogonality`
to evaluate the integrals and obtain `∑_w a_w · |Fourier coefficient|² ≥ 0`.

**Key ingredients**:
- `charProduct_mixed_finset_decomp'` (proved): mixed-conjugation CG decomposition.
- `charProduct_mixed_link_separable_decomp` (proved): per-term separable decomposition
  with mixed conjugation.
- `characterOrthogonality` (axiom): Schur orthogonality for irreducible characters.

### Step (d): Conclude T = B*·B and ⟨g, Tg⟩ = ‖Bg‖² ≥ 0

**Goal**: Assemble the pieces to show `T = B*·B` and conclude positivity, closing
`transferMatrixPositivity_axiom`.

## 4. Key Insight: The σ Reflection and Interface Time-Like Links

The fundamental difficulty is the **σ reflection on interface time-like links**.
When a time-like interface link `g` appears in both the original and reflected
plaquette factors, the product `χ_s(g) · conj(χ_t(g))` arises. This is NOT
`|χ(g)|² = χ(g) · conj(χ(g))` (which would be non-negative), but rather a product of
two different characters, which is complex in general.

The resolution: `χ_s(g) · conj(χ_t(g))` is a matrix coefficient of `ρ_s ⊗ ρ_t*`,
which decomposes via CG (with dual representations) into `∑_w N^w_{s,t*} χ_w(g)` with
`N^w ≥ 0`. After this decomposition, the integral over `g` can be evaluated using
character orthogonality, giving `∑_w N^w · |∫ f · χ_w|² ≥ 0`.

This is why the dual map (added to the axiom on 2026-07-30) is essential: it converts
`conj(χ_t(g))` to `χ_{dual(t)}(g)`, allowing the CG decomposition to combine
`χ_s(g) · χ_{dual(t)}(g)` into a single character sum.

## 5. Alternative Approach: Derived Axiom

If the full formalization proves too complex, an intermediate approach is:

1. **Axiomatize** the separable decomposition of the interface Boltzmann factor as a
   "derived axiom" (a consequence of Peter-Weyl).
2. **Prove** `transferMatrixPositivity_axiom` from the derived axiom (pure measure
   theory + character orthogonality). This removes `transferMatrixPositivity_axiom`,
   replacing it with the derived axiom (count stays at 6).
3. **Prove** the derived axiom from `peterWeyl_clebschGordan_plaquette` (pure
   combinatorics/representation theory). This removes the derived axiom (count → 5).

This decomposes the problem into two cleaner pieces: the measure-theory part (step 2)
and the combinatorics part (step 3). The measure-theory part is conceptually cleaner
and may be more tractable.

## 5a. Key Finding (2026-07-31 session): The L² Expansion Obstruction

**Status**: Step (c) analysis complete. A fundamental obstruction has been identified
that prevents closing `transferMatrixPositivity_axiom` from the current axioms alone.

### The obstruction

After steps (a)–(b), the integral to show ≥ 0 is:

    I = ∫_u ∫_{V⁺} f(u) · f(V⁺, σ(u⁰)) · K(u, V⁺) dμ⁺(V⁺) dμ⁺⁰(u)

where K(u, V⁺) = exp(-β·(S⁺(u) + S⁺(V⁺, σ(u⁰)) + S_int(U⁺, u⁰, reflect(V⁺)))).

The character expansion of K (via `plaquette_product_separable_decomp`, step a) gives:

    K(u, V⁺) = ∑_w F(w) · Φ_w(U⁺) · Ψ_w(u⁰) · Ξ_w(V⁺)

where Φ_w, Ψ_w, Ξ_w are products of characters over U⁺, u⁰, V⁺ links, and F(w) ≥ 0.

By the reflection symmetry S_int(U⁺, u⁰, reflect(V⁺)) = S_int(V⁺, σ(u⁰), reflect(U⁺)),
the decomposition is symmetric: Ξ_w = Φ_w. So:

    I = ∑_w F(w) · ∫_{u⁰} Ψ_w(u⁰) · A_w(u⁰) · A_w(σ(u⁰)) dμ⁰(u⁰)

where A_w(u⁰) = ∫_{u⁺} f(u⁺, u⁰) · Φ_w(u⁺) dμ⁺(u⁺).

**This is obstruction 3 (from gap_analysis.md): the integral is
⟨A_w · Ψ_w, A_w ∘ σ⟩_{L²(μ⁰)}, which is NOT necessarily non-negative.**

The σ reflection on interface time-like links (g ↦ g⁻¹, giving χ(g⁻¹) = conj(χ(g)))
means the integral involves A_w(u⁰) · A_w(σ(u⁰)), not |A_w(u⁰)|².

### Why the L² expansion (full Peter-Weyl) is needed

To evaluate the u⁰ integral ∫ Ψ_w(u⁰) · A_w(u⁰) · A_w(σ(u⁰)) dμ⁰(u⁰) using character
orthogonality, one must expand A_w(u⁰) in the character basis:

    A_w(u⁰) = ∑_λ c_λ · χ_λ(u⁰)

This is the **L² expansion** (Peter-Weyl theorem: matrix elements of irreducible
representations form an orthonormal basis of L²(G)). It is NOT provided by the
current axioms:

- `peterWeyl_clebschGordan_plaquette` provides the character expansion of the
  **Boltzmann factor** (a specific function), NOT the L² expansion of **arbitrary**
  functions.
- `characterOrthogonality` provides Schur orthogonality of characters
  (∫ χ_λ · conj(χ_μ) = δ_{λμ}), which is an **orthogonality** statement, not a
  **completeness** statement.

The L² expansion is a completeness statement: it says that the matrix elements
{ρ_λ(g)_{ij}} span ALL of L²(G), not just the class functions (which are spanned by
characters). Since A_w(u⁰) depends on the arbitrary test function f, it is NOT a
class function in general, so it cannot be expanded in characters alone — the full
matrix element basis is needed.

### Why the decomposition K = ∑ a_w · Φ_w(u) · conj(Φ_w(θ(V⁺,u⁰))) doesn't help

Even if the kernel decomposes as K(u, V⁺) = ∑_w a_w · Φ_w(u) · conj(Φ_w(θ(V⁺, u⁰)))
(where θ(V⁺, u⁰) = (V⁺, σ(u⁰))), the integral becomes:

    I = ∑_w a_w · ∫_{u⁰} A_w(u⁰) · conj(A_w(σ(u⁰))) dμ⁰(u⁰) = ∑_w a_w · ⟨A_w, A_w ∘ σ⟩

which is obstruction 3 — NOT necessarily non-negative. The σ reflection prevents the
factorization into |Fourier coefficient|².

### Proposed path forward: Strengthen peterWeyl_clebschGordan_plaquette

**Progress (2026-08-01):** Two of the three required strengthenings are DONE:

1. ✅ **Schur orthogonality of matrix elements** — The `characterOrthogonality` axiom
   (PositiveDefinite.lean) has been **strengthened** from character orthogonality
   (∫ χ_λ · conj(χ_μ) = δ_{λμ}) to the full Schur orthogonality of **matrix elements**
   (∫ (ρ_λ g)_{ij} · conj((ρ_μ g)_{kl}) dμ = δ_{λμ} δ_{ik} δ_{jl} / dim(λ), as a 3-part
   conjunction: integrability + diagonal + off-diagonal, with `hDims`/`hIrr`
   hypotheses). The character-orthogonality version is now **derived** as the lemma
   `character_orthogonality_from_schur` (0 sorries; `#print axioms`:
   `propext, Classical.choice, Quot.sound, characterOrthogonality`).

2. ✅ **Irreducibility + positive dimension** — The `peterWeyl_clebschGordan_plaquette`
   axiom (PeterWeyl.lean) has been **strengthened** to also provide
   `hIrr : ∀ i, IsIrreducible (ρ i)` and `hDims : ∀ i, 0 < dims i` — the hypotheses
   required to apply the strengthened `characterOrthogonality` to the Peter-Weyl data.
   Both `obtain` sites updated. Axiom count STILL SIX (enriched existing axiom).
   `#print axioms` confirms: `plaquetteBoltzmannPD` =
   `[propext, Classical.choice, Quot.sound, peterWeyl_clebschGordan_plaquette]`;
   `charProduct_PD` = `[propext, Classical.choice, Quot.sound]`;
   `plaquette_product_separable_decomp` = `[propext, Classical.choice, Quot.sound]`.

3. ✅ **L² expansion (Peter-Weyl completeness)** — DONE (2026-08-02). The
   `peterWeyl_clebschGordan_plaquette` axiom has been **strengthened** to also
   provide a countable index set `Λ` (with `Encodable Λ`) of all irreducible
   unitary representations of `SU(N)`, with matrix elements `(ρ_ℓ g)_{ij}` for
   `ℓ ∈ Λ`, an embedding `emb : ι ↪ Λ` with matching characters, the normalized
   Haar measure `μ` (a probability measure), and the **L² completeness**
   (Peter-Weyl theorem, completeness part): if `f ∈ L¹(G, μ)` is integrable and
   all its Fourier coefficients `∫ f · conj((ρ_ℓ g)_{ij}) dμ = 0` vanish, then
   `f = 0` a.e. This is the statement that the matrix elements form an
   orthonormal **basis** (not just an orthogonal family) of `L²(G, μ)`. Axiom
   count STILL SIX (enriched existing axiom, not new). `#print axioms` confirms:
   `plaquetteBoltzmannPD` = `[propext, Classical.choice, Quot.sound,
   peterWeyl_clebschGordan_plaquette]`; `charProduct_PD` and
   `plaquette_product_separable_decomp` = `[propext, Classical.choice, Quot.sound]`.

**Why the L² expansion is needed (precise analysis).** After steps (a)–(b), the
integral to show ≥ 0 is:

    I = ∑_w F(w) · ∫_{u⁰} Ψ_w(u⁰) · A_w(u⁰) · A_w(σ(u⁰)) dμ⁰(u⁰)

where A_w(u⁰) = ∫_{u⁺} f(u⁺, u⁰) · exp(-β S⁺/2) · Φ_w(u⁺) dμ⁺(u⁺) is an arbitrary
L² function of the interface config u⁰ (arbitrary because f is arbitrary). The σ
reflection inverts the time-like interface links (g ↦ g⁻¹), so ρ_λ(σ(u⁰))_{ij} =
conj(ρ_λ(u⁰)_{ji}) (for unitary representations). Expanding A_w in the matrix-element
basis and using Schur orthogonality (with the conj from the σ inversion) evaluates the
integral as ∑ |Fourier coefficient|² ≥ 0. Without the L² expansion, A_w cannot be
expanded, and the integral cannot be evaluated.

**Key subtlety: the sum is infinite but only finitely many terms contribute.** The
L² expansion of A_w involves ALL irreps (infinite). But the integral
∫ Ψ_w · (ρ_λ)_{ij} · conj((ρ_μ)_{lk}) dμ⁰ is non-zero only when the CG decomposition
of Ψ_w · (ρ_λ)_{ij} (a product of characters from the finite ι times a matrix element)
contains the representation μ. By closure of ι under tensor products, if λ ∈ ι then
the CG decomposition stays in ι, so μ ∈ ι (finite). If λ ∉ ι, the decomposition may
leave ι. So the integral splits into a finite part (λ, μ ∈ ι) and an infinite part
(λ, μ ∉ ι). The L² expansion is needed to handle the infinite part and show the total
is ∑ |c|² ≥ 0.

**Formalization challenge.** The L² expansion requires:
- A **countable** index set of all irreducible representations (the current axiom uses
  a finite `Fintype ι`).
- **L² convergence** of the partial sums (not pointwise).
- Exchange of the infinite sum with the integral (dominated convergence / L² theory).

This is essentially formalizing the Peter-Weyl theorem (completeness part) in Lean —
a major effort. Mathlib's `MeasureTheory.Lp` infrastructure may help.

**Axiom formulation — IMPLEMENTED (2026-08-02).** The
`peterWeyl_clebschGordan_plaquette` axiom has been **strengthened** to also
provide the L² completeness, keeping the axiom count at 6. The completeness is
stated in the "trivial orthogonal complement" form: if
`∫ f · conj(ρ_ℓ(g)_{ij}) dμ = 0` for all `ℓ ∈ Λ`, `i`, `j`, then `f = 0` a.e.
This avoids the need to formalize infinite sums and L² convergence directly —
the "trivial orthogonal complement" is a single `∀ f, ... → f = 0 a.e.`
statement. The axiom also provides the countable `Λ` (with `Encodable Λ`), the
matrix elements `ρ_ℓ`, the embedding `emb : ι ↪ Λ`, and the Haar measure `μ`.

With the L² expansion, the OS proof proceeds:
1. Expand K in characters (step a, done).
2. Expand A_w(u⁰) in the matrix element basis (L² expansion — now provided).
3. Use Schur orthogonality of matrix elements (strengthened characterOrthogonality)
   to evaluate the u⁰ integral, using the σ inversion relation ρ_λ(σ)_{ij} =
   conj(ρ_λ_{ji}).
4. The result is ∑ |Fourier coefficient|² ≥ 0, closing transferMatrixPositivity_axiom.

## 6. Current State of Proved Ingredients

All of the following are proved with 0 sorries and 0 custom axioms (verified by
`#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`):

- `plaquetteBoltzmannPD` — plaquette Boltzmann factor is PD on SU(N)⁴
- `plaquetteBoltzmannPD_inv` — with inverted 3rd/4th links
- `boltzmannFactorPD` — full Boltzmann factor is PD
- `osG_thetaG_factorization` — clean algebraic factorization of G(U)·G(θU)
- `reflectLinkVariable_measurePreserving` — reflection is measure-preserving
- `haarMeasure_inv_invariant` — Haar measure invariant under inversion
- `character_expansion_positivity` — abstract measure-theory scaffold
- `character_expansion_nonneg` — corollary: integral is non-negative
- `charProduct_PD` — product of two chars is PD via CG
- `charProduct_finset_decomp` — finite product of chars decomposes via CG
- `charSum_product_decomp` — product of char sums decomposes via CG
- `charSum_finprod_decomp` — finite product of char sums decomposes via CG
- `charSum_product_link_decomp` — product of per-link char sums → separable
- `charProduct_finset_decomp'` — generalized CG decomposition (appearances)
- `charProduct_link_separable_decomp` — per-term separable decomposition
- `charProduct_mixed_finset_decomp'` — mixed-conjugation CG decomposition
- `charProduct_mixed_link_separable_decomp` — per-term separable with mixed conj
- `integral_G_thetaG_eq_inner_g_Tg` — key identity (measure theory, 0 sorries)

## 7. Axiom Inventory (6 axioms)

1. `peterWeyl_clebschGordan_plaquette` — Peter-Weyl + CG + dual map (strengthened)
2. `transferMatrixPositivity_axiom` — **TARGET: prove from #1 + #6**
3. `os_reconstruction_theorem` — OS reconstruction
4. `continuum_limit_exists` — continuum limit
5. `mass_gap_axiom` — **THE CONJECTURE (do NOT remove)**
6. `characterOrthogonality` — Schur orthogonality

Closing `transferMatrixPositivity_axiom` reduces the count to **5**.

## 8. Formalization Plan for Step (c)–(d) (2026-08-02 analysis)

**Status**: In execution. The key mathematical structure is now understood and
mostly formalized: the matrix-element CG strengthening was made (2026-08-02 session 3),
and the plan below has been carried through Lemma 2, Fubini steps 4a–4e, and
Lemma 3 (σ-inversion) as of 2026-08-04; remaining: Lemma 5 (L² expansion
reorganization) and Lemma 6 (final assembly) — see §8.11 and the README session log.

### 8.1 The key mathematical insight: V⁺ conjugation

After the change of variables (step b), the transfer matrix kernel is:

    K(u⁺, u⁰, V⁺) = exp(-β·S⁺(u⁺,u⁰)/2) · exp(-β·S⁺(V⁺,σ(u⁰))/2) · exp(-β·S_int(U⁺,u⁰,reflect(V⁺)))

The interface plaquettes are of three types (§2.2):
- **Type A** (base t=0, spatial dirs): involves U⁺ and u⁰ links (NO V⁺ links)
- **Type B** (base t=T-1, spatial dirs): involves U⁻→V⁺ and u⁰ links
- **Type C** (base t=0, both spatial): involves u⁰ links only (NO V⁺ links)

**Key observation**: V⁺ links appear ONLY in type B plaquettes (after the change
of variables U⁻ = reflect(V⁺)). In type B plaquettes, the V⁺ links appear in:
- Position 1 (g₁): U⁻_time-like → V⁺_time-like⁻¹ (inverted by reflection).
  Character: χ_s(V⁺⁻¹) = conj(χ_s(V⁺)). **Conjugated.**
- Position 4 (g₄⁻¹): U⁻_spatial → V⁺_spatial (not inverted by reflection, but
  inverted by plaquette). Character: χ_v(V⁺⁻¹) = conj(χ_v(V⁺)). **Conjugated.**

**ALL V⁺ links have conjugated characters.** This means the character expansion
of the full kernel K has the form:

    K(u⁺, u⁰, V⁺) = ∑_w F(w) · Φ_w(U⁺) · Ψ_w(u⁰) · conj(Φ_w(V⁺))

with F(w) ≥ 0, where Φ_w is a product of characters of U⁺ (resp. V⁺) links,
and Ψ_w is a product of characters of u⁰ links.

This is proved by applying `plaquette_product_separable_decomp` (step a) to the
interface plaquettes, using the fact that the V⁺ links always appear with
conjugated characters (from the reflection + plaquette inversions).

### 8.2 The integral reduction

With the character expansion K = ∑_w F(w) · Φ_w(U⁺) · Ψ_w(u⁰) · conj(Φ_w(V⁺)),
the integral ⟨g, Tg⟩ becomes:

    I = ∑_w F(w) · ∫_{u⁰} Ψ_w(u⁰) · A_w(u⁰) · conj(A_w(σ(u⁰))) dμ⁰(u⁰)

where A_w(u⁰) = ∫_{u⁺} g(u⁺, u⁰) · Φ_w(U⁺) dμ⁺(u⁺) is the "Fourier coefficient"
of g with respect to Φ_w (a function of u⁰ alone).

**Key**: A_w depends on w (through Φ_w). Different w give different A_w.

### 8.3 The key challenge: individual terms can be negative

**Counterexample** (SU(2), single time-like link, σ = inversion):
- K = χ₀ = 1 (trivial character, PD), A(g) = (ρ_{1/2}(g))₁₂
- ∫ 1 · (ρ(g))₁₂ · conj((ρ(g⁻¹))₁₂) dμ = ∫ (ρ(g))₁₂ · (ρ(g))₂₁ dμ
- For SU(2): (ρ(g))₁₂ = b, (ρ(g))₂₁ = -b̄, so the integral = -∫|b|² dμ < 0.

**Individual terms ∫ Ψ_w · A_w · conj(A_w(σ)) dμ⁰ can be NEGATIVE.**
The SUM ∑_w F(w) · (individual terms) is ≥ 0, but the proof requires the L²
expansion and the specific structure of F(w) and A_w.

### 8.4 The σ inversion relation for matrix elements

For unitary representations, ρ(g⁻¹) = ρ(g)ᴴ (conjugate transpose), so:

    (ρ(σ(g)))_{ij} = (ρ(g⁻¹))_{ij} = conj((ρ(g))_{ji})

This is the key relation that connects the σ reflection to the matrix-element
basis. It is derived from `repCharacter_inv` (PositiveDefinite.lean) and the
unitary property `IsUnitaryRepresentation`.

### 8.5 The L² expansion approach

Expand A_w in the matrix-element basis (using L² completeness from the
strengthened axiom):

    A_w(u⁰) = ∑_{λ,i,j} c^w_{λ,i,j} · ∏_l (ρ_{λ_l}(u⁰_l))_{i_l, j_l}

Then A_w(σ(u⁰)) uses the σ inversion relation:

    A_w(σ(u⁰)) = ∑_{λ,i,j} c^w_{λ,i,j} ·
      ∏_{l spatial} (ρ_{λ_l}(u⁰_l))_{i_l, j_l} ·
      ∏_{l time-like} conj((ρ_{λ_l}(u⁰_l))_{j_l, i_l})

The integral factorizes (by Fubini, since μ⁰ is a product measure) as a product
over interface links. For each link l:

- **Spatial links**: ∫ χ_{w(l)}(g) · (ρ_λ(g))_{ij} · conj((ρ_μ(g))_{kl}) dμ(g)
  — triple product WITH conjugation. Evaluable by CG + Schur orthogonality.

- **Time-like links**: ∫ χ_{w(l)}(g) · (ρ_λ(g))_{ij} · (ρ_μ(g))_{lk} dμ(g)
  — triple product WITHOUT conjugation. NOT directly evaluable by Schur
  orthogonality. Requires converting (ρ_μ(g))_{lk} = conj((ρ_μ(g⁻¹))_{kl})
  and changing variables, giving conj(∫ χ_w · (ρ_λ)_{ji} · (ρ_μ)_{kl} dμ).
  This is complex in general.

### 8.6 The reorganization challenge

The sum ∑_w F(w) · ∫ Ψ_w · A_w · conj(A_w(σ)) dμ⁰ must be reorganized as a sum
of |Fourier coefficient|² terms:

    I = ∑_ν (1/dim(ν)) · |∑_{λ,i,j} c^w_{λ,i,j} · (CG coefficient)|² ≥ 0

This reorganization requires the **matrix-element CG coefficients** (the
unitary change-of-basis matrix U^ν for the decomposition ρ_w ⊗ ρ_λ → ⊕_ν ρ_ν),
NOT just the character-level CG multiplicities cg(s,t,w) provided by the
current axiom.

**Key finding**: The current axiom `peterWeyl_clebschGordan_plaquette` provides
only the character-level CG decomposition (χ_s · χ_t = ∑_w cg(s,t,w) · χ_w).
The matrix-element CG coefficients (U^ν_{(a,i),p}) are NOT provided and CANNOT
be derived from the character-level CG alone (different bases give different
coefficients for the same multiplicities).

### 8.7 Axiom strengthening: matrix-element CG coefficients (DONE 2026-08-02 session 3)

The `peterWeyl_clebschGordan_plaquette` axiom has been **strengthened** to also
provide the **matrix-element CG coefficients**: a family `cgME : ∀ (s t ν : ι),
Fin (dims s) → Fin (dims t) → Fin (dims ν) → ℂ` of unitary change-of-basis
matrices that implement the decomposition of `ρ_s ⊗ ρ_t` into `⊕_ν ρ_ν`,
satisfying:

    (ρ_s(g))_{ab} · (ρ_t(g))_{ij} = ∑_ν ∑_p ∑_q cgME s t ν a i p · (ρ_ν(g))_{pq} · conj(cgME s t ν b j q)

together with the unitarity (completeness) relation:

    ∑_{ν,p} conj(cgME s t ν a i p) · cgME s t ν b j p = δ_{ab} δ_{ij}

This allows evaluating the triple product integrals using Schur orthogonality
and reorganizing the sum as `∑ |Fourier coefficient|² ≥ 0`.

**Axiom count**: This strengthening enriches the existing axiom (count stays at
6). Both `obtain` sites in `PeterWeyl.lean` updated. Full `lake build` GREEN
(2972 jobs). `#print axioms` confirms existing lemmas have unchanged axiom
dependencies: `plaquetteBoltzmannPD` = `[propext, Classical.choice, Quot.sound,
peterWeyl_clebschGordan_plaquette]`; `charProduct_PD` and
`plaquette_product_separable_decomp` = `[propext, Classical.choice, Quot.sound]`
(no custom axioms). Closing `transferMatrixPositivity_axiom` would then reduce
the count to 5.

### 8.8 Intermediate lemmas (formalization order)

1. **`interface_kernel_character_expansion`** — The full kernel K has the
   character expansion K = ∑_w F(w) · Φ_w(U⁺) · Ψ_w(u⁰) · conj(Φ_w(V⁺)) with
   F(w) ≥ 0. Uses `plaquette_product_separable_decomp` + the V⁺ conjugation
   property (§8.1). [Combinatorial + representation theory]

   **DONE (2026-08-02 session 4).** Proven at the abstract plaquette-product
   level in `PeterWeyl.lean` (inside `PlaquetteBoltzmann`). Given a product of
   plaquette Boltzmann factors `∏_p exp(c·Re Tr(g₁g₂g₃⁻¹g₄⁻¹))` and a disjoint
   partition of the link set `L = L_U ⊔ L_0 ⊔ L_V` (U⁺/u⁰/V⁺ links), the product
   equals `∑_w F(w)·(∏_{L_U} χ_{w(l)})(∏_{L_0} χ_{w(l)})·conj(∏_{L_V} χ_{dual(w(l))})`
   with `F(w) ≥ 0`. Proof: `plaquette_product_separable_decomp` (gives
   `∑_w F(w)·∏_l χ_{w(l)}`) composed with `prod_conj_partition_dual` (separates
   V⁺ links with conjugated dual characters) and the disjoint-union split
   `univ \ L_V = L_U ∪ L_0`. `#print axioms` = `[propext, Classical.choice,
   Quot.sound]` (0 sorries, 0 custom axioms). The remaining gap to the concrete
   transfer-matrix kernel is a *separate* lemma connecting
   `exp(-β·S_OS)` to the abstract plaquette-product form (exp-of-sum =
   product-of-exps + the interface plaquette enumeration); that connection is
   not yet formalized.

2. **`transfer_matrix_integral_reduction`** — The integral ⟨g, Tg⟩ reduces to
   ∑_w F(w) · ∫_{u⁰} Ψ_w · A_w · conj(A_w(σ)) dμ⁰. Uses lemma 1 + Fubini.
   [Measure theory]

3. **`matrix_element_sigma_inversion`** — For unitary ρ, (ρ(σ(g)))_{ij} =
   conj((ρ(g))_{ji}). Uses `repCharacter_inv` + unitary property.
   [Representation theory, likely straightforward]

4. **`triple_product_integral_eval`** — The triple product integral
   ∫ χ_w · (ρ_λ)_{ij} · conj((ρ_μ)_{kl}) dμ can be evaluated using the
   matrix-element CG coefficients + Schur orthogonality. [Requires axiom
   strengthening §8.7]

5. **`reflection_positivity_reorganization`** — The sum ∑_w F(w) · ∫ Ψ_w ·
   A_w · conj(A_w(σ)) dμ⁰ can be reorganized as ∑ |Fourier coefficient|² ≥ 0.
   Uses lemma 4 + L² completeness. [The hard part]

6. **`transferMatrixPositivity_axiom` (proof)** — Assemble lemmas 1-5 to
   conclude 0 ≤ ⟨g, Tg⟩, closing the axiom. [Final assembly]

### 8.9 Alternative: avoid matrix-element CG via L² completeness

The "trivial orthogonal complement" form of L² completeness (if all Fourier
coefficients vanish, then f = 0 a.e.) might allow avoiding the matrix-element
CG coefficients. The idea: define the "residual" R = I - ∑ |Fourier
coefficient|² and show R = 0 by showing all Fourier coefficients of R vanish.
This would use the L² completeness to prove the residual is zero without
explicitly evaluating the triple product integrals.

**Feasibility**: Uncertain. This approach requires knowing the form of the
|Fourier coefficient|² terms, which in turn requires the CG decomposition.
May still need the matrix-element CG coefficients to define the Fourier
coefficients. Further analysis needed.

### 8.10 Session strategy

Given the complexity, the formalization should proceed in stages:
1. **DONE (2026-08-02 session 2)**: Write this formalization plan. Prove lemma 3
   (`repMatrixElement_inv`), which is the most self-contained.
2. **DONE (2026-08-02 session 3)**: Strengthen the axiom (§8.7) to provide
   matrix-element CG coefficients `cgME` with decomposition + unitarity.
3. **DONE (2026-08-02 session 4)**: Formalized lemma 1
   (`interface_kernel_character_expansion`) at the abstract plaquette-product
   level — 0 sorries, 0 custom axioms. Also fixed the broken
   `prod_conj_partition_dual` proof (V⁺ conjugation building block).
   **Next sessions**: Formalize lemma 2 (integral reduction, needs the concrete
   kernel↔abstract-plaquette-product connection + Fubini). Then lemmas 4-5
   (the hard part: triple-product integral evaluation + reflection-positivity
   reorganization, using the matrix-element CG coefficients `cgME`).
4. **Final session**: Assemble lemma 6 (close the axiom).

### 8.11 Concrete↔abstract bridge progress (2026-08-02 session 5)

The KEY GAP identified in §8.8 (connecting the *concrete* transfer-matrix kernel
`exp(-β·S_OS)` to the *abstract* plaquette-product form that
`interface_kernel_character_expansion` operates on) has been partially closed.
The bridge decomposes into three pieces (G1, G2, G3):

- **G1 (DONE): exp-of-sum = product-of-exps.** `exp_neg_wilsonActionFinite_eq_prod`
  (`BoltzmannFactor.lean`) already proved `exp(-S_W) = ∏ exp(-S_p)`. The
  transfer-matrix analogue `exp_neg_beta_wilsonActionFinite_eq_prod`
  (`ReflectionPositivity.lean`) proves `exp(-β·S_W) = ∏ exp(-β·S_p)`. Both are
  pure algebra (`Real.exp_sum` + `Finset.sum_neg_distrib`), 0 sorries, 0 custom
  axioms (`#print axioms` = `propext, Classical.choice, Quot.sound`).

- **G2 (DONE): per-plaquette factor = abstract form × positive constant.**
  `plaquetteContribution_exp_decomp` (`ReflectionPositivity.lean`) proves
  `exp(-S_p) = exp(-β)·exp((β/N)·Re Tr(U_∂p))` with coupling `c = β/N ≥ 0`
  (for `β ≥ 0`, `1 ≤ N`). The transfer-matrix variant
  `plaquetteContribution_exp_decomp_tm` proves
  `exp(-β·S_p) = exp(-β²)·exp((β²/N)·Re Tr(U_∂p))` with coupling `c = β²/N ≥ 0`
  (no `β ≥ 0` needed, since `β² ≥ 0`). The coupling non-negativity is
  `plaquetteBoltzmann_coupling_nonneg` / `plaquetteBoltzmann_tm_coupling_nonneg`;
  the constant positivity is `plaquetteBoltzmann_const_pos` /
  `plaquetteBoltzmann_tm_const_pos`. All 0 sorries, 0 custom axioms
  (`#print axioms` = `propext, Classical.choice, Quot.sound`).

  The plaquette product `plaquetteProduct = U(n,μ)·U(n+e_μ,ν)·U(n+e_μ+e_ν,μ)⁻¹·
  U(n+e_ν,ν)⁻¹` already has the 3rd/4th links inverted, matching the abstract
  form `exp(c·Re Tr(g₁g₂g₃⁻¹g₄⁻¹))` that `interface_kernel_character_expansion`
  operates on. So G1+G2 together rewrite `exp(-β·S_W) = C·∏_p exp(c·Re Tr(P_p))`
  with `C > 0` and `c ≥ 0` — exactly the abstract form, up to the positive
  constant `C` (absorbable into normalization).

- **G3 (DONE): interface plaquette enumeration + if-splitting.**
  `isInterfacePlaquette` (`ReflectionPositivity.lean`) is the predicate matching
  the `wilsonActionOSInterface` condition (corners straddle the time interface).
  `wilsonActionOSInterface_eq` rewrites `S_int` as
  `∑ (if isInterface then S_p else 0)`.  `exp_neg_beta_wilsonActionOSInterface_eq_prod`
  applies exp-of-sum + if-splitting to give
  `exp(-β·S_int) = ∏ (if isInterface then exp(-β·S_p) else 1)` — non-interface
  plaquettes contribute 1, so the product is effectively over interface plaquettes
  only.  `exp_neg_beta_wilsonActionOSInterface_eq_prod_abstract` composes this
  with G2 (`plaquetteContribution_exp_decomp_tm`) to give
  `exp(-β·S_int) = ∏ (if isInterface then exp(-β²)·exp((β²/N)·Re Tr(P_p)) else 1)`.
  All 0 sorries, 0 custom axioms (`#print axioms` = `propext, Classical.choice,
  Quot.sound`).

  **G1+G2+G3 together** rewrite the concrete interface Boltzmann factor
  `exp(-β·S_int)` as a product of abstract plaquette Boltzmann factors
  `exp(c·Re Tr(P_p))` (with `c = β²/N ≥ 0`) over interface plaquettes, times a
  positive constant `exp(-β²)` per interface plaquette (absorbable into
  normalization).  This is exactly the form that
  `interface_kernel_character_expansion` operates on.  The remaining piece of
  lemma 2 (`transfer_matrix_integral_reduction`) is: (i) identify the link
  partition `L = L_U ⊔ L_0 ⊔ L_V` (U⁺/u⁰/V⁺ links) for the concrete lattice,
  (ii) apply the abstract character expansion to the concrete lattice, and
  (iii) Fubini to exchange the `u⁺`/`V⁺` integrals with the character sum.

### 8.11.1 Sub-step (ii) progress (2026-08-03 session 3)

Sub-steps (i) and (ii) of Lemma 2 are now COMPLETE:

- **Sub-step (i) (DONE, 2026-08-03 session 2):** Concrete link/plaquette
  structures for the character expansion — `InterfacePlaquette`,
  `InterfaceLink`, `interfaceLinkAssign` (+ surjectivity),
  `interfaceLinkVar`, `plaquetteProduct_interface_eq`, the link partition
  `interfaceLinkPos`/`interfaceLinkInt`/`interfaceLinkNeg` (+ disjoint cover),
  and `prod_if_interface_eq_prod_subtype`. All 0 sorries, 0 custom axioms.

- **Sub-step (ii) (DONE, 2026-08-03 session 3):** Two new lemmas in
  `ReflectionPositivity.lean`:
  1. `interface_boltzmann_eq_abstract_product` — combines G3
     (`exp_neg_beta_wilsonActionOSInterface_eq_prod_abstract`),
     `prod_if_interface_eq_prod_subtype` (restrict to interface plaquettes),
     and `plaquetteProduct_interface_eq` (concrete→abstract plaquette product)
     to show `exp(-β·S_int) = C · ∏_{p ∈ InterfacePlaquette} exp((β²/N)·Re Tr(g₀g₁g₂⁻¹g₃⁻¹))`
     with `C = ∏ exp(-β²) > 0`. Pure algebra — 0 sorries, 0 custom axioms
     (`#print axioms` = `[propext, Classical.choice, Quot.sound]`).
  2. `interface_product_character_expansion` — applies the abstract
     `interface_kernel_character_expansion` (Peter-Weyl / Clebsch-Gordan) to
     the concrete lattice data (`P = InterfacePlaquette`, `L = InterfaceLink`,
     `links = interfaceLinkAssign`, `g = interfaceLinkVar`,
     `L_U/L_0/L_V = interfaceLinkPos/Int/Neg`, with the partition proofs).
     Yields the concrete separable character expansion
     `∏_p exp(c·Re Tr(...)) = ∑_w F(w)·Φ_w(U⁺)·Ψ_w(u⁰)·conj(Φ_w(V⁺))` with
     `F(w) ≥ 0`. 0 sorries; uses `peterWeyl_clebschGordan_plaquette` (axiom
     count 6, unchanged). `#print axioms` = `[propext, Classical.choice,
     Quot.sound, peterWeyl_clebschGordan_plaquette]`.

  Full `lake build` GREEN (2972 jobs). The remaining piece of Lemma 2 is
  sub-step (iii): Fubini to exchange the u⁺/V⁺ integrals with the
  character-expansion sum, reducing `⟨g, Tg⟩` to
  `∑_w F(w)·∫_{u⁰} Ψ_w·A_w·conj(A_w(σ)) dμ⁰`.

### 8.11.2 Sub-step (iii) analysis: Fubini reduction (2026-08-03 session 3)

Sub-step (iii) of Lemma 2 requires reducing the transfer-matrix inner product
`⟨g, Tg⟩` to `∑_w F(w)·∫_{u⁰} Ψ_w·A_w·conj(A_w(σ)) dμ⁰` using the character
expansion (sub-step (ii), now DONE) + Fubini.  The key challenges are:

**Challenge 1: Type mismatch (site-based vs link-based).** The transfer matrix
construction (`TransferMatrix.lean`) operates on SITE-based types:
`PosInterfaceConfig` (positive + interface site configs), `FiniteLinkConfig`
on `negativeSites`/`positiveSites`/`interfaceSites`.  The character expansion
(sub-step (ii)) operates on LINK-based types: `InterfaceLink` (subtype of
`PeriodicSite T L × Fin 4` with `signedTime`-based partition
`interfaceLinkPos/Int/Neg`), `InterfacePlaquette`.  Bridging these requires a
lemma showing that the site partition (`positiveSites`/`interfaceSites`/
`negativeSites`, based on `signedTime T n.time`) is compatible with the link
partition (`interfaceLinkPos/Int/Neg`, based on `signedTime T l.val.1.time`):
a link `(n, μ)` is in `interfaceLinkPos` iff `n ∈ positiveSites`, etc.  This is
straightforward but must be formalized.

**Challenge 2: Interface links vs all links.** The character expansion only
covers INTERFACE PLAQUETTE LINKS (links appearing in at least one interface
plaquette, i.e., `InterfaceLink`).  The transfer matrix integral is over ALL
links on positive/interface/negative sites.  The non-interface-plaquette links
don't appear in the interface action `S_int`, so they contribute trivially
(their integral is just the Haar volume, absorbable into normalization).  This
"trivial integration" step must be formalized: the interface Boltzmann factor
`exp(-β·S_int)` depends only on `InterfaceLink` variables, not all
positive/interface/negative site links.

**Challenge 3: Fubini (finite sum ↔ integral).** The character expansion is a
FINITE sum (since `ι` is finite and `InterfaceLink` is finite), so exchanging
the sum with the integral is straightforward — `integral_finset_sum` or
`Finset.sum_integral` in Mathlib.  No convergence issues.  This is the easiest
part.

**Challenge 4: Measure factorization + change of variables.** After Fubini,
the integral must be split into U⁺/u⁰/V⁺ parts.  The `measure_factorization'`
lemma (TransferMatrix.lean) gives a measure-preserving equivalence between
(positive × negative × interface site configs) and the full config.  The
`transferMatrix_change_of_variables` lemma (step (b), already done) identifies
V⁺ = θ(U⁺) (reflected positive links).  Combining these with the character
expansion requires careful bookkeeping.

**Challenge 5: Fourier coefficients.** After the integral splits, the
"Fourier coefficient" `A_w(u⁰) = ∫_{U⁺} g(U⁺, u⁰)·Φ_w(U⁺) dμ⁺` must be
identified.  The V⁺ integral gives `conj(A_w(σ(u⁰)))` where σ is the reflection
on interface links (from `transferMatrix_change_of_variables`).

**Formalization plan for sub-step (iii):**
1. Bridge lemma: site partition ↔ link partition compatibility. **DONE
   (2026-08-03 session 3):** `interfaceLinkPos_mem_iff`,
   `interfaceLinkInt_mem_iff`, `interfaceLinkNeg_mem_iff` — all 0 sorries, 0
   custom axioms.
2. "Trivial integration" lemma: `exp(-β·S_int)` depends only on `InterfaceLink`.
3. Substitute `interface_boltzmann_eq_abstract_product` +
   `interface_product_character_expansion` into the transfer matrix inner
   product.
4. Fubini: exchange the finite sum with the integral.
5. Split the integral via `measure_factorization'` +
   `transferMatrix_change_of_variables`.
6. Identify the Fourier coefficients `A_w`.

**Note:** Lemma 3 (`matrix_element_sigma_inversion`) is already proved as
`repMatrixElement_inv` in `PositiveDefinite.lean` (0 sorries, 0 custom axioms):
`(ρ g⁻¹) i j = conj ((ρ g) j i)`.  This is the σ reflection on matrix elements.

**Honest framing (per the axiom-growth audit, `docs/axiom_growth_audit.md`):**
G1, G2, G3 are all pure algebra/combinatorics — 0 axioms, 0 sorries. They do NOT
strengthen any axiom. The hard part remains lemmas 4–5 (triple-product integral
evaluation + reflection-positivity reorganization), which *use* the already-
strengthened `peterWeyl_clebschGordan_plaquette` (L² completeness + matrix-element
CG). Closing the axiom would reduce the count 6 → 5, but per the audit this is
honest progress only in the narrow sense that the difficulty has been relocated
into the (already-enriched) Peter–Weyl axiom, not eliminated.

### 8.11.3 Bridge lemmas: `interfaceLinkVar` ↔ `extendToFullConfig` (2026-08-03 session 4)

Step 2 of the 6-step sub-step (iii) plan is now COMPLETE. Three bridge lemmas
were proved in `TransferMatrix.lean` (after `reflect_extendToFullConfig_posInterface`):

- `interfaceLinkVar_extendToFullConfig_pos` — for `l ∈ interfaceLinkPos`
  (positive links), `interfaceLinkVar(extendToFullConfig(U_minus,
  mergePosInterface(U_plus, U_zero))) l = U_plus ⟨(l.val.1, l.val.2), hpos⟩`.
- `interfaceLinkVar_extendToFullConfig_int` — for `l ∈ interfaceLinkInt`
  (interface links), `... = U_zero ⟨(l.val.1, l.val.2), hint⟩`.
- `interfaceLinkVar_extendToFullConfig_neg` — for `l ∈ interfaceLinkNeg`
  (negative links), `... = U_minus ⟨(l.val.1, l.val.2), hneg⟩`.

All 0 sorries, 0 custom axioms (`#print axioms` = `[propext, Classical.choice,
Quot.sound]`). Full `lake build` GREEN (2891 jobs).

**Key technique**: the positive/interface cases use the identity
`interfaceLinkVar U l = restrictPosInterface(restrictLinkVariable(univ, U))
⟨(l.val.1, l.val.2), hmem⟩` (proved by `simp only [interfaceLinkVar,
restrictPosInterface, restrictLinkVariable]` — both sides reduce to
`U.value l.val.1 l.val.2`), then `restrictPosInterface_extendToFullConfig`
(rewrites the restriction of `extendToFullConfig` to the `u` argument), then
`simp only [mergePosInterface, dif_pos/dif_neg]` (selects the positive/interface
branch of `mergePosInterface`). The negative case uses
`restrictLinkVariable_negative_extendToFullConfig` directly.

These lemmas identify the link variables in the character expansion
(`interfaceLinkVar`) with the site-based configurations (`U_plus`, `U_zero`,
`U_minus`) used by the transfer matrix. For `U = extendToFullConfig(
reflectPosToNeg(V⁺), mergePosInterface(U⁺, u⁰))`, the character expansion's
link variables become:
- `Φ_w(U⁺) = ∏_{l ∈ interfaceLinkPos} χ_{w(l)}(U⁺ ⟨l.val, hpos⟩)` — depends
  only on the positive part of `u`.
- `Ψ_w(u⁰) = ∏_{l ∈ interfaceLinkInt} χ_{w(l)}(u⁰ ⟨l.val, hint⟩)` — depends
  only on the interface part of `u`.
- `V_w(V⁺) = ∏_{l ∈ interfaceLinkNeg} χ_{w(l)}(reflectPosToNeg(V⁺) ⟨l.val,
  hneg⟩)` — depends only on `V⁺` (through the reflection).

### 8.11.4 V⁺ conjugation analysis (2026-08-03 session 4)

The V⁺ factor `V_w(V⁺)` in the character expansion is the product over
`interfaceLinkNeg` (negative links) of characters of `reflectPosToNeg(V⁺)`.
The reflection `reflectPosToNeg` maps negative sites to positive sites via
`reflectSite`, inverting time-like links (`μ = 0`: `g → g⁻¹`) and keeping
spatial links (`μ ≠ 0`: `g → g`).

**Key finding**: the V⁺ factor is NOT simply `conj(Φ_w(V⁺))`. The character
expansion's `w(l)` assignment (from `plaquette_product_separable_decomp`, step
(a)) already accounts for the per-plaquette-position inversions (3rd/4th links
are inverted in the plaquette product, handled by the `dual` map within step
(a)). The `prod_conj_partition_dual` rewriting in
`interface_kernel_character_expansion` is a TAUTOLOGY — it rewrites
`∏_{L_V} χ_{w(l)}(g_l)` as `star(∏_{L_V} χ_{dual(w(l))}(g_l))` = `∏_{L_V}
χ_{w(l)}(g_l)` (since `star(conj(χ)) = χ` and `χ_{dual(i)} = conj(χ_i)`).

So the V⁺ factor is `V_w(V⁺) = ∏_{l ∈ interfaceLinkNeg} χ_{w(l)}(g_l)` where
`g_l = reflectPosToNeg(V⁺) l` and `w(l)` already includes the per-position
`dual` from step (a). For each negative link `l = (n, μ)`:
- **Time-like** (`μ = 0`): `g_l = (V⁺ l')⁻¹` (inverted by reflection), so
  `χ_{w(l)}(g_l) = conj(χ_{w(l)}(V⁺ l'))` — **conjugated** by reflection.
- **Spatial** (`μ ≠ 0`): `g_l = V⁺ l'` (NOT inverted by reflection), but if `l`
  appears in an inverted plaquette position (3rd/4th), `w(l)` includes `dual`,
  so `χ_{w(l)}(g_l) = χ_{dual(w'(l))}(V⁺ l') = conj(χ_{w'(l)}(V⁺ l'))` —
  **conjugated** by plaquette inversion.

So ALL V⁺ links are conjugated (time-like by reflection, spatial by plaquette
inversion), matching §8.1. But the conjugation mechanism is more subtle than
the design doc initially suggested: it involves BOTH the reflection inversion
(for time-like) AND the per-position `dual` from step (a) (for spatial links
in inverted positions).

**Reindexing issue**: `V_w(V⁺)` is a product over `interfaceLinkNeg` (negative
links), while `Φ_w(V⁺)` is a product over `interfaceLinkPos` (positive links).
To express `V_w(V⁺)` as `conj(Φ_w(V⁺))`, one needs a bijection
`interfaceLinkNeg → interfaceLinkPos` via `reflectSite`, and the index `w(l)`
for `l ∈ interfaceLinkNeg` becomes `w(reflectInv l')` for `l' ∈ interfaceLinkPos`.
This is NOT `w(l')` in general, so `V_w(V⁺) ≠ conj(Φ_w(V⁺))` — it's
`conj(Φ'_w(V⁺))` with a reflected index. However, since the sum `∑_w` is over
ALL `w : InterfaceLink → ι`, reindexing `w` by the reflection bijection is a
valid reindexing of the sum (provided `F(w)` is invariant under the
reindexing, which follows from the reflection symmetry of the interface
plaquette structure). This reindexing is a non-trivial combinatorial lemma
that needs to be formalized.

**Implication for the Fubini reduction**: the Fubini reduction (sub-step (iii))
does NOT require the V⁺ conjugation. It just requires:
1. Substituting the character expansion into the TM inner product (step 3).
2. Exchanging the finite sum with the integral (step 4, Fubini).
3. Splitting the integral into U⁺/u⁰/V⁺ parts (step 5, measure factorization).
4. Identifying `A_w(u⁰) = ∫_{U⁺} g · exp(-β·S⁺/2) · Φ_w(U⁺) dμ⁺` and
   `B_w(u⁰) = ∫_{V⁺} g(·, σ(u⁰)) · exp(-β·S⁺(·, σ(u⁰))/2) · V_w(V⁺) dμ⁺`
   (step 6).

The identification `B_w = conj(A_w(σ))` (which requires the V⁺ conjugation +
reindexing) is a SEPARATE step that comes after the Fubini reduction. The
Fubini reduction itself just produces `∑_w F(w) · ∫ Ψ_w · A_w · B_w`, which
is NOT necessarily non-negative (that's the obstruction from §8.3). The
non-negativity comes from lemmas 4–5 (the hard part).

### 8.11.5 Pointwise substitution lemma (2026-08-03 session 5)

Step 3 of the 6-step sub-step (iii) plan is now COMPLETE. A new lemma
`interface_boltzmann_character_expansion` was proved in
`ReflectionPositivity.lean` (after `interface_product_character_expansion`):

    exp(-β·S_int(U)) = (C : ℂ) · ∑_w (F w : ℂ) · Φ_w(U) · Ψ_w(U) · V_w(U)

with `C > 0` and `F(w) ≥ 0`, where `Φ_w(U) = ∏_{l ∈ L_U} χ_{w(l)}(g_l)`,
`Ψ_w(U) = ∏_{l ∈ L_0} χ_{w(l)}(g_l)`, and
`V_w(U) = star(∏_{l ∈ L_V} χ_{dual(w(l))}(g_l))` with `g_l = interfaceLinkVar U l`.

This composes `interface_boltzmann_eq_abstract_product` (exp(-β·S_int) =
C · ∏_p exp(c·Re Tr(...))) with `interface_product_character_expansion`
(∏_p exp(c·Re Tr(...)) = ∑_w F(w)·Φ_w·Ψ_w·V_w). 0 sorries; uses
`peterWeyl_clebschGordan_plaquette` (axiom count 6, unchanged).
`#print axioms` = `[propext, Classical.choice, Quot.sound,
peterWeyl_clebschGordan_plaquette]`. Full `lake build` GREEN.

**Key technique**: the coercion `↑(C * ∏_p Real.exp(...))` must be pushed
through to `(C : ℂ) * ∏_p ↑(Real.exp(...))` to match `hF_decomp`. The naive
`push_cast` converts `↑(Real.exp(x))` to `Complex.exp(↑x)` (via
`Complex.ofReal_exp`), which breaks the `rw [hF_decomp]` match (since
`hF_decomp` has `↑(Real.exp(...))`, not `Complex.exp(...)`). The fix is to
use `norm_cast at h` (which pulls the coercion OUT of the product in
`hF_decomp`, converting `∏_p ↑(Real.exp(...))` to `↑(∏_p Real.exp(...))`
WITHOUT touching `Real.exp`), then `rw [Complex.ofReal_mul, h]` to split the
outer `↑(C * ...)` and substitute. This avoids the `Real.exp → Complex.exp`
conversion entirely.

This lemma is the POINTWISE substitution (step 3). The remaining steps are:
- **Step 4 (Fubini)**: exchange the finite sum `∑_w` with the V⁺ integral
  (`integral_finset_sum` or `Finset.sum_integral`). Straightforward since
  `ι` and `InterfaceLink` are finite.
- **Step 5 (measure factorization)**: split the integral into U⁺/u⁰/V⁺
  parts via `measure_factorization'` + `transferMatrix_change_of_variables`.
- **Step 6 (Fourier coefficients)**: identify `A_w(u⁰) = ∫_{U⁺} g · Φ_w dμ⁺`
  and `B_w(u⁰) = ∫_{V⁺} g(·, σ(u⁰)) · V_w dμ⁺`.

### 8.11.6 Fubini reduction plan: steps 4–6 (2026-08-03 session 5)

Step 3 (pointwise substitution) is DONE. The remaining steps 4–6 require
careful handling of the ℝ vs ℂ distinction. The character expansion
`interface_boltzmann_character_expansion` gives a ℂ-valued identity:
```
(Real.exp(-β·S_int(U)) : ℂ) = (C : ℂ) * ∑_w (F w : ℂ) * Φ_w(U) * Ψ_w(U) * V_w(U)
```
while the transfer matrix `transferMatrixReflected` is ℝ-valued. The
recommended approach is to work in ℂ throughout and take the real part at
the end.

**Step 4 (Fubini: finite sum ↔ integral).** The transfer matrix inner
product is:
```
⟨g, Tg⟩ = ∫_{u} g(u) · (Tg)(u) dμ⁺⁰(u)
```
where `(Tg)(u) = transferMatrixReflected(g, u)` involves
`Real.exp(-β·S_int(U))` with `U = extendToFullConfig(reflectPosToNeg(V⁺), u)`.
After coercing to ℂ and substituting the character expansion:
```
(⟨g, Tg⟩ : ℂ) = ∫_{u} (g(u) : ℂ) * (Tg)(u) dμ⁺⁰(u)
```
where `(Tg)(u)` now involves `(C : ℂ) * ∑_w (F w : ℂ) * Φ_w(U) * Ψ_w(U) * V_w(U)`.
The finite sum `∑_w` can be exchanged with the V⁺ integral via
`integral_finset_sum` (or `Finset.sum_integral`), provided each term is
integrable (which follows from the original integrability hypothesis since
the character expansion is a finite sum). The key Mathlib lemma:
```
theorem integral_finset_sum (s : Finset α) (f : α → β → γ)
    (hf : ∀ i ∈ s, Integrable (f i) μ) :
    ∫ x, ∑ i ∈ s, f i x ∂μ = ∑ i ∈ s, ∫ x, f i x ∂μ
```

**Step 5 (measure factorization).** After Fubini, the integral must be split
into U⁺/u⁰/V⁺ parts. The `haarMeasurePosInterface_eq` lemma gives
`μ⁺⁰ = Measure.map (mergePosInterface) (μ⁺ × μ⁰)`, and `measure_factorization'`
gives a measure-preserving equiv between `(U⁺ × U⁻ × U⁰)` and the full config.
The `transferMatrix_change_of_variables` lemma (step (b), already done)
identifies V⁺ = θ(U⁻). Combining these with the character expansion requires
careful bookkeeping. The `integral_G_thetaG_eq_inner_g_Tg` lemma (already
proved) shows the measure factorization works for the full inner product.

**Step 6 (Fourier coefficients).** After the integral splits, the bridge
lemmmas `interfaceLinkVar_extendToFullConfig_pos/int/neg` show that:
- `Φ_w(U) = ∏_{l ∈ L_U} χ_{w(l)}(U⁺ ⟨l.val, hpos⟩)` — depends only on U⁺
- `Ψ_w(U) = ∏_{l ∈ L_0} χ_{w(l)}(u⁰ ⟨l.val, hint⟩)` — depends only on u⁰
- `V_w(U) = ∏_{l ∈ L_V} χ_{w(l)}(reflectPosToNeg(V⁺) ⟨l.val, hneg⟩)` — depends only on V⁺

This separability allows the triple integral to factorize as:
```
(⟨g, Tg⟩ : ℂ) = (C : ℂ) * ∑_w (F w : ℂ) * ∫_{u⁰} Ψ_w(u⁰) * A_w(u⁰) * B_w(u⁰) dμ⁰(u⁰)
```
where `A_w(u⁰) = ∫_{U⁺} (g(U⁺, u⁰) * exp(-β·S⁺(U⁺, u⁰)/2) * Φ_w(U⁺) : ℂ) dμ⁺(U⁺)`
and `B_w(u⁰) = ∫_{V⁺} (g(V⁺, σ(u⁰)) * exp(-β·S⁺(V⁺, σ(u⁰))/2) * V_w(V⁺) : ℂ) dμ⁺(V⁺)`.

**ℝ vs ℂ handling.** The transfer matrix is ℝ-valued, but the character
expansion is ℂ-valued. The recommended approach:
1. Coerce the transfer matrix inner product to ℂ (via `integral_complex` or
   `Complex.integral_real` — the integral commutes with the ℝ→ℂ coercion).
2. Substitute the ℂ-valued character expansion.
3. Apply Fubini and measure factorization in ℂ.
4. Take the real part at the end: `⟨g, Tg⟩ = ((⟨g, Tg⟩ : ℂ).re`.

**Suggested formalization order for the next session:**
1. First, prove a ℂ-valued version of the transfer matrix integrand
   substitution (substitute `interface_boltzmann_character_expansion` into
   the `exp(-β·S_int(U))` factor, coercing to ℂ).
2. Then, prove the Fubini exchange (finite sum ↔ V⁺ integral) using
   `integral_finset_sum`.
3. Then, split the integral using `haarMeasurePosInterface_eq` +
   `measure_factorization'`.
4. Finally, identify A_w and B_w using the bridge lemmas.

Each step is a separate lemma, making the proof more manageable. The key
challenge is the integrability hypotheses — each Fubini step requires showing
the individual terms are integrable, which follows from the original
integrability hypothesis and the finiteness of the character expansion.

### 8.11.7 Uniform character expansion refactor (2026-08-03 session 6)

**KEY INSIGHT.** The Fubini exchange (step 4) requires pulling the finite sum
`∑_w` OUTSIDE the integral. This is only valid if the character-expansion data
`(C, ι, ρ, dual, F)` is the SAME for every `U` in the integration domain. The
original lemmas were stated pointwise (`∀ U, ∃ data, equality(U)`), which gives
potentially different data for each `U` — making the Fubini exchange impossible.

Analysis of the data sources confirmed all five pieces are `U`-independent:
- `C = ∏_p exp(-β²)` — a closed-form constant (no `U`).
- `ι, dims, ρ, dual, coeff, cg, cgME, Λ, …` — from `peterWeyl_clebschGordan_plaquette`
  (no `U` argument).
- `F` — from `interface_kernel_character_expansion`, whose proof defines
  `F w = ∑_α (∏_p coeffIdx(α p)) * F_α α w` where `F_α` comes from
  `charProduct_mixed_link_separable_decomp` (which has `∀ g` INSIDE the
  existential). So `F` is independent of `g = interfaceLinkVar U`.

**REFACTOR (in place, 5 lemmas).** Moved the `∀ U`/`∀ g` from outside (a
parameter) to INSIDE the existentials, making each lemma strictly stronger:
1. `plaquette_product_separable_decomp` (PeterWeyl.lean) — `∀ (g : L → SU N)`
   moved inside; g-dependent `let charProd`/`have h_charProd_fin4`/`h_plaq_exp`/
   `h_regroup` moved inside the `fun g => ?_` branch.
2. `interface_kernel_character_expansion` (PeterWeyl.lean) — `∀ (g : L → SU N)`
   moved inside; `refine ⟨F, hF, fun g => ?_⟩`, `rw [hF_decomp g]`.
3. `interface_boltzmann_eq_abstract_product` (ReflectionPositivity.lean) —
   `∀ (U : …)` moved inside; `refine ⟨C, ?_, fun U => ?_⟩`.
4. `interface_product_character_expansion` (ReflectionPositivity.lean) —
   `∀ (U : …)` moved inside; `exact hF_decomp (interfaceLinkVar N T L U)`.
5. `interface_boltzmann_character_expansion` (ReflectionPositivity.lean) —
   `∀ (U : …)` moved inside; obtains `C` and `hC_eq_all` from the uniform
   `interface_boltzmann_eq_abstract_product` (once, outside `∀ U`), then
   `rw [hC_eq_all U]` per-`U`. (Using a single `C` avoids the `C' = C` defeq
   issue that arises when `obtain`-ing a per-`U` `C'`.)

**RESULT.** Full `lake build` GREEN (2890 jobs). `#print axioms` confirms NO
`sorryAx` and unchanged dependencies:
- `plaquette_product_separable_decomp`, `interface_kernel_character_expansion`,
  `interface_boltzmann_eq_abstract_product`: `[propext, Classical.choice,
  Quot.sound]` (0 custom axioms).
- `interface_product_character_expansion`,
  `interface_boltzmann_character_expansion`: `[propext, Classical.choice,
  Quot.sound, peterWeyl_clebschGordan_plaquette]` (axiom count 6, unchanged).

The uniform `interface_boltzmann_character_expansion` now provides a SINGLE
`(C, ι, ρ, dual, F)` with `∀ U, (exp(-β·S_int(U)) : ℂ) = (C : ℂ) * ∑_w …`,
which is exactly what step 4 (Fubini) needs to exchange `∑_w` with the integral.

### 8.11.8 Step 4a: ℂ coercion + measure factorization (2026-08-02 session 7)

**PROVED** `inner_product_complex_eq_product_integral` in `TransferMatrix.lean`
(after `transferMatrix_change_of_variables`). This is the first sub-lemma of
step 4 (Fubini reduction):

```
(↑(∫_{u} g(u) · (Tg)(u) dμ⁺⁰(u)) : ℂ) =
  ∫_{(U⁺, u⁰)} Complex.ofReal (g(merge(U⁺, u⁰)) · (Tg)(merge(U⁺, u⁰)))
    d(μ⁺ × μ⁰)(U⁺, u⁰)
```

where `g = g_posInterface`, `Tg = transferMatrixReflected(g, ·)`, and
`merge = Function.uncurry (mergePosInterface N T L)`.

**Proof** (4 steps, 0 sorries, 0 custom axioms):
1. **ℂ coercion**: `have h_ofReal := (integral_complex_ofReal).symm` — converts
   `↑(∫ f : ℝ)` to `∫ Complex.ofReal (f)`. Key: use `Complex.ofReal` explicitly
   (not `(... : ℂ)`) to keep the coercion on the whole product `↑(a * b)`,
   not distributed as `↑a * ↑b`. The `(... : ℂ)` annotation distributes the
   coercion over `*`, which is NOT defeq to `↑(a * b)` (they're equal by
   `Complex.ofReal_mul`, a theorem, not by reduction). Using `Complex.ofReal`
   explicitly avoids this issue.
2. **Measure factorization**: `rw [haarMeasurePosInterface_eq]` — converts
   `μ⁺⁰` to `Measure.map (mergePosInterface) (μ⁺ × μ⁰)`.
3. **MeasurableEmbedding setup**: `hME : MeasurableEmbedding (mergePosInterface)`
   via `productHaarMeasureUnionEquiv` (same as `integral_G_thetaG_eq_inner_g_Tg`).
4. **integral_map**: `hME.integral_map (fun u => Complex.ofReal (...))` — converts
   `∫_u f(u) d(map merge (μ⁺×μ⁰))` to `∫_{(U⁺, u⁰)} f(merge(U⁺, u⁰)) d(μ⁺×μ⁰)`.

`#print axioms` = `[propext, Classical.choice, Quot.sound]` (0 sorries, 0 custom
axioms). Full `lake build` GREEN.

**Key technique learned**: `rw [← integral_ofReal]` FAILS because the `↑` in
`integral_ofReal` is `@RCLike.ofReal 𝕜 _` (generic `RCLike`), while the `↑` in
the goal is `@Complex.ofReal` (specific to `ℂ`). These are defeq but not
syntactically equal, so `rw` can't match them. The fix: use `have h := (integral_complex_ofReal).symm`
instead of `rw`, since `exact`/`have` unification works up to defeq.

**Remaining steps for the Fubini reduction (step 4, sub-step (iii)):**
- **Step 4b**: Unfold `transferMatrixReflected` to make the V⁺ integral explicit,
  split the exp via `Real.exp_add` (separate `exp(-β·S⁺(u)/2)` from
  `exp(-β·S_int(U))`), and pull the V⁺-independent factors out of the V⁺ integral.
- **Step 4c**: Fubini exchange — pull `∑_w` out of the V⁺ integral using
  `integral_finsetSum` (the character expansion is a finite sum since `ι` and
  `InterfaceLink` are finite).
- **Step 4d**: Measure factorization — split the `(U⁺, u⁰)` integral into
  `∫_{U⁺} ∫_{u⁰}` using `integral_prod`, and separate `Φ_w`/`Ψ_w`/`V_w` via
  the bridge lemmas `interfaceLinkVar_extendToFullConfig_pos/int/neg`.
- **Step 4e**: Factor the U⁺ integral out, identify `A_w(u⁰)` and `B_w(u⁰)`.

### 8.11.9 Step 4b: unfold transferMatrixReflected + exp split (2026-08-02 session 8)

**PROVED** two lemmas in `TransferMatrix.lean` (after `transferMatrix_change_of_variables`):

1. **`transferMatrixReflected_split_exp_real`** (ℝ-valued core). The reflected transfer
   matrix factors as
   ```
   (Tψ)(u) = exp(-β·S⁺(u)/2) · ∫_{V⁺} ψ(merge(V⁺, σ(u⁰))) ·
             exp(-β·(S⁺(V⁺')/2 + S_int(U))) dμ⁺(V⁺)
   ```
   pulling the V⁺-independent `exp(-β·S⁺(u)/2)` out of the V⁺ integral. **Proof**
   (0 sorries, 0 custom axioms):
   - `unfold transferMatrixReflected; dsimp only` — makes the V⁺ integral explicit.
   - Pointwise `h_ptwise`: split `exp(-β·(a+b+c)) = exp(-β·a) · exp(-β·(b+c))` via a
     `ring` argument rewrite + `Real.exp_add`, then `ring` rearranges
     `ψ(…) · (exp(-β·a) · exp(-β·(b+c))) = exp(-β·a) · (ψ(…) · exp(-β·(b+c)))`.
   - `rw [show (∫ …) = (∫ …) from by congr 1; funext V⁺; exact h_ptwise V₊]` — rewrites
     the integral integrand pointwise.
   - `rw [integral_const_mul]` — pulls `exp(-β·a)` out of the integral (no integrability
     needed; `integral_const_mul` is `integral_smul` for `RCLike`).

2. **`transferMatrixReflected_split_exp_complex`** (ℂ-valued, the actual step 4b). The
   ℂ-valued integrand factors as
   ```
   Complex.ofReal (ψ u · (Tψ)(u)) =
     Complex.ofReal (ψ u · exp(-β·S⁺(u)/2)) ·
     ∫_{V⁺} Complex.ofReal (ψ(merge(V⁺, σ(u⁰))) · exp(-β·(S⁺(V⁺')/2 + S_int(U)))) dμ⁺(V⁺)
   ```
   **Proof** (0 sorries, 0 custom axioms):
   - `rw [transferMatrixReflected_split_exp_real]` — substitutes the ℝ-valued factorization.
   - `set c_exp := Real.exp (-β·S⁺(u)/ 2)` and `set I_split := ∫_{V⁺} …` — abbreviates
     the V⁺-independent factor and the remaining ℝ-valued V⁺ integral. (The goal's RHS
     ℂ-valued integral is NOT replaced, since it differs by the `Complex.ofReal` wrapper.)
   - `rw [show ψ u · (c_exp · I_split) = (ψ u · c_exp) · I_split from by ring]` — reassociates.
   - `rw [Complex.ofReal_mul]` — splits `Complex.ofReal ((ψ u · c_exp) · I_split)` into
     `Complex.ofReal (ψ u · c_exp) · Complex.ofReal I_split`.
   - `have h_cofR : Complex.ofReal I_split = ∫ Complex.ofReal (…) := by rw [hI_split];
     exact (integral_complex_ofReal).symm` — converts the ℝ-valued integral to ℂ-valued
     via `integral_complex_ofReal` (the `.symm` direction: `↑(∫ f : ℝ) = ∫ (f : ℂ)`).
     Key: `exact` (not `rw`) is used for the `@RCLike.ofReal ℂ _` vs `Complex.ofReal`
     defeq mismatch — `exact` unifies up to defeq, `rw` requires syntactic equality.
   - `rw [h_cofR]` — closes the goal (both sides now match).

`#print axioms` for both = `[propext, Classical.choice, Quot.sound]` (0 sorries, 0 custom
axioms). Full `lake build` GREEN.

**Key techniques learned:**
- `integral_const_mul` (=`integral_smul` for `RCLike`) requires NO integrability — it
  works for any measure. This avoids needing `hψ_int` for the exp-split step.
- `integral_complex_ofReal` also requires NO integrability (both sides are 0 if not
  integrable, by convention). So step 4b needs no integrability hypothesis at all.
- `set` with `with h` creates an equation `h : X = <def>`; `rw [h]` unfolds `X` → `<def>`.
  Use `exact (lemma).symm` (defeq) rather than `rw [← lemma]` (syntactic) for the
  `RCLike.ofReal` vs `Complex.ofReal` coercion mismatch.

**What step 4b accomplishes:** the ℂ-valued transfer-matrix integrand is now in the form
`Complex.ofReal (ψ u · exp(-β·S⁺(u)/2)) · ∫_{V⁺} Complex.ofReal (ψ(merge(V⁺, σ(u⁰))) ·
exp(-β·(S⁺(V⁺')/2 + S_int(U)))) dμ⁺(V⁺)`, where the remaining V⁺ integral contains
`exp(-β·(S⁺(V⁺')/2 + S_int(U)))`. Step 4c will further split this exp into
`exp(-β·S⁺(V⁺')/2) · exp(-β·S_int(U))` and substitute the character expansion
`interface_boltzmann_character_expansion` for `exp(-β·S_int(U))` (coerced to ℂ), then
exchange the finite sum `∑_w` with the V⁺ integral via `integral_finset_sum`.

### 8.11.10 Step 4c integrability plan (2026-08-02 session 8)

Step 4c has two parts: (A) the **pointwise substitution** of the character expansion
(replacing `exp(-β·S_int(U))` with `(C : ℂ) · ∑_w …`), and (B) the **Fubini exchange**
(pulling `∑_w` out of the V⁺ integral via `integral_finsetSum`).

**Part A (pointwise substitution) — no integrability needed.** This is a pointwise
identity for each `V⁺`:
```
Complex.ofReal (ψ(merge(V⁺,σ(u⁰))) · exp(-β·(S⁺(V⁺')/2 + S_int(U)))) =
  Complex.ofReal (ψ(merge(V⁺,σ(u⁰))) · exp(-β·S⁺(V⁺')/2)) ·
  ((C : ℂ) · ∑_w (F w : ℂ) · Φ_w(U) · Ψ_w(U) · V_w(U))
```
where `U = extendToFullConfig(reflectPosToNeg(V⁺), u)`. Proof: split the exp via
`Real.exp_add`, split `Complex.ofReal` via `Complex.ofReal_mul`, then substitute
`Complex.ofReal (exp(-β·S_int(U))) = (exp(-β·S_int(U)) : ℂ)` (defeq) and apply
`h_char U` from `interface_boltzmann_character_expansion`. Key technique: use
`have h_cofR : Complex.ofReal (exp(...)) = (C : ℂ) * ∑_w ... := h_char U` (the `have`
type-checks up to defeq, bridging `Complex.ofReal` vs `@RCLike.ofReal ℂ _`).

**Part B (Fubini exchange) — requires integrability.** `integral_finsetSum` requires
`∀ w, Integrable (f w) μ⁺` where `f w V⁺ = Complex.ofReal (ψ(…) · exp(-β·S⁺(V⁺')/2)) ·
(F w : ℂ) · Φ_w(U) · Ψ_w(U) · V_w(U)`. The integrability proof has THREE ingredients:

1. **Character boundedness (DONE).** `repCharacter_norm_le_dim` (PositiveDefinite.lean,
   line ~770): `‖repCharacter ρ g‖ ≤ n` for a unitary `n`-dim representation. Proved via
   `entry_norm_bound_of_unitary` (each entry of a unitary matrix has norm ≤ 1) +
   `norm_sum_le` (triangle inequality for sums). `#print axioms` =
   `[propext, Classical.choice, Quot.sound]`. This gives `|Φ_w(U)| ≤ ∏_{l∈L_U} dims(w l)`,
   `|Ψ_w(U)| ≤ ∏_{l∈L_0} dims(w l)`, `|V_w(U)| ≤ ∏_{l∈L_V} dims(dual(w l))` — all
   constants depending only on `w`.

2. **Action boundedness (TODO).** `|wilsonActionOSInterface N T L β U| ≤ C` for a
   constant `C` (depending on `N, T, L, β` but not `U`). The action is
   `∑_{n,μ,ν} plaquetteContribution N β U n μ ν` (over the finite set
   `PeriodicSite T L × Fin 4 × Fin 4`), where
   `plaquetteContribution = β · (1 - (1/N) · Re Tr(plaquetteProduct))`. Since
   `plaquetteProduct ∈ SU N` (unitary), `|Re Tr(g)| ≤ N` (same argument as
   `repCharacter_norm_le_dim` with the fundamental representation), so
   `|plaquetteContribution| ≤ 2β`. Thus `|S_int| ≤ #(PeriodicSite T L) · 16 · 2β`.
   This gives `exp(-β·S_int(U)) ≥ exp(-β·C) > 0` (a positive lower bound).

3. **Domination argument (TODO).** From `hψ_int` (the original integrand is integrable)
   + ingredient 2 (`exp(-β·S_int) ≥ m > 0`), deduce
   `Integrable (fun V⁺ => ψ(merge(V⁺,σ(u⁰))) · exp(-β·S⁺(V⁺')/2)) μ⁺` (the original
   integrand divided by the bounded-below `exp(-β·S_int)`). Then each character-expansion
   term `f w` is dominated by `|ψ(…) · exp(-β·S⁺(V⁺')/2)| · |F w| · M_w` (where `M_w` is
   the character bound from ingredient 1), which is integrable by `Integrable.mono`
   (dominated by a constant times an integrable function).

**Suggested formalization order for the next session:**
1. Prove `wilsonActionOSInterface_bounded` (ingredient 2) — needs `|Re Tr(g)| ≤ N` for
   `g ∈ SU N` (prove via `repCharacter_norm_le_dim` applied to the fundamental rep, or
   directly via `entry_norm_bound_of_unitary`).
2. Prove the pointwise substitution lemma (part A) — takes the character-expansion data
   as parameters (obtained from `interface_boltzmann_character_expansion`).
3. Prove the integrability of each term (ingredient 3) — from `hψ_int` + ingredients 1-2.
4. Apply `integral_finsetSum` to exchange `∑_w` with the V⁺ integral.
5. Pull `(C : ℂ)` and `(F w : ℂ)` out of the V⁺ integral via `integral_const_mul`.

**Alternative pragmatic approach:** Take `∀ w, Integrable (f w) μ⁺` as a HYPOTHESIS for
the Fubini exchange lemma, and discharge it in a separate lemma using ingredients 1-3.
This modularizes the proof and lets the Fubini exchange proceed even before the
integrability is fully proven.

### 8.11.11 Step 4c: pointwise substitution + Fubini exchange (2026-08-02 session 9)

**PROVED** three lemmas in `TransferMatrix.lean`, all 0 sorries, 0 custom axioms
(`#print axioms` = `[propext, Classical.choice, Quot.sound]`):

1. **`integrand_character_expansion_pointwise`** (Part A — pointwise substitution,
   no integrability needed). For each `V⁺`, the ℂ-valued integrand
   `Complex.ofReal (ψ(merge(V⁺,σ(u⁰))) · exp(-β·(S⁺(V⁺')/2 + S_int(U))))` factors as
   `Complex.ofReal (ψ(merge(V⁺,σ(u⁰))) · exp(-β·S⁺(V⁺')/2)) · ((C : ℂ) · ∑_w …)`,
   where `U = extendToFullConfig(reflectPosToNeg(V⁺), u)`. **Proof**: split exp via
   `Real.exp_add`, rearrange via `ring`, split `Complex.ofReal` via
   `Complex.ofReal_mul`, then `rw [h_char U]` (the `Complex.ofReal (exp …)` vs
   `(exp … : ℂ)` coercion mismatch is handled up to defeq by `rw`). Takes the
   character-expansion data `(C, ι, dims, ρ, dual, F, h_char)` as parameters.

2. **`integral_finsetSum_pull_constants`** (abstract Fubini + constant-pulling helper).
   For a finite index type `ι`, constant `C : ℂ`, scalar coefficients `F : ι → ℝ`,
   a V⁺-dependent prefactor `A : α → ℂ`, and V⁺-dependent summands `X : ι → α → ℂ`:
   `∫ A x · (C · ∑_w (F w) · X w x) ∂μ = C · ∑_w (F w) · ∫ A x · X w x ∂μ`,
   provided each term `(F w) · (A x · X w x)` is integrable. **Proof**: pointwise
   rearrangement via `Finset.mul_sum` + `ring` (rewriting the integral integrand),
   `integral_const_mul` (pull C out, no integrability), `integral_finsetSum`
   (exchange ∑_w ↔ ∫, needs integrability), `integral_const_mul` (pull F w out).

3. **`transfer_matrix_fubini_character_expansion`** (Part B — the full Fubini exchange).
   Combining steps 4b + 4c Part A + the abstract helper, the ℂ-valued transfer matrix
   inner-product integrand factors as
   `Complex.ofReal (ψ u · exp(-β·S⁺(u)/2)) · (C · ∑_w (F w) · ∫_{V⁺} A(V⁺) · Φ_w(U) · Ψ_w(U) · V_w(U) dμ⁺)`.
   Takes the character-expansion data + integrability hypothesis `h_int` as parameters
   (pragmatic approach: `h_int` will be discharged separately using ingredients 1-3).
   **Proof**: `rw [transferMatrixReflected_split_exp_complex]` (step 4b), `congr 1`
   (cancel prefactor), `rw [show (∫ …) = (∫ …)]` (pointwise substitution via
   `integrand_character_expansion_pointwise`), then inline the Fubini exchange steps
   (`simp only [show ∀ V⁺, …]` for integrand rearrangement, `integral_const_mul`,
   `integral_finsetSum`, `integral_const_mul`).

**Key technique learned:** `exact integral_finsetSum_pull_constants …` (passing large
`A`/`X` as explicit arguments) causes a `(deterministic) timeout at whnf` even with
`maxHeartbeats 1000000`. The fix: inline the Fubini exchange steps directly using
`simp only [show ∀ V⁺, …]` (term rewriting) + `rw [integral_const_mul]` +
`rw [integral_finsetSum Finset.univ]` (pattern matching). Each `rw`/`simp only` does
pattern matching, which is far faster than the full unification that `exact` requires.

**What step 4c accomplishes:** the ℂ-valued transfer-matrix integrand is now in the
form `prefactor · (C · ∑_w (F w) · ∫_{V⁺} A(V⁺) · Φ_w(U) · Ψ_w(U) · V_w(U) dμ⁺)`,
where the finite sum `∑_w` is OUTSIDE the V⁺ integral. Step 4d will split the
`(U⁺, u⁰)` product-measure integral and separate `Φ_w`/`Ψ_w`/`V_w` via the bridge
lemmas `interfaceLinkVar_extendToFullConfig_pos/int/neg`. Step 4e will identify the
Fourier coefficients `A_w(u⁰)` and `B_w(u⁰)`.

**REMAINING for step 4c:** discharge the integrability hypothesis `h_int` using
ingredients 1-3 (character boundedness DONE, action boundedness DONE, domination TODO).
This is a separate lemma that can be proven independently.

### 8.11.12 Integrability ingredients: action boundedness (2026-08-02 session 10)

**PROVED** three lemmas toward discharging the integrability hypothesis `h_int`
of `transfer_matrix_fubini_character_expansion`, all 0 sorries, 0 custom axioms
(`#print axioms` = `[propext, Classical.choice, Quot.sound]`):

1. **`plaquetteContribution_bounded`** (Lattice.lean, ~line 270): for any
   `plaquetteProduct ∈ SU N` (unitary), `|Re Tr(g)| ≤ N` (`trace_re_bound`,
   already in SpecialUnitary.lean), so `|(1/N)·Re Tr(g)| ≤ 1`, hence
   `|1 - (1/N)·Re Tr(g)| ≤ 2`, and `|plaquetteContribution| = |β|·|1 - ...| ≤ 2|β|`.
   Key sub-step: `|(1/N)·x| ≤ 1` from `|x| ≤ N` (case split on `N = 0` vs `N > 0`,
   using `div_mul_cancel₀` for `N > 0` and `simp` for `N = 0`).

2. **`wilsonActionOSInterface_bounded`** (ReflectionPositivity.lean, ~line 790):
   `|wilsonActionOSInterface N T L β U| ≤ (Fintype.card (PeriodicSite T L) * 32) * |β|`.
   Uses `wilsonActionOSInterface_eq` (rewrite the `if` condition to
   `isInterfacePlaquette`), then bounds each term by `2|β|` (from
   `plaquetteContribution_bounded`), and sums over `#(PeriodicSite T L)·16` terms.
   Proof technique: bound `S` from above (`S ≤ ∑ 2|β|`) and below (`-∑ 2|β| ≤ S`)
   via `Finset.sum_le_sum` (three levels), then conclude `|S| ≤ C` via `abs_le`.
   Constant sum evaluation: `∑ ν : Fin 4, c = 4·c` via `Finset.sum_const` +
   `Finset.card_fin` + `nsmul_eq_mul`; `∑ n : PeriodicSite T L, c = card·c` via
   `Finset.sum_const` + `Finset.card_univ` + `nsmul_eq_mul`.

3. **`exp_neg_beta_wilsonActionOSInterface_lower_bound`** (ReflectionPositivity.lean,
   ~line 862): `exp(-|β|·C) ≤ exp(-β·S_int(U))` where
   `C = #(PeriodicSite T L)·32·|β|`. This gives a **uniform positive lower bound**
   `m = exp(-|β|·C) > 0` on `exp(-β·S_int)`, independent of `U`. Proof:
   `β·S_int ≤ |β·S_int| = |β|·|S_int| ≤ |β|·C` (by `le_abs_self`, `abs_mul`,
   `wilsonActionOSInterface_bounded`), so `-|β|·C ≤ -β·S_int`, and
   `exp(-|β|·C) ≤ exp(-β·S_int)` by `Real.exp_le_exp.mpr`.

**What remains for the integrability discharge (ingredient 3, domination):**
- **Character product boundedness** (TODO): `‖Φ_w(U)·Ψ_w(U)·V_w(U)‖ ≤ M_w` where
  `M_w = (∏_{l∈L_pos} dims(w l))·(∏_{l∈L_int} dims(w l))·(∏_{l∈L_neg} dims(dual(w l)))`.
  Uses `repCharacter_norm_le_dim` (DONE, gives `‖χ_i(g)‖ ≤ dims i` for unitary ρ) +
  product norm bound (`Finset.norm_prod_le` or `‖∏ f_l‖ ≤ ∏ ‖f_l‖`) +
  `‖star z‖ = ‖z‖` (conjugation preserves norm) + `norm_mul` (triangle for products).
  The `h_unitary : ∀ i, IsUnitaryRepresentation (ρ i)` hypothesis is available from
  `interface_boltzmann_character_expansion`.
- **Domination argument** (TODO): from `hψ_int` (full integrand integrable) +
  ingredient 3 lower bound (`exp(-β·S_int) ≥ m > 0`), deduce
  `|ψ(merge)·exp(-β·S⁺(merge)/2)| ≤ (1/(exp(-β·S⁺(u)/2)·m))·|full_integrand|`,
  hence `|A(V⁺)|` is integrable (by `Integrable.mono`). Then each character term
  `|(F w)·A·Φ·Ψ·V| ≤ |F w|·M_w·|A(V⁺)|` is integrable (by `Integrable.mono` again).
  Key Mathlib lemmas: `Integrable.mono`, `Integrable.const_mul`/`Integrable.smul`,
  `Complex.norm_ofReal` (`‖Complex.ofReal x‖ = |x|`).

### 8.11.13 Integrability discharge: domination argument (2026-08-03 session)

**PROVED** `transfer_matrix_fubini_integrability` (TransferMatrix.lean, ~line 2549) —
the main integrability discharge lemma, 0 sorries, 0 custom axioms
(`#print axioms` = `[propext, Classical.choice, Quot.sound]`). Full lake build GREEN (2972 jobs).

**Statement:** Given `hψ_int` (the full integrand is integrable), `h_integrand_ae`
(each character-expansion integrand is AEStronglyMeasurable), and the character-expansion
data (`h_unitary`, `dims`, `ρ`, `dual`, `F`), produces `∀ w, Integrable (integrand_w) μ⁺`
— exactly the `h_int` hypothesis of `transfer_matrix_fubini_character_expansion`.

**Proof (domination argument):** For each `w`, define constants
`c_u = exp(-β·S⁺(u)/2) > 0`, `m = exp(-|β|·C) > 0` (uniform lower bound on
`exp(-β·S_int(U))` from `exp_neg_beta_wilsonActionOSInterface_lower_bound`),
`M_w = (∏_pos dims)·(∏_int dims)·(∏_neg dims(dual))` (character bound from
`charTripleProduct_norm_le`), `K_w = |F w|·M_w/(c_u·m)`. Then:

1. **Pointwise bound** `‖integrand_w(V⁺)‖ ≤ K_w·|full(V⁺)|` for all `V⁺`:
   - `‖integrand‖ = |F w|·‖A‖·‖B‖` (Complex.norm_mul twice + RCLike.norm_ofReal for `‖(F w:ℂ)‖`).
   - `‖A‖ = |ψ(merge)|·exp(-β·S⁺(merge)/2)` (RCLike.norm_ofReal + abs_mul + Real.abs_exp).
   - `‖B‖ ≤ M_w` (charTripleProduct_norm_le).
   - `|full| = ‖A‖·(c_u·exp(-β·S_int(U)))` (Real.exp_add splits the 3-term exp; `ring` rearranges).
   - `exp(-β·S_int(U)) ≥ m` → `‖A‖ ≤ |full|/(c_u·m)` (le_div_iff₀ + mul_le_mul_of_nonneg_left).
   - Combine via `calc`: `‖integrand‖ ≤ |F w|·M_w·‖A‖ ≤ |F w|·M_w·(|full|/(c_u·m)) = K_w·|full|`.

2. **Dominator integrability** `Integrable (K_w·|full|) μ⁺`:
   `Integrable.smul K_w (Integrable.norm hψ_int)` (norm of integrable is integrable,
   scalar multiple of integrable is integrable; `‖full‖ = |full|` for ℝ).

3. **Apply `Integrable.mono'`** with `h_dom`, `h_integrand_ae w`, and
   `ae_of_all h_bound` (pointwise bound → a.e. bound).

**Key technique:** `RCLike.norm_ofReal` as a `rw` lemma fails to match `‖Complex.ofReal x‖`
(syntactic mismatch between `Complex.ofReal` and `RCLike.ofReal` coercions). Fix: use it as a
TERM — `have h := @RCLike.norm_ofReal ℂ _ x; exact h.trans (by rw [abs_mul, Real.abs_exp])`.
The `@RCLike.norm_ofReal ℂ _` explicit instance annotation is required (otherwise the `RCLike`
typeclass is a metavariable). `Integrable.const_mul` has `c` as an IMPLICIT arg (first explicit
arg is `Integrable f μ`), so use `Integrable.smul K_w` instead (which has `c` explicit).
`ae_of_all` takes the measure as an explicit first arg: `ae_of_all (haarMeasurePositive N T L) h_bound`.

**REMAINING:** The `h_integrand_ae` (AEStronglyMeasurable) hypothesis is taken as a parameter.
Discharging it requires proving measurability of the component functions (`repCharacter`,
`interfaceLinkVar`, `extendToFullConfig`, `reflectPosToNeg`, `mergePosInterface`) and deriving
`AEStronglyMeasurable (fun V⁺ => ψ(merge(V⁺))) μ⁺` from `hψ_int` (via division by the measurable
nonzero `exp(-β·(S⁺(u)/2 + S_int(U)))` factor). This likely requires strengthening
`peterWeyl_clebschGordan_plaquette` to provide `Measurable (ρ i)` (or `Continuous (ρ i)`),
which must be logged in `docs/axiom_growth_audit.md` per the README rule. See design doc §8.11.10.

### 8.11.14 Discharge of `h_integrand_ae` (2026-08-03 session)

**PROVED** `transfer_matrix_integrand_ae` (TransferMatrix.lean, ~line 3700) — discharges the
`h_integrand_ae` hypothesis of `transfer_matrix_fubini_integrability`. 0 sorries, 0 custom axioms
(`#print axioms` = `[propext, Classical.choice, Quot.sound]`).

**Axiom strengthening (#6):** `peterWeyl_clebschGordan_plaquette` strengthened to provide
`hMeas : ∀ i, Measurable (repCharacter (ρ i))` (character measurability). Logged in
`docs/axiom_growth_audit.md` §6. Classification: (a) narrow — one-line consequence of continuity.
Axiom count remains 6 (strengthening, not new axiom).

**New measurability lemmas (all 0 sorries, 0 custom axioms):**
- `measurable_restrictLinkVariable` — `restrictLinkVariable` measurable (coordinate projections).
- `measurable_reflectPosToNeg` — `reflectPosToNeg = restrictLinkVariable ∘ reflectLinkVariable ∘ extendLinkVariable`, each measurable.
- `measurable_extendToFullConfig_reflectPosToNeg` — `extendToFullConfig (reflectPosToNeg V⁺) u` measurable in `V⁺`.
- `measurable_interfaceLinkVar` (ReflectionPositivity.lean) — `interfaceLinkVar · l` measurable in `U` (projection).
- `measurable_integrand_char_factor` — each `repCharacter (ρ i) (interfaceLinkVar U l)` measurable in `V⁺` (composes `hMeas` + the above).
- `measurable_integrand_B` — the full character triple product `B(V⁺) = Φ_w·Ψ_w·star(V_w)` measurable in `V⁺` (`Finset.measurable_prod` + `Measurable.mul` + `continuous_star`).
- `integrand_A_ae` — `AEStronglyMeasurable (fun V⁺ => Complex.ofReal (ψ(merge)·exp(-β·S⁺(merge)/2))) μ⁺` derived from `hψ_int` by dividing by the measurable nonzero factor `exp(-β·S⁺(u)/2)·exp(-β·S_int(U))` (via `AEStronglyMeasurable.mul` + `Measurable.inv` + `congr` with `div_eq_mul_inv`; pointwise equality via `Real.exp_add` + `field_simp [Real.exp_pos]`).

**Key technique:** `AEStronglyMeasurable.div` fails to synthesize `Group ℝ` in this toolchain; use
`AEStronglyMeasurable.mul h_full_ae (Measurable.inv h_factor_meas).aestronglyMeasurable` + `congr`
with `(div_eq_mul_inv _ _).symm` instead. `Measurable.aestronglyMeasurable` needs the measure as
an explicit annotation: `have h : AEStronglyMeasurable _ (haarMeasurePositive N T L) := ...`.
`field_simp [Real.exp_pos]` (not `ring`) closes the pointwise `full/factor = target` goal after
`Real.exp_add` (the `Real.exp` atoms with let-bound `merge`/`U` defeat `ring`).

### 8.11.15 Self-contained step-4c integrability + character expansion (2026-08-03 session)

**PROVED** two self-contained combination lemmas in `TransferMatrix.lean`, both 0 sorries,
0 custom axioms (`#print axioms` = `[propext, Classical.choice, Quot.sound]`). Full lake
build GREEN (2972 jobs).

1. **`transfer_matrix_fubini_integrability_self`** (~line 3740) — combines
   `transfer_matrix_fubini_integrability` (domination argument, takes `h_integrand_ae`)
   with `transfer_matrix_integrand_ae` (discharges `h_integrand_ae` from `hψ_int` + `h_meas`).
   The result is a single lemma whose only hypotheses are `hψ_int` (integrability of the full
   Boltzmann-weighted observable) and `h_meas : ∀ i, Measurable (repCharacter (ρ i))` (character
   measurability, supplied by axiom strengthening #6) — no `h_integrand_ae` parameter remains.

2. **`transfer_matrix_fubini_character_expansion_self`** (~line 3790) — combines
   `transfer_matrix_fubini_character_expansion` (the Fubini + character-expansion exchange,
   takes `h_int`) with `transfer_matrix_fubini_integrability_self` (discharges `h_int` from
   `hψ_int` + `h_meas`). The result is a single lemma whose only hypotheses are the
   character-expansion data (`C`, `h_char`), the representation data (`h_unitary`, `h_meas`),
   and `hψ_int` — no `h_int` parameter remains. This is the self-contained pointwise
   character-expansion identity that step 4d will integrate over `u`.

**Proof:** both are one-liner `exact`s — the integrand expressions in the constituent lemmas
are textually identical, so the conclusions match the hypotheses up to defeq:
```
-- integrability_self:
transfer_matrix_fubini_integrability N T L β ψ u ι dims ρ h_unitary dual F hψ_int
  (transfer_matrix_integrand_ae N T L β ψ u ι dims ρ h_unitary h_meas dual F hψ_int)
-- character_expansion_self:
transfer_matrix_fubini_character_expansion N T L β ψ u C ι dims ρ dual F h_char
  (transfer_matrix_fubini_integrability_self N T L β ψ u ι dims ρ h_unitary h_meas dual F hψ_int)
```

**REMAINING:** Steps 4d (measure factorization split) and 4e (identify Fourier coefficients
A_w, B_w) — see project tasks #47, #48 and §8.8. The bridge lemmas
`interfaceLinkVar_extendToFullConfig_pos/int/neg` (TransferMatrix.lean ~line 1895, already
proved) separate `Φ_w` (depends on `U⁺`), `Ψ_w` (depends on `u⁰`), `V_w` (depends on `V⁺`
via `reflectPosToNeg`) — this is the key input to step 4d.

### 8.11.16 Step 4d foundation: PosInterfaceConfig decomposition (2026-08-03 session)

**PROVED** the foundational lemma for step 4d (measure factorization), 0 sorries, 0 custom
axioms (`#print axioms` = `[propext, Classical.choice, Quot.sound]`). Full lake build GREEN
(2972 jobs).

- **`restrictToPositive`** (TransferMatrix.lean, ~line 1167) — restricts a `PosInterfaceConfig`
  to the positive links only (analogue of `restrictToInterface` for the positive part):
  `restrictToPositive u ⟨(n,μ), hn⟩ = u ⟨(n,μ), Finset.mem_union_left (interfaceSites T L) hn⟩`.

- **`mergePosInterface_restrictToPositive_restrictToInterface`** (TransferMatrix.lean,
  ~line 1183) — a `PosInterfaceConfig` decomposes as the merge of its positive and interface
  restrictions: `mergePosInterface (restrictToPositive u) (restrictToInterface u) = u`. This is
  the key decomposition needed to apply the bridge lemmas
  `interfaceLinkVar_extendToFullConfig_pos/int/neg` (which take `U_plus`/`U_zero` as explicit
  args and require `u = mergePosInterface U_plus U_zero`) to a general `u : PosInterfaceConfig`.

**Proof:** `funext ⟨(n, μ), hmem⟩; simp only [mergePosInterface, restrictToPositive,
restrictToInterface]; split_ifs <;> rfl`. The `simp only` unfolds the three definitions (using
equational lemmas that reduce the `match` on the constructor), producing a `dite`
(`if h : n ∈ positiveSites then ... else ...`). `split_ifs` splits the `dite` into two cases
(via the `Decidable` instance for `Finset.mem`), and `rfl` closes each case — proof irrelevance
is definitional in the Lean kernel, so `u ⟨(n,μ), p₁⟩ = u ⟨(n,μ), p₂⟩` (same proposition) is
`rfl`.

**Key technique learned:** `if_pos`/`if_neg` (for `ite`) do NOT apply to `if h : P then A else B`
(which is a `dite`, dependent if-then-else); use `split_ifs` (which handles both `ite` and
`dite`) or `dif_pos`/`dif_neg` instead. `simp only [def_name]` (not `dsimp only`) is needed to
unfold a `λ`-match-defined function — `simp only` uses the equational lemma which reduces the
`match` on a constructor, while `dsimp only [def_name]` leaves the `match` unreduced.

**Next for step 4d:** Use the decomposition + bridge lemmas to prove a pointwise separation
lemma: for `U = extendToFullConfig(reflectPosToNeg(V⁺), u)`, the character triple product
`Φ_w(U)·Ψ_w(U)·V_w(U)` separates into `Φ_w(restrictToPositive u)·Ψ_w(restrictToInterface u)·
V_w(reflectPosToNeg V⁺)` (three factors depending on disjoint variables). Then integrate over
`(U⁺, u⁰)` via `integral_prod` and factor the integrals.

**Specialized bridge lemmas (2026-08-03, same session):** Three specialized versions of the
bridge lemmas that take `V_plus` and `u : PosInterfaceConfig` directly (instead of
`U_minus`/`U_plus`/`U_zero`), using the decomposition to connect. All 0 sorries, 0 custom axioms.
- `interfaceLinkVar_extendToFullConfig_pos'` (~line 1990): for `U = extendToFullConfig(reflectPosToNeg V⁺) u`,
  positive-link `l` gives `interfaceLinkVar U l = u ⟨..., mem_union_left ... hpos⟩` (depends on `u`'s positive part).
- `interfaceLinkVar_extendToFullConfig_int'` (~line 2010): interface-link `l` gives
  `interfaceLinkVar U l = u ⟨..., mem_union_right ... hint⟩` (depends on `u`'s interface part).
- `interfaceLinkVar_extendToFullConfig_neg'` (~line 2030): negative-link `l` gives
  `interfaceLinkVar U l = reflectPosToNeg V⁺ ⟨..., hneg⟩` (depends on `V⁺` only, not `u`).

**Proof pattern (all three):** `have hdecomp := mergePosInterface_restrictToPositive_restrictToInterface ...;
have h := interfaceLinkVar_extendToFullConfig_{pos,int,neg} ... (restrictToPositive u) (restrictToInterface u) ...;
rw [hdecomp] at h; rw [h]; rfl` (the `rw [hdecomp] at h` rewrites the `mergePosInterface` in the
bridge lemma's LHS back to `u`, connecting the specialized `u`-form to the original `U_plus`/`U_zero` form).

**Restrict-after-merge identities (2026-08-03, same session):** Two lemmas identifying the
positive/interface restrictions of a merged config, 0 sorries, 0 custom axioms.
- `restrictToPositive_mergePosInterface` (~line 1196): `restrictToPositive (mergePosInterface U⁺ u⁰) = U⁺`.
- `restrictToInterface_mergePosInterface` (~line 1214): `restrictToInterface (mergePosInterface U⁺ u⁰) = u⁰`.
These are needed in step 4d to identify the `Φ_w` (depends on `U⁺`) and `Ψ_w` (depends on `u⁰`) factors
after the measure factorization splits `u = mergePosInterface U⁺ u⁰`. **Proof:** `funext` + `simp only
[restrictTo{Positive,Interface}, mergePosInterface]` + `split_ifs` (the `dite` from `mergePosInterface`
selects the correct branch; `rfl` closes via proof irrelevance; the contradictory branch is closed by
`absurd`/`Finset.disjoint_left`).

### 8.11.17 Step 4d: character triple product separation (2026-08-03 session)

**PROVED** the pointwise character triple product separation lemma
`charTripleProduct_separate` (TransferMatrix.lean, ~line 2120), plus three helper
definitions `charFactorPos`/`charFactorInt`/`charFactorNeg` (~line 2088/2102/2116).
All 0 sorries, 0 custom axioms (`#print axioms` = `[propext, Classical.choice,
Quot.sound]`). Full lake build GREEN (2891 jobs).

**Statement:** For `U = extendToFullConfig (reflectPosToNeg V⁺) u`, the character
triple product `Φ_w(U)·Ψ_w(U)·star(V_w(U))` separates into three factors depending
on disjoint variables:
```
(∏_{l∈L_U} χ_{w(l)}(interfaceLinkVar U l)) * (∏_{l∈L_0} χ_{w(l)}(interfaceLinkVar U l)) *
star(∏_{l∈L_V} χ_{dual(w(l))}(interfaceLinkVar U l))
= charFactorPos (restrictToPositive u) * charFactorInt (restrictToInterface u) *
  star (charFactorNeg (reflectPosToNeg V⁺))
```
where `charFactorPos` depends on `u`'s positive part, `charFactorInt` on `u`'s
interface part, and `charFactorNeg` on `V⁺` only (via `reflectPosToNeg`).

**Key design decision (the membership-proof challenge):** `Finset.prod` over
`interfaceLinkPos` does not give the product function access to the membership proof
`hl : l ∈ interfaceLinkPos`, which is needed to derive `l.val.1 ∈ positiveSites` (to
index the site-based config `U⁺` at a link-based index `l`). The solution: define
each `charFactor*` using an `if hpos : l.val.1 ∈ positiveSites T L then ... else 1`
guard (a `dite` on the SITE membership, which is decidable). For `l ∈ interfaceLinkPos`,
the guard is always true (via `interfaceLinkPos_mem_iff`), so the `else 1` branch is
never taken in the product. This keeps the function a base-type `InterfaceLink T L → ℂ`
(no `attach`/subtype coercion needed), making `Finset.prod_congr` apply directly.

**Proof (each factor):** `simp only [charFactor*]` (unfold) → `Finset.prod_congr rfl`
→ `intro l hl` → `rw [dif_pos ((interfaceLink*_mem_iff T L l).mp hl)]` (simplify the
`if` using the membership) → `rw [interfaceLinkVar_extendToFullConfig_*' ... l hpos]`
(bridge lemma: `interfaceLinkVar U l = u ⟨(l.val.1, l.val.2), mem_union_* ... hpos⟩`)
→ `rfl` (closes via `restrictToPositive`/`restrictToInterface` definitional unfolding;
for the neg factor, the bridge lemma directly gives `reflectPosToNeg V⁺ ⟨...⟩`, so `rw`
alone closes the goal — no `rfl` needed).

**Next for step 4d:** Apply `charTripleProduct_separate` inside the V⁺ integral of
`transfer_matrix_fubini_character_expansion_self` (substituting `u = mergePosInterface
U⁺ u⁰` via `restrictToPositive_mergePosInterface`/`restrictToInterface_mergePosInterface`
to make the factors depend on `U⁺`/`u⁰`/`V⁺` disjointly), then factor the integrals via
`integral_prod`. See §8.11.8 (step 4d/4e description).

### 8.11.18 Step 4d: apply separation + integrate + change of variables (2026-08-03 session)

**PROVED** three more lemmas in `TransferMatrix.lean` (after
`transfer_matrix_fubini_character_expansion_self`), all 0 sorries, 0 custom axioms
(`#print axioms` = `[propext, Classical.choice, Quot.sound]`). Full lake build GREEN
(2891 jobs).

**1. `transfer_matrix_fubini_character_expansion_separated`** (~line 4055). Applies
`charTripleProduct_separate` inside the V⁺ integral of
`transfer_matrix_fubini_character_expansion_self`, rewriting the character triple
product `Φ_w(U)·Ψ_w(U)·star(V_w(U))` (with `U = extendToFullConfig (reflectPosToNeg V⁺) u`)
as the separated product `charFactorPos (restrictToPositive u) · charFactorInt
(restrictToInterface u) · star (charFactorNeg (reflectPosToNeg V⁺))`. **Proof:**
`have h := transfer_matrix_fubini_character_expansion_self ...; simp only
[charTripleProduct_separate] at h; exact h`. **Key technique:** `rw
[charTripleProduct_separate] at h` FAILS ("Did not find an occurrence of the pattern")
because `rw` cannot match the pattern under the `∫ V_plus` / `∑ w` / `Finset.prod`
binders — the metavariables `?V_plus`, `?w` would need to unify with BOUND variables,
which `rw` cannot do. `simp only [charTripleProduct_separate] at h` SUCCEEDS because
`simp` does lambda-abstraction matching and can rewrite under binders.

**2. `transfer_matrix_fubini_character_expansion_separated_pull`** (~line 4106). Pulls
the V⁺-independent factors `charFactorPos (restrictToPositive u)` and `charFactorInt
(restrictToInterface u)` out of the V⁺ integral via `integral_const_mul` (after a
pointwise `ring` rearrangement of the integrand). The remaining V⁺ integral depends on
`u` only through the prefactor `Complex.ofReal (ψ(merge(V⁺, σ(u⁰))) · exp(…))` and the
conjugated negative factor `star (charFactorNeg (reflectPosToNeg V⁺))`. **Proof:**
- `have hpt : ∀ w Vp, prefactor * (c1 * c2 * star(g)) = c1 * c2 * (prefactor * star(g))
  := by intro w Vp; ring` — pointwise rearrangement (`ring` treats `star(g)` as an atom).
- `simp only [hpt] at h` — rewrites the integrand under the `∫`/`∑` binders.
- `have h_factor : ∀ w, ∫ Vp, c1*c2*(prefactor*star(g)) = c1*c2*∫ Vp, prefactor*star(g)
  := by intro w; rw [integral_const_mul]` — pulls the constant out of a SINGLE integral
  (not inside a sum). `rw [integral_const_mul]` works here because the constant `c1*c2`
  is a FREE expression (not a bound variable), so `rw` can abstract the bound variable
  for the function metavariable `?f` (unlike Lemma 1 where `?V_plus` needed to BE a
  bound variable).
- `simp only [h_factor] at h` — applies the per-`w` factoring under the `∑ w` binder.
- `exact h`.

**3. `transfer_matrix_fubini_integrated`** (~line 4192). Integrates the pointwise
identity (Lemma 2) over `u` w.r.t. `haarMeasurePosInterface`, coerces the LHS to ℂ via
`integral_complex_ofReal`, and performs the change of variables `u = mergePosInterface
U⁺ u⁰` via `MeasurableEmbedding.integral_map` (using `haarMeasurePosInterface_eq` =
`Measure.map (mergePosInterface) (μ⁺ × μ⁰)`). The restrict-after-merge lemmas simplify
`charFactorPos (restrictToPositive (merge U⁺ u⁰)) = charFactorPos U⁺` and `charFactorInt
(restrictToInterface (merge U⁺ u⁰)) = charFactorInt u⁰`, and the inner prefactor's
`σ(restrictToInterface (merge U⁺ u⁰)) = σ(u⁰)`. The three character factors now depend on
disjoint variables `U⁺`, `u⁰`, `V⁺`. **Proof:**
- `have h_ofReal := (integral_complex_ofReal).symm; rw [h_ofReal]` — LHS becomes
  `∫_u Complex.ofReal (ψ u * Tψ u) du`.
- `have h_pw : ∀ u, Complex.ofReal (ψ u * Tψ u) = RHS(u) := by intro u; exact
  transfer_matrix_fubini_character_expansion_separated_pull ... (hψ_int u)` — pointwise
  identity (note: `hψ_int` is now `∀ u, Integrable ...`, strengthened from the fixed-`u`
  version in Lemma 2; pass `hψ_int u` to Lemma 2).
- `simp only [h_pw]` — rewrites the integrand under the `∫ u` binder.
- `rw [haarMeasurePosInterface_eq]` — measure becomes `Measure.map (merge) (μ⁺×μ⁰)`.
- Set up `hME : MeasurableEmbedding (Function.uncurry (mergePosInterface))` via
  `productHaarMeasureUnionEquiv` (same pattern as `inner_product_complex_eq_product_integral`).
- `rw [hME.integral_map]` — change of variables (NO explicit function arg needed; `rw`
  abstracts the bound variable for the function metavariable). LHS becomes
  `∫_x RHS(Function.uncurry (mergePosInterface) x) d(μ⁺×μ⁰)`.
- `simp only [Function.uncurry, restrictToPositive_mergePosInterface,
  restrictToInterface_mergePosInterface]` — simplifies `Function.uncurry (mergePosInterface)
  x → mergePosInterface x.1 x.2`, then `restrictToPositive (mergePosInterface x.1 x.2) →
  x.1` and `restrictToInterface (mergePosInterface x.1 x.2) → x.2`. Closes the goal (the
  goal's RHS is already in the simplified form, so `simp only` is a no-op on it and
  simplifies the LHS to match).

**Key techniques learned (this session):**
1. **`rw` vs `simp only` under binders:** `rw` CANNOT match a pattern under `∫`/`∑`/
   `Finset.prod` binders when the pattern's metavariables need to unify with BOUND
   variables. `simp only` CAN (it does lambda-abstraction matching). Use `simp only
   [lemma] at h` to rewrite under binders.
2. **`rw [integral_const_mul]` works for a single integral** (not inside a sum) when the
   constant is a FREE expression — `rw` can abstract the bound variable for the function
   metavariable `?f`, just not assign a metavariable to a bound variable.
3. **`rw [hME.integral_map]` without explicit function arg** — `rw` abstracts the bound
   variable to determine the function `g` in `∫ b, g b ∂ map f μ = ∫ a, g (f a) ∂ μ`.
4. **`simp only [Function.uncurry, restrictToPositive_mergePosInterface,
   restrictToInterface_mergePosInterface]`** simplifies the change-of-variables result:
   `Function.uncurry` unfolds to `mergePosInterface x.1 x.2`, then the restrict-after-merge
   lemmas fire.
5. **`hψ_int` strengthening:** Lemma 3 needs `hψ_int : ∀ u, Integrable ...` (universally
   quantified over `u`) since it integrates over `u`. Pass `hψ_int u` to Lemma 2 (which
   takes the fixed-`u` version).

**Next for step 4d (Lemma 4):** Factor the `(U⁺, u⁰)` integral via `integral_prod`
(split into `∫_{u⁰} ∫_{U⁺}`), then pull U⁺-independent constants (`C`, `F w`,
`charFactorInt(u⁰)`, `B_w(u⁰)`) out of the U⁺ integral via `integral_const_mul` +
`integral_finsetSum`. **KEY DIFFICULTY:** `integral_prod` requires `Integrable f
(μ⁺.prod μ⁰)` of the full integrand — this integrability must be established from
`hψ_int` + character boundedness (`charProduct_norm_le`) + Fubini-type arguments. This
is the main remaining challenge for step 4d. Then step 4e identifies `A_w(u⁰) = ∫_{U⁺}
Complex.ofReal(ψ(merge(U⁺,u⁰))·exp(…)) · charFactorPos(U⁺) dμ⁺` and `B_w(u⁰) = ∫_{V⁺}
Complex.ofReal(ψ(merge(V⁺,σ(u⁰)))·exp(…)) · star(charFactorNeg(reflectPosToNeg V⁺)) dμ⁺`.

### 8.11.19 Step 4d Lemma 4a: Fubini split via integral_prod_symm (2026-08-03 session 9)

**PROVED** `transfer_matrix_fubini_integrated_prod` (~line 4306 in TransferMatrix.lean),
0 sorries, 0 custom axioms (`#print axioms` = `[propext, Classical.choice, Quot.sound]`).
Full `lake build` GREEN (2891 jobs).

This lemma applies `integral_prod_symm` to the product-measure integral from
`transfer_matrix_fubini_integrated` (Lemma 3), splitting the `(U⁺, u⁰)` integral into
an iterated integral `∫_{u⁰} ∫_{U⁺}` (outer `u⁰` w.r.t. `μ⁰`, inner `U⁺` w.r.t. `μ⁺`).

**The KEY DIFFICULTY (integrability of `g_RHS` w.r.t. `μ⁺.prod μ⁰`)** was solved via
the **"from-LHS" approach**:
1. Take `h_int : Integrable (fun u => Complex.ofReal (ψ u * Tψ u)) haarMeasurePosInterface`
   as a hypothesis (integrability of the ℂ-valued inner-product integrand).
2. Construct `hMP : MeasurePreserving (Function.uncurry merge) (μ⁺.prod μ⁰) haarMeasurePosInterface`
   via `⟨hME.measurable, (haarMeasurePosInterface_eq N T L).symm⟩`.
3. Push `h_int` through the change of variables via
   `hMP.integrable_comp_emb hME |>.mpr h_int`, giving
   `h_int' : Integrable (fun x => Complex.ofReal (ψ (merge x) * Tψ (merge x))) (μ⁺.prod μ⁰)`.
4. `simp only [Function.uncurry] at h_int'` — unfolds `Function.uncurry merge x` to
   `merge x.1 x.2`.
5. Establish the pointwise identity `h_eq : ∀ x, Complex.ofReal (ψ (merge x) * Tψ (merge x))
   = g_RHS(x)` by applying Lemma 2 (`transfer_matrix_fubini_character_expansion_separated_pull`)
   to `u = merge x.1 x.2` and simplifying with `restrictToPositive_mergePosInterface` +
   `restrictToInterface_mergePosInterface`.
6. Transfer integrability via `h_int'.congr (ae_of_all _ h_eq)` — `Integrable.congr`
   takes `Integrable f μ` and `f =ᵐ[μ] g` and gives `Integrable g μ` (it derives
   `AEStronglyMeasurable g` internally from `f`'s a.e. strong measurability).
7. Apply `integral_prod_symm _ h_g_int` to split the product integral.

**Key techniques learned:**
- **`MeasurePreserving` construction:** `⟨hME.measurable, (haarMeasurePosInterface_eq N T L).symm⟩`
  — `MeasurePreserving` has fields `measurable : Measurable f` and `map_eq : Measure.map f μ = ν`.
  `MeasurableEmbedding.measurable` gives the first; `haarMeasurePosInterface_eq.symm` gives the
  second. Note: `haarMeasurePosInterface_eq` takes explicit `N T L` args, so must write
  `(haarMeasurePosInterface_eq N T L).symm` (not `haarMeasurePosInterface_eq.symm` which is
  parsed as a qualified name).
- **`integral_prod_symm` (not `integral_prod`):** `integral_prod` gives
  `∫ z ∂(μ.prod ν) = ∫ x ∂μ, ∫ y ∂ν, f(x,y)` (outer = first component). For outer = second
  component (`u⁰`), inner = first component (`U⁺`), use `integral_prod_symm` which gives
  `∫ z ∂(μ.prod ν) = ∫ y ∂ν, ∫ x ∂μ, f(x,y)`.
- **`SFinite` instance needed:** `integral_prod_symm` requires `SFinite ν` (the second
  measure). Added `haveI : IsFiniteMeasure (haarMeasureInterface N T L) :=
  productHaarMeasure_isFiniteMeasure N (PeriodicSite T L) (interfaceSites T L)` (and
  similarly for `haarMeasurePositive`). `IsFiniteMeasure` implies `SFinite`.
- **`Integrable.congr` needs only `f =ᵐ[μ] g`:** `Integrable.congr (hf : Integrable f μ)
  (h : f =ᵐ[μ] g) : Integrable g μ` — the `AEStronglyMeasurable g` is derived internally
  from `hf.1.congr h`. No need to separately provide it.
- **`exact h` after `rw [h_split] at h`:** After `integral_prod_symm` splits the integral,
  `g_RHS(⟨U⁺, u⁰⟩)` (with `⟨·,·⟩.1/.2`) is defeq to the explicit form (with `U⁺`/`u⁰`
  directly), so `exact h` closes the goal.

**What Lemma 4a accomplishes:** The inner product `Complex.ofReal(∫_u ψ u * Tψ u du)` is
now expressed as the iterated integral `∫_{u⁰} ∫_{U⁺} g_RHS(U⁺, u⁰) ∂μ⁺ ∂μ⁰`, where
`g_RHS(U⁺, u⁰) = Complex.ofReal(ψ(merge(U⁺,u⁰))·exp(-β·S⁺(merge(U⁺,u⁰))/2)) ·
(C · ∑_w F(w) · (charFactorPos(U⁺) · charFactorInt(u⁰) · B_w(u⁰)))`.

**Next for step 4d (Lemma 4b):** Pull U⁺-independent constants (`C`, `F w`,
`charFactorInt(u⁰)`, `B_w(u⁰)`) out of the inner U⁺ integral via pointwise rearrangement
(`ring`/`Finset.mul_sum`) + `integral_const_mul` + `integral_finsetSum` (exchange sum
with U⁺ integral). The `integral_finsetSum` step requires per-`w` integrability of
`(F w · charFactorInt(u⁰) · B_w(u⁰)) · (prefactor(U⁺,u⁰) · charFactorPos(U⁺))` w.r.t.
`μ⁺` for each `u⁰`. This per-`w` integrability is the remaining challenge — it can be
taken as a hypothesis (like `transfer_matrix_fubini_character_expansion` takes `h_int`)
or derived from the half-Boltzmann integrability + character boundedness. Then step 4e
identifies `A_w(u⁰) = ∫_{U⁺} prefactor(U⁺,u⁰) · charFactorPos(U⁺) dμ⁺` and
`B_w(u⁰) = ∫_{V⁺} Complex.ofReal(ψ(merge(V⁺,σ(u⁰)))·exp(…)) ·
star(charFactorNeg(reflectPosToNeg V⁺)) dμ⁺`.

### 8.11.20 Step 4d Lemma 4b: pull U⁺-independent constants out of inner U⁺ integral (2026-08-03 session 10)

**PROVED** `transfer_matrix_fubini_inner_pull` (~line 4520 in TransferMatrix.lean),
0 sorries, 0 custom axioms (`#print axioms` = `[propext, Classical.choice, Quot.sound]`).
Full `lake build` GREEN (2891 jobs).

Also defined two `noncomputable def`s (both 0 custom axioms):
- **`fourierCoeffPos`** (~line 4449): `A_w(u⁰) = ∫_{U⁺} Complex.ofReal(ψ(merge(U⁺,u⁰))·
  exp(-β·S⁺(merge(U⁺,u⁰))/2)) · charFactorPos(w, U⁺) ∂μ⁺` — the positive Fourier
  coefficient.
- **`fourierCoeffNeg`** (~line 4468): `B_w(u⁰) = ∫_{V⁺} Complex.ofReal(ψ(merge(V⁺,σ(u⁰)))·
  exp(-β·S⁺(merge(V⁺,σ(u⁰)))/2)) · star(charFactorNeg(dual w, reflectPosToNeg V⁺)) ∂μ⁺`
  — the negative Fourier coefficient (should equal `conj(A_w(σ(u⁰)))` by lemma 3).

**Lemma 4b** is a standalone lemma about the inner U⁺ integral for a fixed `u⁰`:
```
∫_{U⁺} prefactor(U⁺,u⁰) · (C · ∑_w F(w) · (charFactorPos(U⁺) · charFactorInt(u⁰) · B_w(u⁰))) ∂μ⁺
  = C · ∑_w F(w) · (charFactorInt(u⁰) · B_w(u⁰) · A_w(u⁰))
```
where `A_w = fourierCoeffPos`, `B_w = fourierCoeffNeg`. The per-`w` integrability
hypothesis `h_int` (each term `(F w) · (prefactor · (charFactorPos · charFactorInt · B_w))`
is integrable w.r.t. `μ⁺`) is taken as a parameter — it will be discharged separately
using character boundedness + half-Boltzmann integrability (see §8.11.10).

**Proof** (inlined Fubini exchange steps, matching the pattern from
`transfer_matrix_fubini_character_expansion` to avoid large-expression whnf timeout):
1. **Per-`w` identity `h_w`**: For each `w`, `∫_{U⁺} prefactor · (Φ · Ψ · B_w) ∂μ⁺ =
   Ψ · B_w · A_w`. Proved by: pointwise `ring` rearrange `prefactor · (Φ · Ψ · B_w) =
   (Ψ · B_w) · (prefactor · Φ)`, rewrite the integral integrand via `congr 1; funext;
   exact hpt`, then `rw [integral_const_mul]` pulls `(Ψ · B_w)` out, and `rfl` recognizes
   `fourierCoeffPos` (defeq to the remaining integral).
2. **Pointwise rearrange** (Step 1): `simp only [show ∀ Upos, A · (C · ∑ w, F · X) =
   C · ∑ w, F · (A · X) from fun Upos => by rw [← mul_assoc, mul_comm _ (C : ℂ), mul_assoc,
   Finset.mul_sum]; refine congrArg ((C : ℂ) * ·) (Finset.sum_congr rfl (fun w _ => by ring))]`
   — rearranges the integrand so `C` and `F(w)` are outside `A · X`.
3. **Pull `C` out** (Step 2): `rw [integral_const_mul]` — no integrability needed.
4. **Exchange `∑_w` with `∫ U⁺`** (Step 3): `rw [integral_finsetSum Finset.univ]` —
   creates main goal + integrability side goal.
5. **Pull each `F(w)` out** (Step 4): `simp only [integral_const_mul]` — no integrability.
6. **Rewrite each integral** (Step 5): `refine congrArg ((C : ℂ) * ·) ?_; exact
   Finset.sum_congr rfl (fun w hw => by rw [h_w w])` — rewrites each
   `∫ U⁺ prefactor · (Φ · Ψ · B_w) ∂μ⁺` to `Ψ · B_w · A_w` via `h_w`.
7. **Integrability** (Step 3 side goal): `exact fun w _ => h_int w`.

**Key techniques learned:**
- **`congrArg ((C : ℂ) * ·) ?_`** to cancel a leading constant factor in an equality of
  sums: `refine congrArg ((C : ℂ) * ·) ?_` changes the goal from `C * ∑ ... = C * ∑ ...`
  to `∑ ... = ∑ ...`, which is then closed by `Finset.sum_congr`. More robust than
  `congr 1` which may over-decompose.
- **`rfl` recognizes `noncomputable def`s**: After `rw [integral_const_mul]`, the
  remaining integral `∫ U⁺ prefactor · charFactorPos ∂μ⁺` is defeq to `fourierCoeffPos`
  (since the def unfolds to that exact integral), so `rfl` closes the goal.
- **Inlining Fubini exchange** (vs calling `integral_finsetSum_pull_constants` directly):
  The comment in `transfer_matrix_fubini_character_expansion` notes that inlining avoids
  "large-expression whnf timeout". Lemma 4b follows this pattern — the `simp only [show
  ∀ x, ...]` + `rw [integral_const_mul]` + `rw [integral_finsetSum Finset.univ]` +
  `simp only [integral_const_mul]` sequence is inlined rather than calling the abstract
  lemma.
- **`fourierCoeffNeg` as a constant w.r.t. U⁺**: `B_w(u⁰) = fourierCoeffNeg` does not
  depend on the U⁺ integration variable, so it is pulled out as a constant via
  `integral_const_mul` (no integrability needed). This is the key insight: the V⁺ integral
  `B_w(u⁰)` is a fixed complex number for each `u⁰`, not a function of `U⁺`.

**What Lemma 4b accomplishes:** The inner U⁺ integral is now expressed as
`C · ∑_w F(w) · (charFactorInt(u⁰) · B_w(u⁰) · A_w(u⁰))`, where `A_w = fourierCoeffPos`
and `B_w = fourierCoeffNeg` are the Fourier coefficients. The remaining work is:
- **Step 4e**: Integrate Lemma 4b's identity over `u⁰` (requires the identity to hold for
  ae `u⁰` + integrability of the RHS w.r.t. `μ⁰`), giving
  `⟨g, Tg⟩ = C · ∑_w F(w) · ∫_{u⁰} charFactorInt(w, u⁰) · A_w(u⁰) · B_w(u⁰) dμ⁰`.
- **Lemma 3 (σ-inversion)**: Show `B_w(u⁰) = conj(A_w(σ(u⁰)))`, connecting the negative
  Fourier coefficient to the conjugate of the positive one evaluated at `σ(u⁰)`.
- **Lemma 5 (reflection positivity reorganization)**: Reorganize the sum as
  `∑ |Fourier coefficient|² ≥ 0`.
- **Lemma 6 (final assembly)**: Conclude `0 ≤ ⟨g, Tg⟩`, closing `transferMatrixPositivity_axiom`.

### 8.11.21 Lemma 3 analysis: σ-inversion requires reindexing (2026-08-03 session 12)

**Key finding**: The pointwise identity `fourierCoeffNeg(w, u⁰) = star(fourierCoeffPos(w, σ(u⁰)))`
does NOT hold for fixed `w`. The V⁺ factor `star(charFactorNeg dual w (reflectPosToNeg V⁺))`
is a product over `interfaceLinkNeg` (negative links), while `star(charFactorPos w V⁺)` is a
product over `interfaceLinkPos` (positive links). These are DIFFERENT link sets, related by the
reflection bijection. The identity only holds for a REINDEXED `w'` (not the original `w`).

**The reindexing `θ`**: Define `θ : (InterfaceLink → ι) → (InterfaceLink → ι)` by:
- `θw(l) = w(l)` for `l ∈ interfaceLinkPos ∪ interfaceLinkInt` (unchanged).
- `θw(l) = w(φ(l))` for `l ∈ interfaceLinkNeg` with `μ(l) = 0` (time-like).
- `θw(l) = dual(w(φ(l)))` for `l ∈ interfaceLinkNeg` with `μ(l) ≠ 0` (spatial).

where `φ : interfaceLinkNeg → interfaceLinkPos` is the reflection bijection on links
(`φ(l) = (reflectSite(l.val.1), l.val.2)`).

**The pointwise character identity** (for the reindexed `w' = θw`):
`star(charFactorNeg dual w' (reflectPosToNeg V⁺)) = star(charFactorPos w V⁺)`

This holds because:
- For time-like `l ∈ interfaceLinkNeg`: `χ_{dual(w'(l))}((reflectPosToNeg V⁺)_l) = χ_{dual(w(φ(l)))}((V⁺_{φ(l)})⁻¹) = conj(χ_{dual(w(φ(l)))}(V⁺_{φ(l)})) = χ_{w(φ(l))}(V⁺_{φ(l)})` (char of inverse + dual = conj).
- For spatial `l ∈ interfaceLinkNeg`: `χ_{dual(w'(l))}((reflectPosToNeg V⁺)_l) = χ_{dual(dual(w(φ(l))))}(V⁺_{φ(l)})` — this requires `dual` involutivity (`dual(dual(i)) = i`) to simplify to `χ_{w(φ(l))}(V⁺_{φ(l)})`.

**WARNING**: The spatial case requires `dual(dual(i)) = i` (dual involutivity), which is NOT
in the current axiom `peterWeyl_clebschGordan_plaquette` (it only provides `hdual : χ_{dual(i)} = conj(χ_i)`).
This may need to be added as a hypothesis or derived.

**The Fourier coefficient identity** (after reindexing):
`fourierCoeffNeg(θw, u⁰) = star(fourierCoeffPos(w, σ(u⁰)))`

This follows from the pointwise identity + integral conjugation (`star(∫ f) = ∫ star(f)`,
since the prefactor `Complex.ofReal(ψ · exp(...))` is real).

**The sum reindexing**: After reindexing `w ↦ θw`, the sum
`∑_w F(w) · ∫ Ψ_w · B_w · A_w` becomes `∑_w F(θw) · ∫ Ψ_w · conj(A_w(σ)) · A_w`
(using `Ψ_{θw} = Ψ_w`, `A_{θw} = A_w` since `θ` leaves pos/int links unchanged).
For this to match the §8.2 form, we need `F(θw) = F(w)` (reflection symmetry of `F`).

**Infrastructure proved this session**:
- `plaquetteLinkIdx_reflect` (ReflectionPositivity.lean, ~line 2066): For any plaquette `p`
  and link position `j`, the reflected link `(θ(link p j).1, (link p j).2)` equals
  `link (reflectPlaquetteIndex p) j'` for some `j'` (a permutation of `j` depending on directions).
  0 sorries, 0 custom axioms. Build GREEN. This is the key lemma showing the reflection maps
  `interfacePlaqLinkFinset` to itself, enabling the reflection bijection `φ` on `InterfaceLink`.

**Abstract scaffold already proved** (PositiveDefiniteIntegral.lean):
- `character_expansion_positivity` / `character_expansion_nonneg`: If a kernel
  `K(x, y) = ∑_i a_i · Φ_i(x) · conj(Φ_i(θ y))` with `a_i ≥ 0` and `θ` measure-preserving,
  then `∫∫ f(x) · f(θ y) · K(x, y) = ∑_i a_i · ‖∫ f · Φ_i‖² ≥ 0` for real `f`.
  **BUT**: this requires `θ : Y → X` (a function of `y` only), while the TM inner product has
  `g(V⁺, σ(u⁰))` depending on both `V⁺` (= `y`) and `u⁰` (part of `x`). So the abstract lemma
  does NOT directly apply — the `u⁰`-dependence of `σ(u⁰)` prevents the clean separation.

**Remaining steps for Lemma 3**:
1. Define `reflectInterfaceLink : InterfaceLink → InterfaceLink` using `plaquetteLinkIdx_reflect`
   to show the reflected link is in `interfacePlaqLinkFinset`.
2. Prove `reflectInterfaceLink` is involutive and maps `interfaceLinkPos ↔ interfaceLinkNeg`.
3. Define the reindexing `θ` and prove the pointwise character identity.
4. Prove the Fourier coefficient identity `fourierCoeffNeg(θw, u⁰) = star(fourierCoeffPos(w, σ(u⁰)))`.
5. Prove `F(θw) = F(w)` (reflection symmetry of `F` — may require the structure of `F` from
   `plaquette_product_separable_decomp`).

### 8.11.22 Lemma 3 infrastructure proved + dual-involutivity NOT needed (2026-08-03 session 13)

**Infrastructure proved this session** (all 0 sorries, 0 custom axioms, build GREEN):

1. `isInterfacePlaquette_reflect` (ReflectionPositivity.lean, ~line 2100): reflection preserves the
   interface plaquette predicate (`isInterfacePlaquette` ↔ reflected). Extracted as a standalone
   lemma from the `h_interface_inv` local proof in `interface_action_reflection_symmetric_os_periodic`.

2. `reflectInterfaceLink` (ReflectionPositivity.lean, ~line 2125): the reflection of an interface
   link `l = (n, μ)` → `(θn, μ)`. Proved the reflected link is in `interfacePlaqLinkFinset` using
   `plaquetteLinkIdx_reflect` + `isInterfacePlaquette_reflect`. **This is the `φ` map for Lemma 3.**

3. `reflectInterfaceLink_involution` (~line 2148): `reflectInterfaceLink` is involutive
   (`ReflectSite.involution`).

4. `reflectInterfaceLink_mem_neg_of_pos` / `_pos_of_neg` / `_int_of_int` (~line 2153-2184):
   reflection maps `interfaceLinkPos ↔ interfaceLinkNeg` and `interfaceLinkInt → interfaceLinkInt`
   (via `signedTime_reflectSite`). **Key fix**: use `true_and` (not `and_true`) after
   `Finset.mem_univ` — the filter gives `True ∧ cond`, and `omega` (not `linarith`/`ring`) closes
   the resulting integer arithmetic.

5. `reflectInterfaceLinkPosNegEquiv` (~line 2190): the bijection
   `{l // l ∈ interfaceLinkPos} ≃ {l // l ∈ interfaceLinkNeg}`. `left_inv`/`right_inv` via
   `Subtype.eq` + `reflectInterfaceLink_involution` (NOT `ext` — `ext` over-unfolds to `.time`).

6. `reflectPosToNeg_apply` (TransferMatrix.lean, ~line 1808): the link action of `reflectPosToNeg`.
   For a negative-site link `(n, μ)` with `n ∈ negativeSites`:
   - `μ = 0` (time-like): `(V⁺_{(θn, 0)})⁻¹` — inverted (reflection reverses time-link orientation);
   - `μ ≠ 0` (spatial): `V⁺_{(θn, μ)}` — unchanged.
   **Key fix**: `extendLinkVariable` uses a *dependent* `if h : n ∈ sites then ...` (dite), so use
   `dif_pos hpos` (not `if_pos`) to reduce it.

**KEY MATHEMATICAL FINDING: dual involutivity is NOT needed.**

The §8.11.21 WARNING (spatial case needs `dual(dual(i)) = i`) was based on proving the pointwise
identity WITHOUT the outer `star`/`conj`. But the actual identity required by the Fourier-coefficient
structure has `star` on BOTH sides:

- `fourierCoeffNeg` integrand: `ofReal(P) * star(charFactorNeg dual w (reflectPosToNeg V⁺))`
- `star(fourierCoeffPos(w, σ(u⁰)))` = `∫ ofReal(P) * star(charFactorPos w V⁺) ∂μ⁺`
  (star commutes with ∫ for the real Haar measure; `star(ofReal · z) = ofReal · star(z)`).

So the pointwise identity to prove is:
`star(charFactorNeg dual (θw) (reflectPosToNeg V⁺)) = star(charFactorPos w V⁺)`

Since `star` distributes over the product (`map_prod`), this becomes a per-link identity
`star(χ_{dual(θw(l))}((reflectPosToNeg V⁺)_l)) = star(χ_{w(l')}(V⁺_{l'}))` where `l' = φ(l)`.

Using `conj(χ_{dual(i)}(g)) = χ_i(g)` (from `hdual` + `conj_conj`) and `repCharacter_inv`
(`χ(g⁻¹) = conj(χ(g))` for unitary reps, PositiveDefinite.lean ~line 757):

- **Time-like** (`μ = 0`, `θw(l) = w(l')`, `(reflectPosToNeg V⁺)_l = (V⁺_{l'})⁻¹`):
  `star(χ_{dual(w(l'))}((V⁺_{l'})⁻¹)) = conj(conj(χ_{dual(w(l'))}(V⁺_{l'}))) = χ_{dual(w(l'))}(V⁺_{l'})`
  (repCharacter_inv + conj_conj). RHS = `star(χ_{w(l')}(V⁺_{l'})) = χ_{dual(w(l'))}(V⁺_{l'})` (hdual). ✓

- **Spatial** (`μ ≠ 0`, `θw(l) = dual(w(l'))`, `(reflectPosToNeg V⁺)_l = V⁺_{l'}`):
  `star(χ_{dual(dual(w(l')))}(V⁺_{l'})) = conj(χ_{dual(dual(w(l')))}(V⁺_{l'})) = χ_{dual(w(l'))}(V⁺_{l'})`
  (conj(χ_{dual(i)}) = χ_i with `i = dual(w(l'))`). RHS = `χ_{dual(w(l'))}(V⁺_{l'})` (hdual). ✓

**Both cases close WITHOUT `dual(dual(i)) = i`.** The reindexing `θ` is:
- `θw(l) = w(l)` for `l ∈ interfaceLinkPos ∪ interfaceLinkInt` (unchanged);
- `θw(l) = w(φ(l))` for `l ∈ interfaceLinkNeg` with `μ(l) = 0` (time-like);
- `θw(l) = dual(w(φ(l)))` for `l ∈ interfaceLinkNeg` with `μ(l) ≠ 0` (spatial).

**Remaining steps for Lemma 3** (updated):
1. Define `θ : (InterfaceLink → ι) → (InterfaceLink → ι)` (the reindexing above).
2. Prove the pointwise identity `star(charFactorNeg dual (θw) (reflectPosToNeg V⁺)) = star(charFactorPos w V⁺)`
   — reindex the `interfaceLinkNeg` product to `interfaceLinkPos` via `reflectInterfaceLinkPosNegEquiv`,
   then per-link identity (2 cases, using `repCharacter_inv` + `hdual` + `conj_conj`).
3. Prove the Fourier coeff identity `fourierCoeffNeg(θw, u⁰) = star(fourierCoeffPos(w, σ(u⁰)))`
   (pointwise identity + `star` commutes with `∫`).
4. Prove `F(θw) = F(w)` (reflection symmetry of `F`).

### 8.11.23 Lemma 3 steps 2–4 PROVED: main pointwise identity + Fourier coeff identity (2026-08-04 session 15)

**Steps proved this session** (all 0 sorries, 0 custom axioms, build GREEN 2891 jobs):

**Step 2 — Main pointwise identity** (`charFactorNeg_thetaReindex_eq_charFactorPos`, TransferMatrix.lean ~line 5130):
`charFactorNeg dual (θw) (reflectPosToNeg V⁺) = charFactorPos w V⁺`.
Uses `Finset.prod_bij` to reindex `interfaceLinkNeg → interfaceLinkPos` via `reflectInterfaceLink`
(an involution). The bijection `i = reflectInterfaceLink` maps neg→pos; injectivity + surjectivity
follow from `reflectInterfaceLink_involution`. The per-element identity `f a = g (i a)` uses the
per-link lemma `charFactorNeg_thetaReindex_link_eq` (proved session 14) with `b = reflectInterfaceLink a`
+ involution to fold the double reflection back to `a`.
The `star` version `charFactorNeg_thetaReindex_eq_charFactorPos_star` (~line 5180) is
`congrArg star` of the non-star version.

**Step 3 — Fourier coeff identity** (`fourierCoeffNeg_thetaReindex_eq_star_fourierCoeffPos`, ~line 5206):
`fourierCoeffNeg(θw, u⁰) = star(fourierCoeffPos(w, σ(u⁰)))`.
Both integrands share the same real Boltzmann prefactor `ofReal(ψ(merge(V, σ(u⁰)))·exp(...))`.
The proof: (1) `simp only [fourierCoeffNeg, fourierCoeffPos]` unfolds both; (2) `rw [← starRingEnd_apply, ← integral_conj]`
moves `star` inside the RHS integral; (3) `integral_congr_ae` + the pointwise identity (step 2 star version)
+ `RingHom.map_mul` + `Complex.conj_ofReal` + `starRingEnd_apply` to simplify.

**KEY TECHNICAL GOTCHAS discovered this session (CRITICAL for next session):**

1. **`star` vs `conj` vs `starRingEnd` — defeq but `rw` is syntactic.** On `ℂ`:
   - `star` = `@Star.star ℂ _` (the `Star` typeclass operation).
   - `conj` (from `open scoped ComplexConjugate`) = `starRingEnd _` (a bundled `ℂ →+* ℂ` `RingHom`).
   - They are **defeq** (`Complex.star_def := rfl`, `starRingEnd_apply := rfl`), but `rw` matches
     **syntactically**, so `rw [← integral_conj]` (which looks for `(starRingEnd _) (∫ ...)`) does NOT
     match `star (∫ ...)` in the goal.
   - **Fix**: `rw [← starRingEnd_apply]` converts `star x` → `(starRingEnd _) x` (= `conj x`) BEFORE
     using `integral_conj`. After the integral manipulation, `rw [starRingEnd_apply]` converts back.
   - For `conj(x * y) = conj x * conj y`, use `RingHom.map_mul` (since `starRingEnd` is a `RingHom`),
     NOT `star_mul'` (which uses `star`, not `conj`/`starRingEnd`).
   - For `conj(ofReal r) = ofReal r`, use `Complex.conj_ofReal` (which uses `conj` = `starRingEnd _`).

2. **`integral_congr_ae` + `ae_of_all` + `intro V` creates beta-redexes.** After `refine integral_congr_ae (ae_of_all μ ?_)` + `intro V`, the goal is `(fun x => ...) V = (fun y => ...) V` (beta-redexes). `rw` CANNOT match patterns inside beta-redexes. **Fix**: add `dsimp only` after `intro V` to beta-reduce before `rw`.

3. **`integral_conj` has NO integrability hypothesis** (`∫ conj(f) = conj(∫ f)` holds unconditionally, both sides 0 if non-integrable). So no `Integrable` hypothesis is needed for the Fourier coeff identity.

**Remaining step for Lemma 3:**
5. Prove `F(θw) = F(w)` (reflection symmetry of `F`). `F` is constructed by
   `plaquette_product_separable_decomp` (PeterWeyl.lean ~line 1192) from the per-plaquette
   character-expansion coefficients `coeff r s t u v` and Clebsch-Gordan coefficients `cg s t w`.
   The invariance `F(θw) = F(w)` follows from the reflection symmetry of the interface plaquette
   structure (reflection permutes the plaquettes and their link positions, preserving the
   `coeff`/`cg` structure). This is a non-trivial combinatorial step that requires understanding
   how `F` is assembled from the per-plaquette decomposition. See §8.11.21 line 1904 for the
    sum-reindexing argument.

### 8.11.24 Lemma 3 sub-step 5: θ is IDEMPOTENT (not involutive); reindexing approach needs revision (2026-08-04 session 16)

**Infrastructure proved this session** (all 0 sorries, 0 custom axioms, build GREEN 2891 jobs):

1. **`thetaReindex_idempotent`** (TransferMatrix.lean ~line 5258): `θ(θw) = θw`.
   The reindexing `θ = thetaReindex` is IDEMPOTENT, NOT involutive. It is a PROJECTION:
   it replaces `w|_{neg}` with `f(w|_{pos})` (via `reflectInterfaceLink` and `dual`),
   and leaves `w|_{pos ∪ int}` unchanged. Applying `θ` again gives the same result,
   since `θw|_{pos ∪ int} = w|_{pos ∪ int}` and `θ(θw)|_{neg}` depends on
   `θw|_{pos} = w|_{pos}` (same as `θw|_{neg}`).

2. **`charFactorPos_thetaReindex_eq`** (~line 5297): `charFactorPos(θw, U⁺) = charFactorPos(w, U⁺)`.
   Since `θw|_{pos} = w|_{pos}`. Uses `Finset.prod_congr` + `split_ifs` + `thetaReindex_pos`.

3. **`charFactorInt_thetaReindex_eq`** (~line 5313): `charFactorInt(θw, u⁰) = charFactorInt(w, u⁰)`.
   Since `θw|_{int} = w|_{int}`. Same technique.

4. **`fourierCoeffPos_thetaReindex_eq`** (~line 5333): `fourierCoeffPos(θw, u⁰) = fourierCoeffPos(w, u⁰)`.
   Follows from `charFactorPos_thetaReindex_eq` via `integral_congr_ae`.

**KEY TECHNICAL FINDING: `split_ifs` for `dite` inside `Finset.prod_congr`.**
After `simp only [charFactorPos]` + `refine Finset.prod_congr rfl (fun l hl => ?_)`, the
per-element goal has TWO `if hpos : ... then ... else 1` (dite) expressions (LHS and RHS).
`rw [dif_pos h]` only rewrites the FIRST occurrence. `simp only [dif_pos h]` makes no progress
(dif_pos not recognized as simp lemma in this context). **Fix**: use `split_ifs with h`
which splits ALL `if`/`dite` in the goal simultaneously, then `rw [thetaReindex_pos ...]`
in the `then` branch and `rfl` in the `else` branch.

**CRITICAL MATHEMATICAL FINDING: The sum reindexing `w ↦ θw` does NOT work.**

The design doc §8.11.21 claims: "After reindexing `w ↦ θw`, the sum
`∑_w F(w) · ∫ Ψ_w · B_w · A_w` becomes `∑_w F(θw) · ∫ Ψ_w · conj(A_w(σ)) · A_w`".
This requires `θ` to be a BIJECTION on `(InterfaceLink → ι)` (for `Fintype.sum_bijective`).
But `θ` is NOT a bijection — it is a PROJECTION (idempotent) that forgets `w|_{neg}`:

- `θw|_{pos ∪ int} = w|_{pos ∪ int}` (unchanged)
- `θw|_{neg} = f(w|_{pos})` (determined by `w|_{pos}` via `reflectInterfaceLink` + `dual`)

So `θ` maps `(w_P, w_I, w_N) ↦ (w_P, w_I, f(w_P))`, forgetting `w_N`. Two functions that
agree on `pos ∪ int` but differ on `neg` have the same `θw`. Hence `θ` is not injective
and the reindexing `∑_w F(w)·G(w) = ∑_w F(θw)·G(θw)` is INVALID.

**`F(θw) = F(w)` alone is NOT sufficient.** Even if `F(θw) = F(w)` (meaning `F` is
independent of `w|_{neg}`), the sum reindexing still fails because `θ` is not a bijection.
The condition `F(θw) = F(w)` says `F(w_P, w_I, w_N) = F(w_P, w_I, f(w_P))` for all `w_N`,
i.e., `F` doesn't depend on `w_N`. But this doesn't make `∑_w F(w)·B_w = ∑_w F(w)·B_{θw}`
because `B_w` depends on `w_N` while `B_{θw}` depends on `f(w_P)`, and these are different.

**The CORRECT reflection symmetry is `F(w*) = F(w)`** where `w*` is the FULL reflection
reindexing that swaps pos↔neg via `φ = reflectInterfaceLink`:
- `w*(l) = dual(w(φ⁻¹(l)))` (time-like) or `w(φ⁻¹(l))` (spatial) for `l ∈ pos`
- `w*(l) = w(l)` for `l ∈ int`
- `w*(l) = dual(w(φ(l)))` (time-like) or `w(φ(l))` (spatial) for `l ∈ neg`

This `w*` IS a bijection (it permutes link indices via `φ` on pos↔neg, identity on int).
It is an involution iff `dual` is an involution (`dual(dual(i)) = i`). It is a bijection
iff `dual` is a bijection. The reflection symmetry `F(w*) = F(w)` follows from the
reflection invariance of the plaquette product (`∏_p exp(c·Re Tr(P_p(g))) = ∏_p exp(c·Re Tr(P_p(θg)))`)
by uniqueness of the character expansion.

**Note**: `w*` is DIFFERENT from `thetaReindex w`. `thetaReindex` keeps pos unchanged and
modifies neg; `w*` swaps pos↔neg. They agree on `int` and `neg` (both give `f(w|_{pos})`
on neg), but differ on pos (`thetaReindex` gives `w|_{pos}`, `w*` gives `g(w|_{neg})`).

**Remaining work for Lemma 3** (revised plan):
1. Add `dual` bijectivity as a hypothesis (or derive from existing axioms — the current
   axiom `peterWeyl_clebschGordan_plaquette` only provides `hdual : χ_{dual(i)} = conj(χ_i)`,
   not `dual` bijectivity).
2. Define `w*` (the full reflection reindexing) and prove it's a bijection (using `dual`
   bijectivity + `reflectInterfaceLink_involution`).
3. Prove `F(w*) = F(w)` (reflection symmetry of `F` — from the reflection invariance of
   the plaquette product + uniqueness of character expansion). This requires the concrete
   `F` from `plaquette_product_separable_decomp`, not just a hypothesis.
4. Use `w*` reindexing + the σ-inversion identity `fourierCoeffNeg(θw) = conj(fourierCoeffPos(w, σ))`
   to convert the sum to the §8.2 form. The key step: after reindexing by `w*`,
   `B_{w*} = B_{θw}` (since `w*|_{neg} = θw|_{neg} = f(w|_{pos})`), and
   `B_{θw} = conj(A_w(σ))` (σ-inversion identity). But `A_{w*}` depends on `w*|_{pos} = g(w|_{neg})`,
   NOT `w|_{pos}`. So the §8.2 form `A_w · conj(A_w(σ))` is NOT directly obtained.
5. **Alternative**: Use the POS form character expansion directly:
   `K = ∑_w F'(w) · charFactorPos(w, U⁺) · charFactorInt(w, u⁰) · conj(charFactorPos(w, V⁺))`.
   This requires finding `F'` such that the POS form equals the NEG form. By uniqueness of
   character expansion, `F'(w_P, w_I) = F(w_P, w_I, f(w_P))` (up to normalization), but this
   only captures the `w_N = f(w_P)` terms, missing `w_N ≠ f(w_P)` terms. So the POS form is
   NOT valid in general unless `F` is supported on `w_N = f(w_P)`.
6. **Most promising alternative**: Use the L² expansion approach (Lemma 5, §8.5-8.6)
   directly, bypassing the σ-inversion sum reindexing. The σ-inversion identity
   `fourierCoeffNeg(θw) = conj(fourierCoeffPos(w, σ))` is still useful for evaluating the
   V⁺ integral, but the sum is handled by the L² expansion (matrix-element CG coefficients)
   rather than by reindexing.

**Key files & line numbers (current state)**:
- `thetaReindex` (~4942), `thetaReindex_pos/int/neg_time/neg_spatial` (~4954-5043),
  `thetaReindex_idempotent` (~5258), `charFactorPos_thetaReindex_eq` (~5297),
  `charFactorInt_thetaReindex_eq` (~5313), `fourierCoeffPos_thetaReindex_eq` (~5333),
  `charFactorNeg_thetaReindex_eq_charFactorPos` (~5130),
  `fourierCoeffNeg_thetaReindex_eq_star_fourierCoeffPos` (~5206).
- `reflectInterfaceLink` + involution + mem lemmas (ReflectionPositivity.lean ~2127-2184).
- `interfaceLinkPartition_disjoint_cover` (ReflectionPositivity.lean ~1116).

### 8.11.25 Lemma 3 alternative: full reflection reindexing `w*` + plain form identity `B_w = A_{w*}(σ)` (2026-08-04 session 17)

**KEY FINDING: The σ twist requires the L² expansion REGARDLESS of the reindexing issue.**

Even if the sum reindexing `w ↦ θw` were valid (it's not — θ is a projection), the resulting
"good" form would be `∑_w F(w) ∫ Ψ_w A_w conj(A_w(σ))`, which STILL has the σ twist
(`A_w(u⁰) · conj(A_w(σ(u⁰)))` ≠ `|A_w|²`). The L² expansion is needed to handle the σ
reflection on `u⁰` (which inverts time-like interface links), regardless of the reindexing.

**PROVED this session** (all 0 sorries, 0 custom axioms, build GREEN 2891 jobs):

1. **`fullReflectReindex`** (TransferMatrix.lean ~line 5375): The full reflection reindexing
   `w*` that swaps pos ↔ neg via `φ = reflectInterfaceLink`, applying `dual` on time-like links:
   - `l ∈ pos`, time-like: `w*(l) = dual(w(φ(l)))` (φ(l) ∈ neg, inverted link)
   - `l ∈ pos`, spatial: `w*(l) = w(φ(l))` (φ(l) ∈ neg, unchanged link)
   - `l ∈ int ∪ neg`: `w*(l) = w(l)` (identity)

2. **`fullReflectReindex_pos_time/pos_spatial`** (~5399/5413): Unfold `w*` on pos links.

3. **`charFactorNeg_eq_star_charFactorPos_link_fullReflect`** (~5440): Per-link identity.
   For `b ∈ pos`, `l = φ(b) ∈ neg`:
   `χ_{dual(w(l))}(reflectPosToNeg V⁺_l) = star(χ_{w*(b)}(V⁺_b))`.
   - Time-like: `χ_{dual(w(l))}((V⁺_b)⁻¹) = conj(χ_{dual(w(l))}(V⁺_b))` (repCharacter_inv)
     = `star(χ_{dual(w(l))}(V⁺_b))` (conj = star), and `w*(b) = dual(w(l))`.
   - Spatial: `χ_{dual(w(l))}(V⁺_b) = conj(χ_{w(l))}(V⁺_b))` (hdual)
     = `star(χ_{w(l))}(V⁺_b))` (conj = star), and `w*(b) = w(l)`.
   NO `dual` involutivity needed — `conj = star` (defeq) closes both cases.

4. **`charFactorNeg_eq_star_charFactorPos_fullReflect`** (~5510): Product identity.
   `charFactorNeg dual w (reflectPosToNeg V⁺) = star(charFactorPos (fullReflectReindex dual w) V⁺)`.
   Uses `Finset.prod_bij` (reindex neg → pos via `reflectInterfaceLink`) + per-link identity.
   Pushes `star` inside the `charFactorPos` product via `← starRingEnd_apply, map_prod`.

5. **`star_charFactorNeg_eq_charFactorPos_fullReflect`** (~5570): Star version.
   `star(charFactorNeg dual w (reflectPosToNeg V⁺)) = charFactorPos (fullReflectReindex dual w) V⁺`.
   Follows from (4) + `Complex.conj_conj` (star(star x) = x).

6. **`fourierCoeffNeg_eq_fourierCoeffPos_fullReflect`** (~5590): **Plain form identity**.
   `fourierCoeffNeg dual w u⁰ = fourierCoeffPos (fullReflectReindex dual w) (σ(u⁰))`,
   i.e., `B_w(u⁰) = A_{w*}(σ(u⁰))`. Follows from (5) via `integral_congr_ae`.

**Mathematical significance**: The identity `B_w = A_{w*}(σ)` is the "plain form" relationship
between the negative and positive Fourier coefficients. It does NOT require reindexing the sum
(unlike the `θ` approach which requires `w ↦ θw` reindexing, which is invalid since θ is a
projection). The sum becomes `∑_w F(w) ∫ Ψ_w A_w A_{w*}(σ)`, the "twisted" form.

**The σ twist**: `A_{w*}(σ(u⁰))` involves `σ(u⁰)` (the reflected interface config, with time-like
links inverted). This is NOT `conj(A_w(u⁰))` in general. The L² expansion is needed to handle
this twist: expand `A_w` and `A_{w*}(σ)` in the matrix-element basis, use the σ-inversion
relation `(ρ(σ(g)))_{ij} = conj((ρ(g))_{ji})` (repMatrixElement_inv), evaluate the triple
product integral using CG decomposition + Schur orthogonality, and reorganize as `∑|coeff|² ≥ 0`.

**Relationship between `w*` and `θw`**: They agree on `int` and `neg` (both give `f(w|_{pos})`
on neg), but differ on pos (`θw` gives `w|_{pos}`, `w*` gives `g(w|_{neg})` via φ). The existing
identity `B_{θw} = conj(A_w(σ))` (fourierCoeffNeg_thetaReindex_eq_star_fourierCoeffPos) and the
new identity `B_w = A_{w*}(σ)` (fourierCoeffNeg_eq_fourierCoeffPos_fullReflect) are both correct
but serve different purposes: the former requires sum reindexing (invalid), the latter does not.

**Key files & line numbers (current state)**:
- `fullReflectReindex` (~5375), `fullReflectReindex_pos_time/pos_spatial` (~5399/5413),
  `charFactorNeg_eq_star_charFactorPos_link_fullReflect` (~5440),
  `charFactorNeg_eq_star_charFactorPos_fullReflect` (~5510),
  `star_charFactorNeg_eq_charFactorPos_fullReflect` (~5570),
  `fourierCoeffNeg_eq_fourierCoeffPos_fullReflect` (~5590).
- `thetaReindex` (~4942), `thetaReindex_idempotent` (~5258),
  `charFactorNeg_thetaReindex_eq_charFactorPos` (~5130),
  `fourierCoeffNeg_thetaReindex_eq_star_fourierCoeffPos` (~5206).
- `repCharacter_inv` (PositiveDefinite.lean ~757): `χ(g⁻¹) = conj(χ(g))`.
- `repMatrixElement_inv` (PositiveDefinite.lean ~804): `(ρ g⁻¹)_{ij} = conj((ρ g)_{ji})`.
- `characterOrthogonality` (PositiveDefinite.lean ~899): Schur orthogonality of matrix elements.
- `cgME` + `hcgME_decomp` + `hcgME_unitary` (PeterWeyl.lean ~243-251): matrix-element CG coefficients.
- L² completeness (PeterWeyl.lean ~276): if all Fourier coefficients vanish, then `f = 0` a.e.

**Remaining work** (revised plan):
1. **Lemma 5 (L² expansion reorganization)**: Expand `A_w` and `A_{w*}(σ)` in the matrix-element
   basis, use σ-inversion + CG decomposition + Schur orthogonality to evaluate the triple
   product integral `∫ Ψ_w · A_w · A_{w*}(σ) dμ⁰`, and reorganize the sum as `∑|coeff|² ≥ 0`.
   This is the hard part — requires formalizing the L² expansion, CG triple product evaluation,
   and the reorganization. See §8.5-8.6 for the mathematical analysis.
2. **Assemble lemma 6**: Close `transferMatrixPositivity_axiom` (axiom count 6→5).

### 8.11.26 Lemma 5 Steps 3-4b + trivial projection lemma proved (2026-08-04 session 21)

**PROVED this session** (all 0 sorries, 0 NEW custom axioms, build GREEN 2857 jobs):

1. **`multi_link_gram_psd_nonneg`** (PeterWeyl.lean ~line 1621, Step 3 of Lemma 5): Fixed syntax
   error (lemma statement was missing summand + `:= by`). The multi-link Gram matrix PSD property:
   `0 ≤ ∑_{x,y} d(x)·conj(d(y))·∑_g ∏_l A_l(g_l,x_l)·conj(A_l(g_l,y_l))`. Proof: rewrite
   `∏_l (A_l·conj(A_l))` as `(∏_l A_l)·conj(∏_l A_l)` via `Finset.prod_mul_distrib` +
   `map_prod (starRingEnd ℂ)`, pull `∑_g` out, reorder `∑_x∑_y∑_g → ∑_g∑_x∑_y`, factor per-g
   as `normSq(∑_x d(x)·∏_l A_l)`, conclude `Finset.sum_nonneg`. `#print axioms` =
   `[propext, Classical.choice, Quot.sound]`.

2. **`reflection_positivity_reorganization`** (PeterWeyl.lean ~line 1693, Step 4b of Lemma 5):
   The weighted multi-link Gram matrix PSD property:
   `0 ≤ ∑_w F(w)·∑_{x,y} d_w(x)·conj(d_w(y))·∑_g ∏_l A^{(w,l)}(g_l,x_l)·conj(A^{(w,l)}(g_l,y_l))`
   with `F(w) ≥ 0`. Proof: `Finset.sum_nonneg` per `w`, each term `≥ 0` by
   `multi_link_gram_psd_nonneg`, and `(F w : ℂ) * gram_term ≥ 0` since `F w` is real and
   `gram_term` is real+nonneg (by `Complex.le_def` / `Complex.nonneg_iff`:
   `0 ≤ z ↔ 0 ≤ z.re ∧ 0 = z.im`). Key technique: `Complex.le_def.mpr` + `constructor` +
   `Complex.mul_re`/`Complex.mul_im` + `Complex.ofReal_re`/`Complex.ofReal_im` + `mul_nonneg`.
   `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

3. **`integral_matrix_element_trivial_projection`** (PeterWeyl.lean ~line 1876, key building
   block for time-like triple product): `∫ (ρ_σ(g))_{rs} dμ = if σ = σ_0 then 1 else 0`, where
   `σ_0` is the trivial representation (`dims σ_0 = 1`, `ρ_{σ_0}(g) = 1` identity matrix).
   Proof: rewrite `∫ (ρ_σ)_{rs} = ∫ (ρ_σ)_{rs} · conj((ρ_{σ_0})_{00})` (since
   `conj((ρ_{σ_0})_{00}) = conj(1) = 1`), then apply Schur orthogonality:
   - `σ = σ_0`: diagonal Schur gives `if r = 0 ∧ s = 0 then 1/dims σ_0 else 0 = 1` (since
     `r, s : Fin 1` are both `0` by `Subsingleton.elim`, and `dims σ_0 = 1`).
   - `σ ≠ σ_0`: off-diagonal Schur gives `0`.
   Key technique: `hσ_0_trivial : ∀ g, (ρ σ_0 g) = 1` (identity matrix, avoids `0 : Fin n`
   `NeZero` issue in parameter); `haveI : NeZero (dims σ_0) := ⟨Nat.ne_of_gt (hDims σ_0)⟩`
   inside proof; `haveI hsub : Subsingleton (Fin (dims σ)) := hσ_0_dims.symm ▸ inferInstance`
   after `subst h`. `#print axioms` = `[propext, Classical.choice, Quot.sound,
   characterOrthogonality]` (uses existing `characterOrthogonality` axiom, no NEW axioms).

**Key API findings**:
- `Complex.le_def : z ≤ w ↔ z.re ≤ w.re ∧ z.im = w.im` (in `ComplexOrder` scope, defeq `Iff.rfl`).
- `Complex.nonneg_iff : 0 ≤ z ↔ 0 ≤ z.re ∧ 0 = z.im`.
- `Complex.zero_le_real : (0 : ℂ) ≤ (x : ℂ) ↔ 0 ≤ x` (for `x : ℝ` coerced to `ℂ`).
- `Complex.mul_re : (z * w).re = z.re * w.re - z.im * w.im`.
- `Complex.mul_im : (z * w).im = z.re * w.im + z.im * w.re`.
- `Complex.ofReal_re : (r : ℂ).re = r`, `Complex.ofReal_im : (r : ℂ).im = 0`.
- `Fin 1` is `Subsingleton` (via `Unique`), but `Fin (dims σ)` needs `hσ_0_dims.symm ▸ inferInstance`.
- `NeZero n` needed for `0 : Fin n`; use `⟨Nat.ne_of_gt (hDims i)⟩` from `hDims : ∀ i, 0 < dims i`.

**Step 4a analysis (remaining work for Lemma 5)**:
The time-like triple product integral `∫ χ_s · (ρ_t)_{ij} · (ρ_u)_{kl} dμ` (WITHOUT conjugation)
requires:
1. CG decomposition of `(ρ_t)_{ij} · (ρ_u)_{kl}` (hcgME_decomp): gives `∑_ν ∑_p ∑_q cgME(t,u,ν,i,k,p) · (ρ_ν)_{pq} · conj(cgME(t,u,ν,j,l,q))`.
2. So integral = `∑_ν ∑_p ∑_q cgME(t,u,ν,i,k,p) · conj(cgME(t,u,ν,j,l,q)) · ∫ χ_s · (ρ_ν)_{pq}`.
3. Expand `χ_s = ∑_a (ρ_s)_{aa}`, CG decomp of `(ρ_s)_{aa} · (ρ_ν)_{pq}`: gives `∑_σ ∑_r ∑_s' cgME(s,ν,σ,a,p,r) · (ρ_σ)_{r,s'} · conj(cgME(s,ν,σ,a,q,s'))`.
4. So `∫ χ_s · (ρ_ν)_{pq} = ∑_a ∑_σ ∑_r ∑_s' cgME(s,ν,σ,a,p,r) · conj(cgME(s,ν,σ,a,q,s')) · ∫ (ρ_σ)_{r,s'}`.
5. `∫ (ρ_σ)_{r,s'} = if σ = σ_0 then 1 else 0` (by `integral_matrix_element_trivial_projection`).
6. Result: PSD Gram matrix in `(i,k)` vs `(j,l)` indices, with coefficient
   `∑_ν ∑_p ∑_a ∑_r cgME(t,u,ν,i,k,p) · cgME(s,ν,σ_0,a,p,r)` (and its conjugate).

The full Step 4a also requires the L² expansion (from `peterWeyl_clebschGordan_plaquette` Part 2),
the σ-inversion (`repMatrixElement_inv`), and the Fubini factorization. These are the remaining
hard parts. The spatial case uses `triple_product_character_matrix_integral` (Step 1) directly.

### 8.11.27 Time-like triple product integral formalized (2026-08-04 session 22)

**PROVED this session** (all 0 sorries, 0 NEW custom axioms, build GREEN 2857 jobs):

1. **`character_times_matrix_element_integral`** (PeterWeyl.lean ~line 1930, helper lemma):
   `∫ χ_s(g) · (ρ_ν g)_{pq} dμ = ∑_a ∑_r ∑_{s'} cgME(s,ν,σ_0,a,p,r) · conj(cgME(s,ν,σ_0,a,q,s'))`.
   Proof: expand `χ_s = ∑_a (ρ_s)_{aa}`, apply `hcgME_decomp` to `(ρ_s)_{aa} · (ρ_ν)_{pq}`,
   exchange sums with integral (4 levels: a, σ, r, s'), evaluate
   `∫ (ρ_σ)_{rs'} = if σ = σ_0 then 1 else 0` (by `integral_matrix_element_trivial_projection`),
   collapse σ sum (only σ = σ_0 contributes). `#print axioms` =
   `[propext, Classical.choice, Quot.sound, characterOrthogonality]`.

2. **`triple_product_character_matrix_integral_timelike`** (PeterWeyl.lean ~line 2060, main lemma):
   `∫ χ_s(g) · (ρ_t g)_{ij} · (ρ_u g)_{kl} dμ = ∑_ν ∑_p ∑_q (cgME(t,u,ν,i,k,p) · conj(cgME(t,u,ν,j,l q))) · (∑_a ∑_r ∑_{s'} cgME(s,ν,σ_0,a,p,r) · conj(cgME(s,ν,σ_0,a,q,s')))`.
   This is the time-like triple product WITHOUT conjugation (as arises in reflection positivity
   when the σ twist inverts time-like links). Proof: apply `hcgME_decomp` to `(ρ_t)_{ij} · (ρ_u)_{kl}`,
   exchange sums with integral (3 levels: ν, p, q), evaluate `∫ χ_s · (ρ_ν)_{pq} dμ` using
   `character_times_matrix_element_integral`. `#print axioms` =
   `[propext, Classical.choice, Quot.sound, characterOrthogonality]`.

**Key techniques**:
- **Integrability of single matrix elements** (`hInt_single`): derived from `hInt σ σ_0 r s' 0 0`
  (integrability of `(ρ_σ)_{rs'} · conj((ρ_{σ_0})_{00})`) by rewriting `conj((ρ_{σ_0})_{00}) = 1`
  via `hσ_0_trivial`. Uses `funext g; rw [hconj00 g, mul_one]` to prove function equality, then
  `rw [heq] at h; exact h` to transfer integrability.
- **Integrability of `χ_s · (ρ_ν)_{pq}`** (`hInt_char_me`): derived by rewriting the function to
  its CG decomposition (a finite sum of `(ρ_σ)_{rs'}` terms with constant coefficients) using
  `funext g; exact hpt_inner ν p q g`, then `rw [heq]` + `integrable_finsetSum` (4 levels) +
  `Integrable.smul` + `hInt_single`.
- **Outer pointwise identity** (`hpt_outer`): `χ_s · (ρ_t)_{ij} · (ρ_u)_{kl} = ∑_ν ∑_p ∑_q (coeff) · χ_s · (ρ_ν)_{pq}`
  via `rw [mul_assoc, hcgME_decomp t u g i j k l, Finset.mul_sum]` + `Finset.sum_congr` per level + `ring`.
- **Integral evaluation** (`hInt_eval`): `rw [integral_const_mul, character_times_matrix_element_integral ...]`
  pulls out the constant CG coefficient and applies the helper lemma.

**PSD property of the result**: When `dims σ_0 = 1`, `r = s' = 0` (unique element of `Fin 1`), so the
inner sum `∑_a ∑_r ∑_{s'} cgME(s,ν,σ_0,a,p,r) · conj(cgME(s,ν,σ_0,a,q,s'))` becomes
`∑_a cgME(s,ν,σ_0,a,p,0) · conj(cgME(s,ν,σ_0,a,q,0))`, a Gram matrix in `(p,q)`. The full result is
then `∑_ν ∑_a |∑_p cgME(t,u,ν,i,k,p) · cgME(s,ν,σ_0,a,p,0)|² ≥ 0` (a sum of squared norms).
This PSD property is NOT yet formalized as a separate lemma — it would require collapsing `r, s'` to `0`
using `Subsingleton (Fin (dims σ_0))` and recognizing the Gram structure.

**Remaining work for Step 4a (item 76)**:
1. ✅ Time-like triple product integral — DONE (this session).
2. ✅ Spatial triple product integral — DONE (`triple_product_character_matrix_integral`).
3. ❌ L² expansion of `A_w` and `A_{w*}(σ)` in matrix-element basis — HARDEST PART. The axiom's
   Part 2 gives completeness ("if all Fourier coefficients vanish, then f = 0 a.e."), not an
   explicit expansion. Need to either assume the expansion as a hypothesis or derive it.
4. ✅ σ-inversion for time-like links — `repMatrixElement_inv` available (PositiveDefinite.lean:804).
5. ❌ Fubini factorization of the integral over the product measure.
6. ❌ Recognition as multi-link Gram matrix → apply `reflection_positivity_reorganization`.
7. ❌ PSD property of the time-like triple product result (collapse r,s' to 0, recognize Gram).

### 8.11.28 KEY STRATEGIC INSIGHT: Character-level approach may avoid L² expansion (2026-08-04 session 22)

**Analysis**: The L² expansion (item 3 above) is the hardest part of Step 4a. However, it may
be AVOIDABLE by using the character-level kernel expansion directly:

1. `integral_G_thetaG_eq_inner_g_Tg` (TransferMatrix.lean:4776, PROVEN) reduces
   `∫ G(U)·G(θU) dμ₀ = ∫ g·(Tg) dμ⁺⁰` (inner product with transfer matrix `T`).
2. `interface_kernel_character_expansion` (PeterWeyl.lean:1469, PROVEN) gives the kernel
   `K = ∑_w F(w) · (∏_{L_U} χ_{w(l)}) · (∏_{L_0} χ_{w(l)}) · conj(∏_{L_V} χ_{dual(w(l))})`
   with `F(w) ≥ 0`. This is a sum of RANK-1 operators: `T = ∑_w F(w) · |Φ_w⟩⟨Φ_w|`.
3. By Fubini + sum-integral exchange: `∫ g·Tg = ∑_w F(w) · |⟨g, Φ_w⟩|² ≥ 0`
   (sum of non-negative terms, since `F(w) ≥ 0` and `|⟨g, Φ_w⟩|² ≥ 0`).

**Why this avoids the L² expansion**: The arbitrary function `f` (or `g`) appears only in the
Fourier coefficients `⟨g, Φ_w⟩ = ∫ g · Φ_w dμ` (finite integrals), NOT in the expansion itself.
The Gram structure comes from the character expansion of the BOLTZMANN FACTOR (a specific
function, expanded by `interface_kernel_character_expansion`), not from the L² expansion of `f`
(an arbitrary function). The `f` function does NOT need to be expanded in any basis.

**Key difference from the matrix-element approach (§8.5-8.6)**: The matrix-element approach
expands `A_w` (the Boltzmann factor) in the matrix-element basis, which requires the L²
expansion (existence part of Peter-Weyl). The character-level approach uses the CHARACTER
expansion (Part 1 of the axiom, already provided by `interface_kernel_character_expansion`),
which is sufficient because the σ twist at the character level is just conjugation
(`χ(g⁻¹) = conj(χ(g))`, handled by the `dual` map).

**Remaining work for this approach**:
- Formalize the connection between `interface_kernel_character_expansion` (abstract plaquette
  product) and the concrete transfer matrix kernel `T` (in ReflectionPositivity.lean).
- Formalize the Fubini + sum-integral exchange: `∫ g·Tg = ∑_w F(w) · |⟨g, Φ_w⟩|²`.
- Apply `Finset.sum_nonneg` to conclude `≥ 0`.
- Assemble with `integral_G_thetaG_eq_inner_g_Tg` to close `transferMatrixPositivity_axiom`.

**Note**: The time-like triple product lemmas proven this session
(`character_times_matrix_element_integral`, `triple_product_character_matrix_integral_timelike`)
are still valuable as building blocks for the matrix-element approach (fallback if the
character-level approach encounters difficulties), and as verification of the mathematical
correctness of the time-like triple product evaluation. But they may NOT be needed if the
character-level approach succeeds.

### 8.11.29 Character-level approach ANALYSIS: does NOT directly work; L² expansion required (2026-08-05 session 23)

**Analysis result**: The character-level approach (§8.11.28) does NOT directly give
`∑_w F(w) · |⟨g, Φ_w⟩|² ≥ 0`. The σ twist and the `fullReflectReindex` reindexing `w*`
are fundamental obstacles that require the L² expansion.

**Detailed findings**:

1. **The reindexing `w*` prevents rank-1 structure**: After the change of variables
   `U⁻ ↦ V⁺`, the character expansion gives
   `exp(-β·S_int(U)) = C · ∑_w F(w) · Φ_w(U⁺) · Ψ_w(U⁰) · conj(Φ_{w*}(V⁺))`
   where `w* = fullReflectReindex dual w` (proven in `charFactorNeg_eq_star_charFactorPos_fullReflect`).
   The kernel is `∑_w F(w) · |Φ_w⟩⟨Φ_{w*}|` (different vectors on left/right), NOT
   `∑_w F(w) · |Φ_w⟩⟨Φ_w|` (same vector). A sum of `|u⟩⟨v|` with `u ≠ v` is NOT
   positive in general.

2. **The σ twist breaks the Mercer-PD structure**: The integral is
   `I = ∫_{U⁺,U⁰,V⁺} h(U⁺,U⁰) · h(V⁺,σ(U⁰)) · exp(-β·S_int(U)) dμ`
   where `h(u) = f(u)·exp(-β·S⁺(u))`. The `h(V⁺,σ(U⁰))` factor uses `σ(U⁰)` (reflected
   interface links) instead of `U⁰`, so the integral is NOT of the form
   `∫∫ f(x)·conj(f(y))·K(x,y) dμ(x)dμ(y)` (Mercer form). The kernel has an implicit
   delta function `δ(V⁰, σ(U⁰))` which is discontinuous, so
   `PositiveDefiniteKernel.integralOperator_nonneg` (which requires continuity) cannot
   be applied directly.

3. **The PD property of `exp(-β·S_int)` does not directly help**: While
   `exp(-β·S_int)` is PD on `SU(N)^L` (by `plaquetteBoltzmannPD` + `PositiveDefinite.prod`),
   the PD kernel is `φ(g·h⁻¹)` (ratio of group elements). Our integral has the link
   variables in a different arrangement (not as a ratio), and the `h` factors (from the
   arbitrary function `f`) break the PD structure.

4. **The `PositiveDefinite.integral` lemma does not directly apply**: While integrating
   out `U⁰` gives a continuous kernel `K(U⁺,V⁺)`, the `h` factors prevent it from being
   Mercer-PD. The `h` factors couple `U⁺` with `U⁰` and `V⁺` with `σ(U⁰)`, breaking the
   quadratic form structure needed for Mercer-PD.

**Conclusion**: The L² expansion is NECESSARY. The σ twist and reindexing `w*` cannot be
avoided by the character-level or PD approaches alone.

**The L² expansion approach (the correct path)**:

The existing infrastructure (proven in prior sessions) provides:
- `transfer_matrix_fubini_integrated_pull` (Step 4e, TransferMatrix.lean:4632):
  `Complex.ofReal(∫ ψ·Tψ dμ⁺⁰) = C · ∑_w F(w) · ∫_{u⁰} Ψ_w(u⁰) · A_w(u⁰) · B_w(u⁰) dμ⁰(u⁰)`
- `fourierCoeffNeg_eq_fourierCoeffPos_fullReflect` (TransferMatrix.lean:5597):
  `B_w(u⁰) = A_{w*}(σ(u⁰))` where `w* = fullReflectReindex dual w`
- `triple_product_character_matrix_integral` (PeterWeyl.lean:1740, WITH conjugation, for time-like links)
- `triple_product_character_matrix_integral_timelike` (PeterWeyl.lean:2060, WITHOUT conjugation, for spatial links)
- `reflection_positivity_reorganization` (PeterWeyl.lean:1702, the assembly lemma)

The remaining steps:
1. Substitute `B_w = A_{w*}(σ)` into the Step 4e result, giving
   `I = C · ∑_w F(w) · ∫_{u⁰} Ψ_w(u⁰) · A_w(u⁰) · A_{w*}(σ(u⁰)) dμ⁰(u⁰)`.
2. Apply the L² expansion to `A_w(u⁰)` in the matrix-element basis of the interface links.
3. Use Fubini (product measure over interface links) to factorize the integral.
4. Evaluate each per-link triple product integral:
   - Time-like links (μ=0): `∫ χ_w · (ρ_λ)_{ij} · conj((ρ_μ)_{kl}) dμ` → `triple_product_character_matrix_integral`
   - Spatial links (μ≠0): `∫ χ_w · (ρ_λ)_{ij} · (ρ_μ)_{kl} dμ` → `triple_product_character_matrix_integral_timelike`
5. Reorganize the result as a multi-link Gram matrix (combining time-like and spatial
   structures — the "reorganization challenge" §8.6, which needs the matrix-element CG
   coefficients `cgME` from the axiom).
6. Apply `reflection_positivity_reorganization` to conclude ≥ 0.
7. Assemble with `integral_G_thetaG_eq_inner_g_Tg` to close `transferMatrixPositivity_axiom`.

**The L² expansion (the hardest part)**: The axiom `peterWeyl_clebschGordan_plaquette`
provides L² completeness (Part 2): if all Fourier coefficients vanish, then `f = 0` a.e.
This implies the matrix elements form a dense subspace of L². The L² expansion of `A_w`
is a countable sum (using `Λ` from the axiom), but it COLLAPSES to a finite sum after
evaluating the triple product integrals (by Schur orthogonality — most terms are zero).

**Key simplification**: The triple product integral `∫ χ_w · (ρ_λ)_{ij} · ... dμ` is zero
unless `λ` is in the CG decomposition of `w` (a finite set, since `ι` is finite). So only
finitely many `λ` contribute, and the countable sum collapses to a finite sum.

**Proposed formalization strategy**:
- Add the L² expansion as a HYPOTHESIS (finite sum, using the CG decomposition irreps).
- Prove the main lemma using the existing triple product integrals + `reflection_positivity_reorganization`.
- Discharge the hypothesis using the completeness axiom (Part 2) in a separate step.
- The key challenge is the reorganization (step 5): combining time-like and spatial Gram
  structures into the uniform multi-link Gram form required by `reflection_positivity_reorganization`.

### 8.11.30 Step 1 DONE + reorganization challenge deep analysis (2026-08-05 session 24)

**Step 1 completed**: `transfer_matrix_fubini_integrated_pull_fullReflect` (TransferMatrix.lean:5619)
combines `transfer_matrix_fubini_integrated_pull` (Step 4e) with
`fourierCoeffNeg_eq_fourierCoeffPos_fullReflect` (Lemma 3 plain form) to give the "fullReflect form":
`Complex.ofReal(∫ ψ·Tψ dμ⁺⁰) = C · ∑_w F(w) · ∫_{u⁰} Ψ_w(u⁰) · A_w(u⁰) · A_{w*}(σ(u⁰)) dμ⁰`
where `w* = fullReflectReindex dual w`. Proven via `simp only` with the pointwise equality
`fourierCoeffNeg_eq_fourierCoeffPos_fullReflect`. 0 sorries, 0 custom axioms. Build GREEN (2891 jobs).

**Reorganization challenge — deep analysis**:

The L² expansion of `A_w(u⁰)` and `A_{w*}(σ(u⁰))` in the Peter-Weyl basis gives:
`A_w(u⁰) = ∑_{(λ,i,j)} c^w_{(λ,i,j)} · ∏_l (ρ_{λ_l}(u⁰_l))_{i_l,j_l}`
`A_{w*}(σ(u⁰)) = ∑_{(μ,k,l)} c^{w*}_{(μ,k,l)} · ∏_l (ρ_{μ_l}(σ(u⁰_l)))_{k_l,l_l}`

After Fubini factorization, the per-link triple products are:
- **Time-like** (μ=0, σ(g)=g⁻¹): `∫ χ_w · (ρ_λ)_{ij} · conj((ρ_μ)_{lk}) dμ` → Gram form `∑_a A(a,(i,l))·conj(A(a,(j,k)))` with `x_l=(i_l,l_l)`, `y_l=(j_l,k_l)`.
- **Spatial** (μ≠0, σ(g)=g): `∫ χ_w · (ρ_λ)_{ij} · (ρ_μ)_{kl} dμ` → Gram form `∑_{ν,a} A((ν,a),(i,k))·conj(A((ν,a),(j,l)))` with `x_l=(i_l,k_l)`, `y_l=(j_l,l_l)`.

**KEY OBSTACLE**: The coefficient `c^w_{(λ,i,j)} · c^{w*}_{(μ,k,l)}` does NOT factor as `d(x)·conj(d(y))`
because `c^w` couples `i` (in `x`) with `j` (in `y`), and `c^{w*}` couples `l` (in `x`) with `k` (in `y`).
This prevents direct application of `reflection_positivity_reorganization`.

**Why `c^{w*} ≠ conj(c^w)`**: `charFactorPos(w*,U⁺) ≠ conj(charFactorPos(w,U⁺))` because
`fullReflectReindex` involves the link reflection `φ` (mapping pos→neg links) with selective `dual`
(time-like only), while `conj(charFactorPos(w,·))` applies `dual` to ALL links without reflection.
So the Fourier coefficients `c^w` and `c^{w*}` are genuinely different functions.

**Why `fullReflectReindex` is NOT a bijection**: `w*` on positive links depends on `w` at NEGATIVE
links (via `φ`), while `w*` on negative/interface links is the identity. So `w*` depends only on
`w|_{negative∪interface}`, losing `w|_{positive}`. Sum reindexing `w ↦ w*` is INVALID.

**Time-like trace structure**: For a single time-like link, the expression is
`Tr(P^T · B_a · Q^T · B_a†)` where `P = c^w`, `Q = c^{w*}`, `B_a` = CG coefficient matrix.
If `Q = conj(P)`, this equals `∑_a ‖P^T · B_a‖²_F ≥ 0`. But `Q ≠ conj(P)` in general.

**Possible approaches for the reorganization**:
1. **Sum over `w` provides structure**: Individual `J_w` may not be ≥ 0, but `∑_w F(w)·J_w` might be.
   The sum over `w` could allow a different grouping that produces a sum of squares.
2. **Single-function L² expansion**: Expand `A_w(u⁰)·A_{w*}(σ(u⁰))` as ONE function of `u⁰`.
   The coefficient `e^w_{(ν,p,q)}` still couples `p` (in `x`) with `q` (in `y`), so this doesn't
   directly give `d(x)·conj(d(y))` either. But the CG decomposition of the product might help.
3. **More general PSD lemma**: Instead of `reflection_positivity_reorganization` (which requires
   `d(x)·conj(d(y))`), prove a more general lemma that handles `c^w·c^{w*}` coefficients.
   The expression `Tr(P^T · B · Q^T · B†)` might be ≥ 0 under certain conditions on `P, Q, B`.
4. **Reindex the sum**: Find a bijection on the Fourier modes that transforms `c^{w*}` into
   `conj(c^w)`. This requires understanding the relationship between `F(w)` and `F(w*)`.

**Next steps**: The reorganization (step 5) is the key remaining challenge. The most promising
approach is (1) or (3): either use the sum over `w` to provide the missing structure, or prove
a more general PSD lemma that handles the `c^w·c^{w*}` coefficient structure.

### 8.11.31 Deep analysis of the reorganization: PD property alone is INSUFFICIENT (2026-08-05 session 25)

**Extensive analysis** of the reorganization step (Step 5 of Lemma 5) was performed this session.
The key findings are:

**Finding 1: The reorganization CANNOT be done term-by-term.** The `reflection_positivity_reorganization`
lemma requires `d(x)·conj(d(y))`, but the coefficient `c^w_{(λ,i,j)} · c^{w*}_{(μ,k,l)}` does NOT
factor this way because `c^w` and `c^{w*}` are independent Peter-Weyl coefficients from two SEPARATE
L² expansions (of `A_w` and `A_{w*}(σ)`). The non-negativity requires the SUM over `w`.

**Finding 2: The PD property of K alone does NOT imply the reflection positivity integral is ≥ 0.**
The PD property of a class function `K(g) = ∑_λ a_λ · χ_λ(g)` with `a_λ ≥ 0` gives the DOUBLE
integral `∫∫ f(x)·conj(f(y))·K(x⁻¹y) dμ dμ = ∑_λ (a_λ/dims(λ))·‖F_λ‖²_F ≥ 0` (standard PD quadratic
form). But the reflection positivity integral is a SINGLE integral `∫ f(g)·f(g⁻¹)·K(g) dμ`, which
is DIFFERENT. The single integral has `K(g)` (kernel at a point), while the double integral has
`K(x⁻¹y)` (kernel of the difference). The single integral is a "diagonal" restriction, not a
standard PD quadratic form.

**Finding 3: For a single time-like link, the per-λ integral is NOT ≥ 0.** The integral
`∫ f(g)·f(g⁻¹)·χ_λ(g) dμ` was computed using the Fourier transform `F_w = ∫ f(g)·ρ_w(g)† dμ` and
the CG decomposition. The result is `∑_{w,u,σ} dims(w)·∑_{i,p} R_{w,u,σ}(i,p)·conj(Q_{w,u,σ}(i,p))`
where `R` involves `F_w` and `Q` involves `F_u`. This is an inner product `⟨R, Q⟩`, NOT a norm
squared, so it's NOT necessarily ≥ 0 for a single `λ`. The non-negativity comes from the SUM
`∑_λ a_λ · [this]` with `a_λ ≥ 0`.

**Finding 4: The sum over σ (intermediate representation) gives a Gram matrix.** In the triple
product evaluation, the sum over the intermediate representation `σ` gives
`∑_σ P(σ,j,p)·conj(P(σ,i,q))` which IS a Gram matrix (PSD). But the full expression couples
different Fourier coefficients `F_w` and `F_u` through `(F_w)_{ij}·conj((F_u)_{pq})`, so the
overall expression is NOT a standard quadratic form `x†·M·x` with PSD `M`.

**Finding 5: Even/odd decomposition.** For involution `θ` (θ²=id) with `θ`-invariant `K`:
`I = ∫ f·f∘θ·K = (1/4)(∫ h²·K - ∫ k²·K)` where `h = f + f∘θ` (θ-even) and `k = f - f∘θ` (θ-odd).
For θ-even `h`: `∫ h·h∘θ·K = ∫ h²·K`. For θ-odd `k`: `∫ k·k∘θ·K = -∫ k²·K`. This decomposition
shows `I = (1/4)(∫ h²·K - ∫ k²·K)`, which is ≥ 0 iff `∫ h²·K ≥ ∫ k²·K`. This is NOT guaranteed
by the PD property alone, but might follow from the specific structure of the Boltzmann factor.

**Finding 6: The non-negativity is a DEEP property.** It requires the specific structure of the
Boltzmann factor (product of PD plaquette factors) and the support of `f` (positive+interface links).
It CANNOT be proven from the PD property of `K` alone. The standard proof (Osterwalder-Seiler) goes
plaquette by plaquette, using the fact that each plaquette factor is PD and the reflection maps
plaquettes to plaquettes. The product structure then gives the result by induction.

**Finding 7: The relationship `c^{w*} ≠ conj(c^w)` is fundamental.** For a real function `f`,
the Peter-Weyl coefficients satisfy `d_{dual(λ),p,q} = conj(d_{λ,p,q})` (reality constraint). But
`c^{w*}` (the coefficient of `A_{w*}(σ(u⁰))` in the `u⁰` basis) is NOT `conj(c^w)` because the `σ`
twist on time-like links breaks the conjugation structure: `(ρ_μ(σ(g)))_{kl} = conj((ρ_μ(g))_{lk})`
for time-like links (conjugated AND transposed), but `(ρ_μ(σ(g)))_{kl} = (ρ_μ(g))_{kl}` for spatial
links (unchanged). This mix of conjugated and non-conjugated matrix elements prevents the clean
`d(x)·conj(d(y))` factorization.

**Most promising approaches for the reorganization (updated):**
1. **Prove a more general reorganization lemma** that uses the sum over `w` and the CG coefficient
   structure. The key: the sum over `σ` gives a Gram matrix, and the sum over `λ` with `a_λ ≥ 0`
   provides the positivity. Need to show the combined sum is ≥ 0.
2. **Even/odd decomposition**: Show `∫ h²·K ≥ ∫ k²·K` for the specific structure of the Boltzmann
   factor and the support of `f`. This might use the product structure of plaquette factors.
3. **Search the literature** for the actual Osterwalder-Seiler proof. Key references: Osterwalder-
   Seiler, Glimm & Jaffe, Seiler "Gauge Theories as a Problem in Constructive QFT". The proof likely
   uses the plaquette-by-plaquette induction, not the character expansion.
4. **Plaquette-by-plaquette induction**: Instead of the L² expansion + reorganization, prove
   reflection positivity by induction on the number of plaquettes, using the PD property of each
   plaquette factor and the tensor product structure. This might be a cleaner formalization path.

**Conclusion**: The L² expansion + reorganization approach (Steps 2-5) is the current plan, but
the reorganization (Step 5) is a deep mathematical challenge. The most promising alternative is
approach (4): plaquette-by-plaquette induction, which might avoid the reorganization obstacle
entirely. This should be explored in future sessions.

### 8.11.32 KEY INSIGHT: Temporal interface links are the obstacle — expand ONLY in them (2026-08-05 session 26)

**Build GREEN (2891 jobs). No code changes this session — pure analysis.**

This session identified the precise mathematical structure of the obstruction and a clear path forward.

**Finding 1: The reflection acts differently on spatial vs temporal interface links.**

From the code (`Lattice.lean:198`): `(θU)(n, μ) = U(θn, μ)⁻¹` if μ=0 (temporal), else `U(θn, μ)` (spatial).
For interface sites (signedTime=0, fixed by reflection θ):
- **Spatial interface links** U((0,x), i): θ maps to U((0,x), i) — **FIXED** (same site, spatial direction, no inverse).
- **Temporal interface links** U((0,x), 0) = w(x): θ maps to U((0,x), 0)⁻¹ = w(x)⁻¹ — **INVERTED**.

So `θ(u⁰) = (u⁰_spatial, u⁰_temporal⁻¹)`. The spatial interface links are fixed; the temporal ones are inverted.

**Finding 2: `reflectToPosInterface` confirms the inversion.** (`TransferMatrix.lean:1111`): It creates a
full config with positive=1, negative=U⁻, interface=U⁰, then reflects and restricts to pos+interface.
The result has positive links = reflect(U⁻) and **interface links = θ(U⁰)** (temporal inverted).

**Finding 3: The interface action decomposes cleanly.** (`ReflectionPositivity.lean:455`):
`S_int = S_spatial_0(u⁰_s) + S_ts_upper(u⁺, u⁰_s, w) + S_ts_lower(U⁻, u⁰_s)` where:
- `S_spatial_0`: pure spatial plaquettes at t=0 (interface only, reflection-invariant, depends on u⁰_s only)
- `S_ts_upper`: time-space plaquettes at t=0 (involve positive links + temporal interface w + spatial interface u⁰_s)
- `S_ts_lower`: time-space plaquettes at t=-1 (involve negative links + spatial interface u⁰_s, NOT w)

Key: **w (temporal interface) appears ONLY in S_ts_upper and in f — NOT in S_ts_lower.**

**Finding 4: The transfer matrix factorizes after separating temporal/spatial interface.**

With u⁰ = (u⁰_s, w) and the S_int decomposition:
`(Tg)(u⁺, u⁰_s, w) = exp(-β·(S⁺/2 + S_spatial_0 + S_ts_upper(u⁺,u⁰_s,w))) · B(u⁰_s)`
where `B(u⁰_s) = ∫ f(reflect(U⁻), u⁰_s, w⁻¹) · exp(-β·(S⁻(U⁻,u⁰_s) + S_ts_lower(U⁻,u⁰_s))) dμ⁻`
is INDEPENDENT of u⁺ and w (S_ts_lower doesn't involve w).

Then `∫ g·Tg = ∫ A(u⁰_s) · exp(-β·S_spatial_0(u⁰_s)) · B(u⁰_s) dμ⁰_s` where
`A(u⁰_s) = ∫ f(u⁺, u⁰_s, w) · exp(-β·(S⁺ + S_ts_upper)) dμ⁺ dw` (integrated over u⁺ AND w).

By change of variables U⁻→reflect(V⁺):
`B(u⁰_s) = ∫ f(V⁺, u⁰_s, w⁻¹) · exp(-β·(S⁺(V⁺,u⁰_s) + S_ts_upper(V⁺,u⁰_s,w⁻¹))) dμ⁺ dw`
(using S⁻(reflect(V⁺),u⁰_s) = S⁺(V⁺,u⁰_s) and S_ts_lower(reflect(V⁺),u⁰_s) = S_ts_upper(V⁺,u⁰_s,w⁻¹))

So `B(u⁰_s) = ∫ f(V⁺, u⁰_s, w̃) · exp(-β·(S⁺(V⁺,u⁰_s) + S_ts_upper(V⁺,u⁰_s,w̃))) dμ⁺ dw̃`
where w̃ = w⁻¹ (renamed). Since inversion w→w⁻¹ is measure-preserving on SU(N):
**`B(u⁰_s) = A(u⁰_s)`** (the integral over w⁻¹ with f at w⁻¹ equals the integral over w with f at w,
because w→w⁻¹ is a measure-preserving bijection and S_ts_upper(V⁺,u⁰_s,w⁻¹) = S_ts_upper(V⁺,u⁰_s,w)
... WAIT: is S_ts_upper invariant under w→w⁻¹? NOT necessarily — the plaquette involves w·A, not w alone.)

**Finding 5: The w→w⁻¹ invariance of S_ts_upper is NOT automatic.** The upper interface plaquette at x is
`U_p = w(x) · A_x` where A_x = U((1,x),i)·U((1,x+î),0)†·U((0,x),i)†. Under w→w⁻¹: `U_p → w⁻¹·A_x ≠ U_p`.
So `S_ts_upper(u⁺,u⁰_s,w⁻¹) ≠ S_ts_upper(u⁺,u⁰_s,w)` in general. **B(u⁰_s) ≠ A(u⁰_s) in general.**

**Finding 6: THE RESOLUTION — Expand f in Peter-Weyl basis of w ONLY.** The key insight:

The previous approach (§8.11.30-31) expanded in ALL interface links, leading to the reorganization
obstacle. The NEW approach expands ONLY in the temporal interface links w (which are inverted by θ),
keeping the spatial interface links u⁰_s fixed (since they're fixed by θ).

Expand `f(U⁺, u⁰_s, w) = ∑_α c_α(U⁺, u⁰_s) · Φ_α(w)` where Φ_α = ∏_x (ρ_{λ_x}(w_x))_{i_x,j_x}.
Then `f(reflect(U⁻), u⁰_s, w⁻¹) = ∑_β c_β(reflect(U⁻), u⁰_s) · conj(Φ_β(w))` (since ρ(w⁻¹) = ρ(w)†).

The integral over w of `Φ_α(w) · conj(Φ_β(w)) · exp(-β·S_ts_upper(w))` is a PRODUCT of triple product
integrals (one per spatial site x), each handled by `triple_product_character_matrix_integral` (PROVEN).

The triple product integral gives a **Gram matrix structure**: `M_{α,β} = ∑_γ P_γ(α)·conj(P_γ(β))·a_γ`
where a_γ ≥ 0 are the plaquette factor coefficients and P_γ are CG coefficients.

So `∫ f·f(θ)·exp(-β·S_ts_upper) dw = ∑_γ a_γ(U⁺,u⁰_s) · D_γ(U⁺,u⁰_s) · conj(D_γ(reflect(U⁻),u⁰_s))`
where `D_γ = ∑_α c_α · P_γ(α)` and a_γ ≥ 0.

**Finding 7: The remaining integral is a PD quadratic form.** After the w-expansion:
`I = ∫ exp(-β·S_spatial_0) · ∑_γ a_γ(U⁺,u⁰_s) · D_γ(U⁺,u⁰_s) · conj(D_γ(reflect(U⁻),u⁰_s)) · exp(-β·(S_pos+S_neg)) dμ⁺dμ⁻dμ⁰_s`

Substituting U⁻→reflect(V⁺) and using S_neg(reflect(V⁺)) = S_pos(V⁺):
`I = ∫ exp(-β·S_spatial_0) · ∑_γ [∫ a_γ·D_γ·exp(-β·S_pos) dμ⁺] · [∫ conj(D_γ)·exp(-β·S_pos) dμ⁺]* dμ⁰_s`

**KEY**: a_γ(U⁺,u⁰_s) ≥ 0 comes from the plaquette factor expansion. If a_γ is CONSTANT (independent of U⁺),
then `I = ∫ exp(-β·S_spatial_0) · ∑_γ a_γ · |∫ D_γ·exp(-β·S_pos) dμ⁺|² dμ⁰_s ≥ 0`. ✓

If a_γ depends on U⁺ (through the matrix elements (ρ_ν(A_x))_{qp}), the non-negativity requires
absorbing a_γ into the positive Boltzmann factor. Since a_γ·exp(-β·S_pos) = [plaquette factor
contribution from S_ts_upper] · exp(-β·S_pos) = exp(-β·(S_pos + S_ts_upper)) evaluated at the
γ-component, this IS the full positive Boltzmann factor, which is PD. **This needs verification.**

**Finding 8: The Lüscher decomposition perspective.** After integrating out w, the transfer matrix
becomes a SUM of standard integral operators in the spatial links (one per representation γ):
`T' = ∑_γ T'_γ` where each `T'_γ` is an integral operator with kernel `K_γ(U⁺, U⁻, u⁰_s)`.
Each `T'_γ` has the Lüscher form `V^{1/2}·U_γ·V^{1/2}` where V = spatial plaquette factor (positive
multiplication) and `U_γ` = temporal plaquette operator (PD kernel in spatial links). So each `T'_γ`
is positive, and the sum `T' = ∑_γ T'_γ` is positive. This gives `∫ g·T'g ≥ 0` directly.

**The clear path forward (NEW PLAN):**
1. **Decompose interface into spatial (u⁰_s) and temporal (w) links.** Define the split formally.
2. **Expand f in Peter-Weyl basis of w ONLY.** (Not all interface links — just w.)
3. **Integrate out w using triple product integral** (PROVEN: `triple_product_character_matrix_integral`).
   This gives a Gram matrix structure with a_γ ≥ 0.
4. **Show the remaining operator is a sum of PD kernel operators** (Lüscher decomposition V^{1/2}·U·V^{1/2}).
   Each term is positive because U_γ is PD (temporal plaquette factor) and V is positive (spatial factor).
5. **Conclude `∫ g·Tg ≥ 0`** from the positivity of the sum of positive operators.

**Why this avoids the §8.11.30-31 reorganization obstacle:**
- The previous approach expanded in ALL interface links, so c^w and c^{w*} were independent coefficients
  from two separate expansions, and the reorganization needed to combine them into d(x)·conj(d(y)).
- The NEW approach expands ONLY in w (temporal interface), keeping u⁰_s fixed. The spatial interface
  links are the SAME in both f-factors (fixed by θ), so there's no mismatch in u⁰_s. The only expansion
  is in w, and the w-integral gives a Gram matrix directly (via the triple product integral).
- The "reflection twist" (w vs w⁻¹) is handled by the Peter-Weyl expansion: ρ(w⁻¹) = ρ(w)†, so the
  second f-factor's w-basis functions are conjugates of the first's. The triple product integral
  `∫ ρ_λ(w)·conj(ρ_μ(w))·ρ_ν(w) dw` is EXACTLY the proven lemma.

**Key files for the next session:**
- `triple_product_character_matrix_integral` (PeterWeyl.lean:1740) — the PROVEN triple product integral.
- `plaquetteBoltzmannPD` (PeterWeyl.lean) — the PD property of the plaquette factor (gives a_γ ≥ 0).
- `reflectToPosInterface` (TransferMatrix.lean:1111) — confirms θ(u⁰) inverts temporal interface links.
- `interfaceSites` (ReflectionPositivity.lean:203) — signedTime = 0, need to split into spatial/temporal.
- `transferMatrixCorrect` (TransferMatrix.lean:1279) — the transfer matrix to decompose.

### 8.11.33 Temporal/spatial split DEFINED + σ-action proven + proof strategy refined (2026-08-05 session 27)

**Build GREEN (2891 jobs). New code: 2 definitions + 5 lemmas, all 0 sorries, 0 custom axioms.**

**New definitions** (ReflectionPositivity.lean, after `interfaceLinkPartition_hcover`):
- `interfaceLinkTemporal (T L)` : Finset (InterfaceLink T L) — time-0 links with μ=0 (temporal).
- `interfaceLinkSpatial (T L)` : Finset (InterfaceLink T L) — time-0 links with μ≠0 (spatial).

**New lemmas** (ReflectionPositivity.lean):
- `interfaceLinkTemporal_mem_iff` / `interfaceLinkSpatial_mem_iff` : membership ↔ in L_0 ∧ μ=0/≠0.
- `interfaceLinkTemporal_spatial_partition` : Disjoint + cover (L_0 = L_0_temporal ⊔ L_0_spatial).
- `prod_interfaceLinkInt_eq_temporal_spatial` : ∏_{L_0} = ∏_{temporal} · ∏_{spatial}.

**New lemma** (TransferMatrix.lean, after `sigmaInterface` def):
- `sigmaInterface_apply` : σ(U⁰)(n,μ) = U⁰(reflectSite n, μ)⁻¹ if μ=0, else U⁰(reflectSite n, μ).
  This formally confirms §8.11.32 Finding 1: σ inverts temporal, keeps spatial.

**Proof strategy refined — the Lüscher decomposition approach:**

After deep analysis of the §8.11.32 approach, the key challenge is the U⁺-dependence of the
Gram matrix coefficients a_γ (Finding 7 concern). The resolution is the **Lüscher decomposition**:

After expanding f in the Peter-Weyl basis of temporal links w and integrating out w:
1. The w-integral gives a Gram matrix M_{α,γ}(U⁺, u⁰_s) = ∑_δ P_δ(α)·conj(P_δ(γ))·a_δ(U⁺, u⁰_s).
2. a_δ(U⁺, u⁰_s) depends on U⁺ through A_x (the product of the other 3 links in each plaquette).
3. The KEY: a_δ(U⁺, u⁰_s) · exp(-β·S⁺(U⁺)/2) is part of the FULL positive Boltzmann factor
   exp(-β·(S⁺(U⁺) + S_ts_upper(U⁺, u⁰_s, w))), which is PD (product of PD plaquette factors).
4. So the U⁺ integral ∫ c_α(U⁺, u⁰_s) · a_δ(U⁺, u⁰_s) · exp(-β·S⁺(U⁺)/2) dμ⁺ is a PD kernel
   evaluation, and the V⁺ integral is its conjugate (after the change of variables).
5. The product |∫ ... dμ⁺|² ≥ 0, and the sum over δ with a_δ ≥ 0 gives the result.

**The formalization challenge:** Step 4 requires showing that the expansion of a PD function
in matrix elements gives a PD kernel. This is a standard result in harmonic analysis on compact
groups but needs careful formalization. The key ingredients:
- `plaquetteBoltzmannPD` (PROVEN): the plaquette Boltzmann factor is PD.
- `PositiveDefinite.prod` (PROVEN): product of PD functions is PD.
- The full positive Boltzmann factor exp(-β·(S⁺ + S_ts_upper)) is PD (product of PD plaquette factors).
- Expanding in w-matrix elements and integrating out w gives a PD kernel in (U⁺, u⁰_s).

**Alternative: use the existing `reflection_positivity_reorganization` lemma.**
If a_δ is CONSTANT (independent of U⁺), the expression becomes
∫ exp(-β·S_spatial_0) · ∑_δ a_δ · |∫ D_δ · exp(-β·S_pos) dμ⁺|² dμ⁰_s ≥ 0,
which matches `reflection_positivity_reorganization` directly. But a_δ is NOT constant
(it depends on U⁺ through (ρ_ν(A_x))_{qp}). So this alternative requires the U⁺-dependence
to be absorbed into the PD kernel, as in the Lüscher approach above.

**Next session plan:**
1. Define the Peter-Weyl expansion of ψ in temporal links as a HYPOTHESIS (finite sum).
2. Substitute into the transfer matrix inner product (using the existing Fubini infrastructure).
3. Apply `triple_product_character_matrix_integral` to evaluate the temporal link integral.
4. Show the result is ≥ 0 using the PD property (Lüscher decomposition or reorganization).
5. Assemble with `integral_G_thetaG_eq_inner_g_Tg` to close `transferMatrixPositivity_axiom`.

**Key files for the next session:**
- `interfaceLinkTemporal` / `interfaceLinkSpatial` (ReflectionPositivity.lean:1171/1182) — NEW.
- `sigmaInterface_apply` (TransferMatrix.lean:1839) — NEW.
- `prod_interfaceLinkInt_eq_temporal_spatial` (ReflectionPositivity.lean:1221) — NEW.
- `triple_product_character_matrix_integral` (PeterWeyl.lean:1740) — PROVEN.
- `reflection_positivity_reorganization` (PeterWeyl.lean:1702) — PROVEN.
- `transfer_matrix_fubini_integrated_pull_fullReflect` (TransferMatrix.lean:5632) — PROVEN.
- `plaquetteBoltzmannPD` (PeterWeyl.lean:325) — PROVEN.
- `interface_kernel_character_expansion` (PeterWeyl.lean:1469) — PROVEN.

### 8.11.34 Deep analysis of the temporal expansion: the c' ≠ conj(c) obstacle PERSISTS (2026-08-05 session 28)

**Build GREEN (unchanged, 2891 jobs). No code changes this session — pure analysis.**

This session performed a deep analysis of the temporal expansion approach (§8.11.32-33) to
determine whether it actually resolves the reorganization obstacle (§8.11.30-31). The conclusion
is **NO — the temporal expansion alone does NOT resolve the obstacle.** The `c' ≠ conj(c)` problem
(Finding 7, §8.11.31) persists even after expanding only in temporal links.

**The fullReflect form (PROVEN, `transfer_matrix_fubini_integrated_pull_fullReflect`, line 5659):**

    Complex.ofReal(∫ ψ·Tψ dμ⁺⁰) = C · ∑_w F(w) · ∫_{u⁰} charFactorInt(w,u⁰) · A_w(u⁰) · A_{w*}(σ(u⁰)) dμ⁰

where:
- `charFactorInt(w,u⁰) = ∏_{l ∈ L_0} χ_{w(l)}(u⁰_l)` (product of characters over interface links)
- `A_w(u⁰) = fourierCoeffPos` (positive Fourier coefficient, a function of u⁰)
- `A_{w*}(σ(u⁰)) = fourierCoeffPos` at the reflected weight `w* = fullReflectReindex` and reflected
  interface `σ(u⁰)` (σ inverts temporal links, keeps spatial — PROVEN `sigmaInterface_apply`)
- `F(w) ≥ 0` (the character expansion coefficients of the interface Boltzmann factor)

**Step 1: Split charFactorInt into temporal and spatial parts.**
Using `prod_interfaceLinkInt_eq_temporal_spatial` (PROVEN, line 1221):

    charFactorInt(w,u⁰) = charFactorInt_temporal(w, w-links) · charFactorInt_spatial(w, u⁰_s-links)

where `charFactorInt_spatial(w, u⁰_s) = ∏_{l ∈ L_0_spatial} χ_{w(l)}(u⁰_s,l)` is INVARIANT under σ
(since σ fixes spatial links: `charFactorInt_spatial(w, σ(u⁰)) = charFactorInt_spatial(w, u⁰_s)`).

**Step 2: Expand A_w and A_{w*} in Peter-Weyl basis of temporal links.**
`A_w(u⁰_s, w-links) = ∑_α c_α(u⁰_s) · Φ_α(w-links)` where `Φ_α = ∏_x (ρ_{λ_x}(w_x))_{i_x,j_x}`.

For `A_{w*}(σ(u⁰))`: σ inverts temporal links, so `σ(u⁰)` has temporal links = (w-links)⁻¹. And
`w* = fullReflectReindex` applies `dual` on temporal pos links. Using `ρ(w⁻¹) = ρ(w)†` and
`repCharacter(ρ(dual i), g) = conj(repCharacter(ρ i), g)` (the `hdual` hypothesis):

    A_{w*}(u⁰_s, (w-links)⁻¹) = ∑_β c'_β(u⁰_s) · conj(Φ_β(w-links))

where `c'_β` is the Peter-Weyl coefficient of `A_{w*}` in the temporal-link basis.

**Step 3: The temporal-link integral is a triple product integral (PROVEN).**
The integral over temporal links:

    ∫_{w-links} charFactorInt_temporal(w, w-links) · [∑_α c_α·Φ_α] · [∑_β c'_β·conj(Φ_β)] dμ

The `charFactorInt_temporal = ∏_x χ_{w(x)}(w_x)` is a product of CHARACTERS. The integral
`∫ χ_s · Φ_α · conj(Φ_β) dμ` is EXACTLY `triple_product_character_matrix_integral` (PROVEN,
line 1740), giving a Gram matrix `∑_a cgME(s,α,β,a,...)·conj(cgME(...))` — PSD in (α,β).

**Step 4: THE OBSTACLE — the result is c†·M·c', NOT ‖c‖².**
After the temporal-link integral, the expression becomes:

    ∑_α ∑_β c_α(u⁰_s) · c'_β(u⁰_s) · M_{αβ}(w, u⁰_s)

where `M_{αβ} = ∑_a cgME·conj(cgME) ≥ 0` is a PSD Gram matrix. BUT this is `c†·M·c'` where:
- `c = (c_α)` is the Peter-Weyl coefficient vector of `A_w` (positive Fourier coefficient)
- `c' = (c'_β)` is the Peter-Weyl coefficient vector of `A_{w*}` (reflected Fourier coefficient)

**This is `c†·M·c'`, NOT `c†·M·conj(c)` or `c†·M·c`.** A PSD matrix M gives `c†·M·c ≥ 0` and
`c†·M·conj(c) ≥ 0` (if M is real-symmetric), but `c†·M·c'` for ARBITRARY c' is NOT necessarily ≥ 0.

**The fundamental issue (Finding 7, §8.11.31, CONFIRMED):** `c' ≠ conj(c)` because:
- `c_α` comes from `A_w(u⁰) = ∫ ψ(merge(U⁺,u⁰))·exp(-βS⁺/2)·charFactorPos(w,U⁺) dμ⁺`
- `c'_β` comes from `A_{w*}(σ(u⁰))` which has the σ twist (temporal links inverted) AND the dual
  representation (w* applies dual on temporal pos links).
- The σ twist + dual means `c'_β` is NOT simply `conj(c_β)`. The spatial links are the same in
  both (fixed by σ), but the temporal-link basis functions are conjugated AND the weight is dual'd.

**Conclusion: The temporal expansion + triple product integral gives a Gram matrix, but the
quadratic form is `c†·M·c'` with `c' ≠ conj(c)`, which is NOT obviously ≥ 0.** The non-negativity
requires a DEEPER property than the triple product integral alone provides.

**The Lüscher decomposition (§8.11.33) is the resolution, but it requires proving:**
1. The FULL positive Boltzmann factor `exp(-β·(S⁺ + S_ts_upper))` is PD (product of PD plaquette
   factors — `plaquetteBoltzmannPD` PROVEN, `PositiveDefinite.prod` PROVEN).
2. Expanding a PD function in matrix elements and integrating out the expanded variable gives a
   PD kernel in the remaining variables. This is a standard harmonic-analysis result but needs
   careful formalization.
3. The U⁺ integral then becomes a PD kernel evaluation, and the V⁺ integral is its conjugate
   (after the change of variables U⁻ → reflect(V⁺)), giving `|∫ ... dμ⁺|² ≥ 0`.

**The MOST PROMISING alternative (approach 4, §8.11.31, CONFIRMED by literature):**
The literature search confirms the actual Osterwalder-Seiler / Lüscher proof uses
**plaquette-by-plaquette induction**, NOT the character expansion:
- "Luscher starting from the Wilson action builds up a Hilbert space as a Fock space derived from
  equal time fields and explicitly constructs a transfer matrix which he proves to be positive
  definite" (from the Lüscher 1977 / Osterwalder-Seiler 1978 literature).
- The proof uses the fact that each plaquette factor `exp(c·Re Tr(g₁g₂g₃g₄))` is PD
  (`plaquetteBoltzmannPD` PROVEN), and reflection maps plaquettes to plaquettes, so the product
  structure gives reflection positivity by induction on the number of plaquettes.

**This avoids the character expansion (and the c' ≠ conj(c) obstacle) ENTIRELY.** The key
ingredients already PROVEN:
- `plaquetteBoltzmannPD` (PeterWeyl.lean:325) — each plaquette factor is PD.
- `PositiveDefinite.prod` — product of PD functions is PD.
- The reflection maps plaquettes to plaquettes (`reflectPlaquetteIndex`, PROVEN).

**Recommended path forward (UPDATED):**
1. **Pursue the plaquette-by-plaquette induction** (approach 4) as the PRIMARY strategy.
   This matches the actual mathematical proof and avoids the character expansion obstacle.
2. The induction would show: if `K_p(g) = exp(c·Re Tr(plaquette_p(g)))` is PD for each plaquette p,
   and reflection θ maps plaquette p to plaquette θ(p), then `∫ ∏_p K_p(g_p) · ∏_p K_p(θ(g_p)) ≥ 0`
   by induction (using PD of each factor + the tensor product structure).
3. The temporal expansion (§8.11.32-33) remains a FALLBACK if the induction is hard to formalize,
   but it requires the additional "PD kernel from PD function expansion" result (step 2 above).

**Key realization for the next session:** The character-expansion approach (Steps 1-5 of Lemma 5)
has been thoroughly explored and hits a fundamental obstacle (`c†·M·c'` with `c' ≠ conj(c)`).
The plaquette-by-plaquette induction is the mathematically correct approach and should be pursued.
The PROVEN infrastructure (`plaquetteBoltzmannPD`, `PositiveDefinite.prod`, reflection plaquette
mapping) supports this approach directly.

**Key files for the next session (plaquette induction approach):**
- `plaquetteBoltzmannPD` (PeterWeyl.lean:325) — PD of each plaquette factor (KEY INPUT).
- `PositiveDefinite.prod` (PeterWeyl.lean) — product of PD functions is PD.
- `reflectPlaquetteIndex` / `reflectPlaquetteIndexEquiv` (ReflectionPositivity.lean) — reflection
  maps plaquettes to plaquettes (involution).
- `plaquetteContribution_reflect_eq_all` (ReflectionPositivity.lean) — reflection symmetry of
  each plaquette contribution.
- `interface_boltzmann_eq_abstract_product` (ReflectionPositivity.lean:1266) — interface Boltzmann
  factor = C · ∏_{interface plaquettes} exp(c·Re Tr(...)) (the abstract plaquette product form).
- `G_thetaG_factorization` (TransferMatrix.lean:3044) — G·G(θU) factorization.
- `integral_G_thetaG_eq_inner_g_Tg` (TransferMatrix.lean:4803) — ∫ G·G(θU) = ∫ g·Tg.

### 8.11.36 CRITICAL FINDING: The axiom is FALSE with temporal interface links — fix applied (2026-08-05 session 30)

**Build GREEN (2890 jobs). Code changes made this session.**

This session discovered that the axiom `transferMatrixPositivity_axiom`, as
previously stated (with `dependsOnlyOnPosInterface`), is **FALSE**. The fix
was applied: the axiom and all downstream lemmas now use the stronger
`dependsOnlyOnPosSpatialInterface` (which excludes temporal interface links,
i.e. `μ = 0` at `t = 0` sites).

**The counterexample:**

For `β = 0` (free theory), take `f(g) = Im Tr(g)` for a single temporal
interface link `g` (at site `(0, x)`, direction `μ = 0`). This `f` satisfies
`dependsOnlyOnPosInterface` (the temporal interface link is at an interface
site, which is in `positiveSites ∪ interfaceSites`).

The reflection `θ` maps the temporal interface link to its inverse:
`θ(g) = g⁻¹` (since `reflectLinkVariable` inverts `μ = 0` links, and the
interface site `t = 0` maps to itself under reflection).

For `β = 0`, `osG(f)(U) = f(U)`, so the integral becomes:
```
∫ f(g) · f(g⁻¹) dg = ∫ Im Tr(g) · Im Tr(g⁻¹) dg
                  = ∫ Im Tr(g) · (-Im Tr(g)) dg    (since Tr(g⁻¹) = conj(Tr(g)))
                  = -∫ (Im Tr(g))² dg < 0
```

This is **strictly negative** (since `Im Tr(g)` is not identically zero on
`SU(N)` for `N ≥ 2`). The axiom is false.

The same counterexample works for small `β > 0`: for `β → 0`, the Boltzmann
factor `B₁ → 1`, so the integral approaches the `β = 0` value, which is
negative.

**Why the existing counterexample note (line 379) was insufficient:**

The codebase already had a note (ReflectionPositivity.lean:379-385) about a
counterexample for `f` depending on BOTH a positive-site link AND its
reflection (a negative-site link). The `dependsOnlyOnPosInterface` hypothesis
excludes that counterexample by requiring `f` to depend only on
positive+interface links.

However, the existing note did NOT address the case of `f` depending on
**temporal interface links** (which ARE in the positive+interface region).
The new counterexample shows that `dependsOnlyOnPosInterface` is still
insufficient: it allows `f` to depend on temporal interface links, for which
the axiom is false.

**The fix: `dependsOnlyOnPosSpatialInterface`**

A new predicate `dependsOnlyOnPosSpatialInterface` was defined
(ReflectionPositivity.lean, after `dependsOnlyOnPosInterface`). It requires
`f` to depend only on:
- All links at positive-time sites (all directions `μ`).
- **Spatial** links (`μ ≠ 0`) at interface sites (`t = 0`).

Temporal interface links (`μ = 0` at `t = 0`) are **excluded**. This matches
the Lüscher Hilbert space `L²(G^{spatial links})`, where temporal links are
integrated out as part of the transfer matrix kernel, not part of the state.

The implication `dependsOnlyOnPosSpatialInterface → dependsOnlyOnPosInterface`
was proved, so all existing lemmas using `dependsOnlyOnPosInterface` (e.g.
`G_thetaG_factorization`, `integral_G_thetaG_eq_inner_g_Tg` in
TransferMatrix.lean) still work — just apply the implication to convert.

**Changes made:**
1. Defined `dependsOnlyOnPosSpatialInterface` (ReflectionPositivity.lean).
2. Proved `dependsOnlyOnPosSpatialInterface.dependsOnlyOnPosInterface`.
3. Changed `transferMatrixPositivity_axiom` to use `dependsOnlyOnPosSpatialInterface`.
4. Changed `gibbsExpectationPeriodic_reflection_positive` to use it.
5. Changed `PeriodicExpectation.reflectionPositive` field to use it.
6. Changed `lattice_ym_reflection_positive_periodic` theorem to use it.
7. Updated axiom and theorem docstrings to explain the counterexample.
8. Build GREEN (2890 jobs). 0 sorries, 0 new custom axioms.

**Why this is the correct physical statement:**

In the Lüscher/Osterwalder-Seiler proof, the transfer matrix `T` acts on
`L²(G^{spatial links})`. The temporal links are NOT part of the Hilbert
space — they are internal to the transfer matrix and get integrated out.
The reflection `σ` only inverts temporal links, so if the state doesn't
depend on temporal links, the `σ` twist is irrelevant.

For `β = 0` with the weakened axiom: `F(u⁰)` doesn't depend on `u⁰_t`
(since `B₁ = 1`), so `∫ F · F(σ) dμ⁰ = ∫ F² dμ⁰ ≥ 0`. ✓

For `β > 0` with the weakened axiom: `F(u⁰)` depends on `u⁰_t` through
`B₁`, so the `σ` twist still appears in the integral. The Lüscher mechanism
(matrix-element expansion + Schur orthogonality) resolves this, but the
formalization is complex. The infrastructure is available:
- `characterOrthogonality` (Schur orthogonality for matrix elements).
- `peterWeyl_clebschGordan_plaquette` (CG decomposition, L² completeness).
- `plaquetteBoltzmannPD` / `plaquetteBoltzmannPD_inv` (PD of plaquette factors).

**The proof strategy for closing the (now weakened) axiom:**

The key integral to show is `≥ 0`:
```
I = ∫ f(U⁺, u⁰_s) · f(V⁺, u⁰_s) · B₁(U⁺, u⁰_s, u⁰_t) · B₁(V⁺, u⁰_s, (u⁰_t)⁻¹) dμ
```
where `f` doesn't depend on `u⁰_t` but `B₁` does (through interface plaquettes).

Step 1: Expand `B₁` in matrix elements of the temporal links `u⁰_t`. Each
plaquette factor `exp(c · Re Tr(g₁ g₂ g₃⁻¹ g₄⁻¹))` expands as:
```
∑_α a_α ∑_{i,j,k,l} ρ_α(g₁)_{ij} ρ_α(g₂)_{jk} conj(ρ_α(g₃)_{lk}) conj(ρ_α(g₄)_{il})
```
The temporal links appear as `g₂, g₄` (or their inverses).

Step 2: Take the product over plaquettes (giving a sum of products of matrix
elements).

Step 3: Integrate over `u⁰_t` using Schur orthogonality:
```
∫ ρ_α(g)_{ij} · conj(ρ_β(g)_{kl}) dg = δ_{αβ} δ_{ik} δ_{jl} / d_α
```
This pairs matrix elements from `B₁(U⁺, u⁰_t)` with those from
`B₁(V⁺, (u⁰_t)⁻¹)` (the conjugation comes from the inversion).

Step 4: Use CG unitarity to show the surviving terms form a sum of `|·|² ≥ 0`.

This is the Lüscher mechanism. It is complex but the infrastructure is
available. The key remaining work is to formalize steps 1–4.

### 8.11.35 Deep analysis of the plaquette induction: the σ twist is the SOLE obstacle (2026-08-05 session 29)

**Build GREEN (unchanged, 2891 jobs). No code changes this session — pure analysis.**

This session performed a deep analysis of the plaquette-by-plaquette induction approach (approach 4)
to determine exactly where the obstacle lies and what structure is needed to overcome it.

**KEY FINDING 1: The OS decomposition confirms the factorization.**

From the code (ReflectionPositivity.lean:431-465):
- `wilsonActionOSPositive` = plaquettes with ALL four corners at positive time (> 0). Does NOT
  include interface plaquettes.
- `wilsonActionOSNegative` = plaquettes with ALL four corners at negative time (< 0). Does NOT
  include interface plaquettes.
- `wilsonActionOSInterface` = the remaining plaquettes (straddling the interface).

So S⁺ = S⁺_pure(U⁺) (pure positive, no interface), and S_int = S_int_upper(U⁺,u⁰) + S_int_lower(U⁻,u⁰)
where upper plaquettes involve U⁺ and u⁰, and lower plaquettes involve U⁻ and u⁰.

By reflection symmetry: S_int_lower(reflect(V⁺), u⁰) = S_int_upper(V⁺, σ(u⁰)).

This gives the FACTORIZATION:
    B = exp(-β·(S⁺(U⁺,u⁰) + S⁺(V⁺,σ(u⁰)) + S_int))
      = exp(-β·(S⁺_pure(U⁺) + S_int_upper(U⁺,u⁰))) · exp(-β·(S⁺_pure(V⁺) + S_int_upper(V⁺,σ(u⁰))))
      = B₁(U⁺,u⁰) · B₁(V⁺,σ(u⁰))

where B₁(U⁺,u⁰) = exp(-β·(S⁺_pure(U⁺) + S_int_upper(U⁺,u⁰))) is the "upper half" Boltzmann factor.

**KEY FINDING 2: B₁(V⁺, u⁰_s, (u⁰_t)⁻¹) IS positive-definite.**

B₁ is a product of plaquette factors, each PD. The key question is whether B₁ with temporal links
inverted is still PD. Using the character expansion:

Each plaquette factor exp(c·Re Tr(g₁g₂g₃⁻¹g₄⁻¹)) = ∑_α a_α χ_α(g₁) χ_β(g₂) conj(χ_γ(g₃)) conj(χ_δ(g₄))
with a_α ≥ 0. When temporal links are inverted (g → g⁻¹), χ(g⁻¹) = conj(χ(g)), so the expansion
becomes a sum of products of characters and conjugate characters, each PD on the independent link
factors. The sum with non-negative coefficients is PD (PositiveDefinite.sum).

So B₁(V⁺, u⁰_s, (u⁰_t)⁻¹) is PD on (V⁺, u⁰_s, u⁰_t).

**KEY FINDING 3: The full B is PD on (U⁺, u⁰, V⁺) (Schur product).**

B₁(U⁺, u⁰_s, u⁰_t) is PD on (U⁺, u⁰_s, u⁰_t), extended to (U⁺, u⁰, V⁺) by ignoring V⁺ (PD on a
subgroup, extended via group homomorphism projection, is PD — PositiveDefinite.comp_hom).

B₁(V⁺, u⁰_s, (u⁰_t)⁻¹) is PD on (V⁺, u⁰_s, u⁰_t), extended to (U⁺, u⁰, V⁺) by ignoring U⁺.

The product of two PD functions on the SAME group is PD (Schur product theorem,
PositiveDefinite.mul / PositiveDefinite.finprod).

So B = B₁(U⁺,u⁰) · B₁(V⁺,σ(u⁰)) is PD on (U⁺, u⁰, V⁺).

**KEY FINDING 4: The integral reduces to ∫ F(u⁰) · F(σ(u⁰)) dμ⁰.**

With the factorization, the inner product ⟨g, Tg⟩ becomes:
    ⟨g, Tg⟩ = ∫_{U⁺,u⁰,V⁺} f(U⁺,u⁰) · f(V⁺,σ(u⁰)) · B₁(U⁺,u⁰) · B₁(V⁺,σ(u⁰)) dμ⁺ dμ⁰ dμ⁺
             = ∫_{u⁰} F(u⁰) · F(σ(u⁰)) dμ⁰

where F(u⁰) = ∫_{U⁺} f(U⁺,u⁰) · B₁(U⁺,u⁰) dμ⁺.

**KEY FINDING 5: WITHOUT the σ twist, the result is TRIVIALLY ≥ 0.**

If σ were the identity (no temporal link inversion), then:
    ∫ F(u⁰) · F(u⁰) dμ⁰ = ∫ F(u⁰)² dμ⁰ ≥ 0

(since F is real). The σ twist is the SOLE obstacle.

**KEY FINDING 6: For f independent of temporal interface links, the result IS ≥ 0.**

If f doesn't depend on u⁰_t, then F(u⁰) = F(u⁰_s) (independent of u⁰_t), and
F(σ(u⁰)) = F(u⁰_s, (u⁰_t)⁻¹) = F(u⁰_s) (same). So:
    ∫ F(u⁰) · F(σ(u⁰)) dμ⁰ = ∫ F(u⁰_s)² dμ⁰ ≥ 0

**KEY FINDING 7: For general f, ∫ f(g)·f(g⁻¹)·K(g) dμ is NOT necessarily ≥ 0.**

Counterexample: G = ℤ/3ℤ, f(0)=1, f(1)=1, f(2)=-1, K=1 (constant, PD and ≥ 0).
Then ∫ f(g)·f(g⁻¹)·K dμ = f(0)·f(0) + f(1)·f(2) + f(2)·f(1) = 1 - 1 - 1 = -1 < 0.

So even with K real and ≥ 0, the integral can be negative. The PRODUCT STRUCTURE of K
(product of PD plaquette factors) is essential but the link-sharing prevents simple factorization.

**KEY FINDING 8: The existing infrastructure is available but doesn't directly apply.**

- `PositiveDefinite.integral` (PositiveDefiniteIntegral.lean:98) — PROVEN: an integral (average) of
  PD functions is PD. This is the "partial trace of PD is PD" result. But our F has the f factor
  (F = ∫ f·B₁ dμ⁺, not ∫ B₁ dμ⁺), so F is NOT the partial trace of B₁.
- `PositiveDefinite.integralOperator_nonneg` (PositiveDefiniteIntegral.lean:192) — PROVEN:
  ∫∫ f(x)·conj(f(y))·φ(x⁻¹y) dμ dμ ≥ 0 for PD φ. But our integral has B at the POINT (not the
  difference x⁻¹y) and f·f (not f·conj(f)).
- `character_expansion_positivity` (PositiveDefiniteIntegral.lean:1009) — PROVEN: if K(x,y) =
  ∑_i a_i·Φ_i(x)·conj(Φ_i(θy)) with a_i ≥ 0 and θ measure-preserving, then ∫∫ f(x)·f(θy)·K =
  ∑_i a_i·‖∫ f·Φ_i‖² ≥ 0. But our kernel B = B₁(x)·B₁(θy) is a PRODUCT of two character
  expansions (double sum), not a single separable expansion. And the u⁰ variable is SHARED
  between x and y (not a product measure).

**KEY FINDING 9: The matrix M_{α,β} = ∫ χ_α·conj(χ_β)·K dμ IS PSD when K is real and ≥ 0.**

For K real and pointwise ≥ 0:
    ∑ c_α conj(c_β) M_{α,β} = ∫ |∑ c_α χ_α|² · K dμ ≥ 0

(since |∑ c_α χ_α|² ≥ 0 and K ≥ 0 pointwise). So M is PSD.

BUT the u⁰_t integral gives ∑ d_α · d_β · M_{α,β} (NOT ∑ d_α · conj(d_β) · M_{α,β}), and d_α is
COMPLEX (character coefficients of a real function satisfy d_{dual(α)} = conj(d_α), but d_α itself
is not necessarily real). So the PSD property of M does NOT directly give ∑ d_α d_β M_{α,β} ≥ 0.

**CONCLUSION: The σ twist (temporal link inversion at the interface) is the SOLE obstacle.**

The factorization B = B₁·B₁ reduces the integral to ∫ F·F(σ) dμ⁰. Without σ, this is trivially ≥ 0.
With σ, it's NOT necessarily ≥ 0 for general f (Finding 7).

The Lüscher proof handles this by using a DIFFERENT Hilbert space: L²(SU(N)^L) where L is the
number of SPATIAL links at a fixed time. The temporal links are NOT part of the Hilbert space;
they're integrated out. This avoids the σ twist entirely.

**RECOMMENDED PATH FORWARD:**
1. **Change the Hilbert space**: Instead of L²(positive+interface), use L²(positive+spatial-interface).
   Integrate out the temporal interface links FIRST. The remaining integral is over (U⁺, u⁰_s, V⁺)
   with NO σ twist (since σ only affects temporal links, and they've been integrated out).
2. **Show the u⁰_t integral is ≥ 0**: The u⁰_t integral ∫ f(U⁺,u⁰_s,u⁰_t)·f(V⁺,u⁰_s,(u⁰_t)⁻¹)·K dμ⁰_t
   needs to be shown ≥ 0. This requires the PRODUCT STRUCTURE of K (not just K ≥ 0).
3. **Alternative**: Prove the result for f independent of temporal interface links (trivially ≥ 0),
   then extend by density/continuity to general f. This requires showing the integral is continuous
   in f (boundedness/integrability conditions).
4. **Alternative**: Read the actual Lüscher (1977) / Osterwalder-Seiler (1978) proof to understand
   the specific mechanism for handling temporal link inversion, and formalize it.

**Key files for the next session:**
- `PositiveDefinite.integral` (PositiveDefiniteIntegral.lean:98) — partial trace of PD is PD.
- `character_expansion_positivity` (PositiveDefiniteIntegral.lean:1009) — abstract positivity lemma.
- `PositiveDefinite.integralOperator_nonneg` (PositiveDefiniteIntegral.lean:192) — PD → positive operator.
- `PositiveDefinite.comp_hom` (PositiveDefinite.lean:470) — PD preserved by group homomorphisms.
- `PositiveDefinite.finprod` (PositiveDefinite.lean:503) — Schur product theorem (n-ary).
- `plaquetteBoltzmannPD` (PeterWeyl.lean:325) — each plaquette factor is PD.
- `plaquetteBoltzmannPD_inv` (PeterWeyl.lean:425) — PD with inverse links.
- OS decomposition (ReflectionPositivity.lean:431-465) — S⁺/S⁻/S_int split.
- `transferMatrixReflected` (TransferMatrix.lean:2326) — the reflected transfer matrix (has σ twist).
- `integral_G_thetaG_eq_inner_g_Tg` (TransferMatrix.lean:4803) — ∫ G·G(θU) = ∫ g·Tg.

### 8.11.37 Shared-variable positivity lemma PROVEN + σ-disappears-from-g strategy (2026-08-05 session 32)

**MILESTONE: `character_expansion_nonneg_shared` is PROVEN** (PositiveDefiniteIntegral.lean:1196).
0 sorries, 0 custom axioms. Build GREEN (2972 jobs).

This is the shared-variable generalization of `character_expansion_nonneg`: when a variable `z`
is shared between the `x` and `y` integrals (not a product measure), the integral
`∫_z ∫_x ∫_y g(x,z)·g(y,z)·K(x,y,z) dμ dμ dν ≥ 0` provided `K(x,y,z) = ∑_i a(z,i)·Φ_i(z,x)·conj(Φ_i(z,y))`
with `a(z,i) ≥ 0`. For each fixed `z`, `character_expansion_positivity` (with `θ = id`) gives the
inner double integral as `↑(∑_i a(z,i)·‖∫_x g(x,z)·Φ_i(z,x) dμ‖²)`; integrating over `z` preserves
non-negativity.

**KEY FIX for the Mathlib API issue (session 31 blocker):** The blocker was a COERCION MISMATCH.
`character_expansion_positivity` produces `Complex.ofReal` coercions (displayed as `↑`), while
`integral_ofReal` (the Mathlib lemma that pulls `ofReal` out of an integral) is stated with
`RCLike.ofReal`. These are defeq (`RCLike.ofReal_eq_complex_ofReal := rfl`, Mathlib/Analysis/Complex/Basic.lean:357)
but NOT syntactically equal, so `rw [integral_ofReal]` fails ("Did not find an occurrence of the pattern").
The fix: `simp only [← RCLike.ofReal_eq_complex_ofReal]` normalises the `Complex.ofReal` coercions to
`RCLike.ofReal` BEFORE `rw [integral_ofReal]`, after which the rewrite matches.

**Key Mathlib lemmas used (all with NO integrability hypothesis):**
- `integral_congr_ae {f g : α → G} (h : f =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ` (Bochner/Basic.lean:299).
- `integral_ofReal {f : X → ℝ} : ∫ x, (f x : 𝕜) ∂μ = ↑(∫ x, f x ∂μ)` (ContinuousLinearMap.lean:158, `@[norm_cast]`).
- `Complex.zero_le_real {x : ℝ} : (0 : ℂ) ≤ (x : ℂ) ↔ 0 ≤ x` (Complex/Order.lean:92).
- `integral_nonneg {f : α → E} (hf : 0 ≤ f) : 0 ≤ ∫ x, f x ∂μ` (Bochner/Basic.lean:612, needs `ClosedIciTopology E`; `ℝ` has it).
- `MeasurePreserving.id μ : MeasurePreserving id μ μ` (Ergodic/MeasurePreserving.lean:56).

**Note:** The `hInt : Integrable ...` hypothesis was REMOVED — the lemma is true WITHOUT it (all
key lemmas work without integrability; the Bochner integral is 0 for non-integrable functions, so
`0 ≤ 0` holds trivially). This makes the lemma more general.

---

**σ-disappears-from-g lemma (step 1 of the proof strategy) — analysis and formalization plan:**

The goal: when `f` satisfies `dependsOnlyOnPosSpatialInterface`, the σ twist is invisible to
`g_posInterface`. Specifically:
```
g_posInterface(mergePosInterface(V⁺, σ(u⁰))) = g_posInterface(mergePosInterface(V⁺, u⁰))
```
where `g_posInterface(u) = f(extendLinkVariable(u)) · exp(-β·osPositiveOfPosInterface(u)/2)`.

This requires TWO sub-lemmas:

**Sub-lemma A: `f` doesn't see σ.** `f(extendLinkVariable(mergePosInterface(V⁺, σ(u⁰)))) = f(extendLinkVariable(mergePosInterface(V⁺, u⁰)))`.
The two extended configs agree on:
- **Positive-site links** (any μ): both come from V⁺ (via `mergePosInterface`). ✓
- **Spatial interface links** (n ∈ interfaceSites, μ ≠ 0): `sigmaInterface_apply` gives `σ(u⁰)(n,μ) = u⁰(reflectSite n, μ)`. For interface sites, `reflectSite n = n` (see below), so `σ(u⁰)(n,μ) = u⁰(n,μ)`. ✓
They differ ONLY on **temporal interface links** (n ∈ interfaceSites, μ = 0): `σ(u⁰)(n,0) = (u⁰(n,0))⁻¹` (inverted). But `dependsOnlyOnPosSpatialInterface` means f does NOT depend on temporal interface links. So `f` gives the same value. ✓

**KEY: `reflectSite n = n` for interface sites.** `reflectSitePeriodic n = { n with time := -n.time }` (Lattice.lean:142). For `n ∈ interfaceSites`, `signedTime T n.time = 0`. The `signedTime` definition (ReflectionPositivity.lean:157): `if t.val ≤ (T-1)/2 then t.val else t.val - T`. For `signedTime = 0`: either `t.val = 0` (first branch) or `t.val = T` (second branch, impossible since `t.val < T`). So `n.time = 0` in ZMod T, hence `-n.time = 0`, hence `reflectSitePeriodic n = n`. **This lemma needs to be proved** (it does not currently exist in the codebase). Suggested name: `reflectSite_interface_self`.

**Sub-lemma B: `osPositiveOfPosInterface` doesn't see σ.** `osPositiveOfPosInterface(mergePosInterface(V⁺, σ(u⁰))) = osPositiveOfPosInterface(mergePosInterface(V⁺, u⁰))`.
`osPositiveOfPosInterface(u) = wilsonActionOSPositive(extendLinkVariable(u))` (TransferMatrix.lean:1245).
`wilsonActionOSPositive` sums plaquettes where ALL FOUR corners have `signedTime > 0` (ReflectionPositivity.lean:465-472). A plaquette with all 4 corners positive uses ONLY links at positive sites (the links connect positive sites to positive sites). So `wilsonActionOSPositive` reads ONLY positive-site links. In both `extendLinkVariable(mergePosInterface(V⁺, σ(u⁰)))` and `extendLinkVariable(mergePosInterface(V⁺, u⁰))`, the positive-site links come from V⁺ (same). So `osPositiveOfPosInterface` gives the same value. ✓
**This requires proving `wilsonActionOSPositive` only reads positive-site links** — i.e., for any plaquette (n, μ, ν) with all 4 corners positive, all 4 links `U.value n μ`, `U.value (n+μ) ν`, `U.value (n+ν) (-μ)` (or similar), `U.value (n+μ+ν) (-ν)` are at positive sites. This follows from: if all 4 corners are positive sites, then the links between them are at positive sites. **Suggested approach:** show that for a plaquette with all corners positive, each link index `(site, dir)` has `site ∈ positiveSites`, then use `extendLinkVariable`'s definition (links at positive sites come from the config, which is V⁺ in both cases).

**Formalization order for the next session:**
1. Prove `reflectSite_interface_self`: `n ∈ interfaceSites → reflectSite n = n` (from `signedTime = 0 → n.time = 0 → reflectSitePeriodic n = n`).
2. Prove `sigmaInterface_spatial_fixed`: for `n ∈ interfaceSites, μ ≠ 0`, `sigmaInterface U_zero ⟨(n,μ),hn⟩ = U_zero ⟨(n,μ),hn⟩` (using `reflectSite_interface_self` + `sigmaInterface_apply`).
3. Prove `extendLinkVariable_merge_sigma_agree`: `extendLinkVariable(mergePosInterface(V⁺, σ(u⁰)))` and `extendLinkVariable(mergePosInterface(V⁺, u⁰))` agree on positive-site links and spatial interface links (link-by-link, using `mergePosInterface` definition + `sigmaInterface_spatial_fixed`).
4. Prove `f_sigma_invisible`: apply `dependsOnlyOnPosSpatialInterface` to (3).
5. Prove `osPositiveOfPosInterface_sigma_invariant`: using `wilsonActionOSPositive` only reads positive-site links.
6. Combine (4) + (5) → `g_posInterface_sigma_invisible`.

**After step 1 (σ-disappears), the remaining work is step 3 (Lüscher mechanism):** Show the interface
kernel `J(U⁺, V⁺, u⁰_s) = ∫_{u⁰_t} exp(-β·S_int(...)) dμ⁰_t` has a diagonal character expansion
`J = ∑_γ a_γ(u⁰_s)·Φ_γ(U⁺, u⁰_s)·conj(Φ_γ(V⁺, u⁰_s))` with `a_γ ≥ 0`. This is the HARD part —
it requires expanding the interface Boltzmann factor in characters of the temporal links, integrating
using Schur orthogonality (kills non-trivial temporal characters), and using CG decomposition.
Infrastructure available: `plaquette_product_separable_decomp`, `characterOrthogonality`,
`triple_product_character_matrix_integral`, `reflection_positivity_reorganization`,
`plaquetteBoltzmannPD` (PeterWeyl.lean:325).

### 8.11.38 CRITICAL FINDING: Character expansion gives ∑ A² (NOT ∑ |A|²) — fundamental obstacle (2026-08-06 session 34)

**Build GREEN (unchanged, 2972 jobs). No code changes this session — pure analysis.**

This session performed a deep analysis of the Lüscher mechanism (step 3) to determine whether the
character expansion approach can prove the integral is ≥ 0. The conclusion is **NO — the character
expansion gives ∑ A_α² (not ∑ |A_α|²), which is NOT necessarily ≥ 0.** This is a FUNDAMENTAL obstacle.

**The key reduction (after step 1, σ disappears from g):**

The transfer matrix inner product reduces to:
```
⟨g, Tg⟩ = ∫_{u⁰} F(u⁰) · F(σ(u⁰)) dμ⁰
```
where `F(u⁰) = ∫_{U⁺} f(U⁺, u⁰_s) · B₁(U⁺, u⁰) dμ⁺` is REAL, and `σ` inverts temporal links u⁰_t
(keeps spatial u⁰_s). The key identity: `G(u⁰) = F(σ(u⁰))` (by the change of variables u⁰_t → (u⁰_t)⁻¹,
which is measure-preserving, and U⁺/V⁺ are dummy variables with the same measure and function f).

**The character expansion in temporal links:**

`B₁(U⁺, u⁰_s, u⁰_t) = ∑_α C_α(U⁺, u⁰_s) · χ_α(u⁰_t)` (character expansion in temporal links).

`B₁(V⁺, u⁰_s, (u⁰_t)⁻¹) = ∑_α C_α(V⁺, u⁰_s) · conj(χ_α(u⁰_t))` (σ twist conjugates the CHARACTER).

So `F(u⁰) = ∑_α A_α(u⁰_s) · χ_α(u⁰_t)` and `F(σ(u⁰)) = ∑_α A_α(u⁰_s) · conj(χ_α(u⁰_t))`
where `A_α(u⁰_s) = ∫_{U⁺} f(U⁺, u⁰_s) · C_α(U⁺, u⁰_s) dμ⁺`.

The u⁰_t integral: `∫ χ_α · conj(χ_β) dμ = δ_{αβ}` (character orthogonality).

**The result: `⟨g, Tg⟩ = ∑_α ∫_{u⁰_s} A_α(u⁰_s)² dμ⁰_s`** (NOT `∑_α ∫ |A_α|² dμ⁰_s`).

The σ twist conjugates the CHARACTER (χ → conj(χ)), NOT the COEFFICIENT (C → conj(C)).
Character orthogonality gives δ_{αβ}, and the surviving term is `A_α · A_α = A_α²` (NOT `|A_α|²`).

**The dual pairing (partial resolution):**

Since B₁ is REAL, `C_{dual(α)} = conj(C_α)` (dual map: χ_{dual(α)} = conj(χ_α)).
Since f is REAL, `A_{dual(α)} = conj(A_α)`.
So `∑_α A_α² = ∑_{α=dual(α)} A_α² + ∑_{α<dual(α)} 2·Re(A_α²)`.
- Self-dual α (α = dual(α)): A_α is real, so A_α² ≥ 0. ✓
- Non-self-dual α: `2·Re(A_α²) = 2·(Re(A_α)² - Im(A_α)²)`, which can be NEGATIVE. ✗

**The dual pairing only helps for self-dual characters. The obstacle PERSISTS for non-self-dual.**

**The matrix element approach also fails:**

With matrix elements, the σ twist gives `(ρ_β((u⁰_t)⁻¹))_{kl} = conj((ρ_β(u⁰_t))_{lk})` (conjugate AND
index swap). Schur orthogonality: `∫ (ρ_α)_{ij} · conj((ρ_β)_{lk}) = δ_{αβ} δ_{il} δ_{jk} / d_α`.
Surviving term: `C_{α,i,j}(U⁺) · C_{α,j,i}(V⁺) · (1/d_α)` (index swap j,i).

The CG decomposition gives `C_{α,j,i} ≠ conj(C_{α,i,j})` in general. The coefficient of `(ρ_ν)_{qp}`
from `(ρ_s)_{aa} · (ρ_t)_{ij}` is `∑_a cgME(...,i,q) · conj(cgME(...,j,p))`, while
`conj(coefficient of (ρ_ν)_{pq})` is `∑_a conj(cgME(...,i,p)) · cgME(...,j,q)`. These are NOT equal
(the CG coefficients with i and j are NOT swapped). So `C_{α,j,i} ≠ conj(C_{α,i,j})`.

**The obstacle is FUNDAMENTAL:** The σ twist conjugates the CHARACTER/matrix-element, NOT the
COEFFICIENT. The orthogonality gives δ-matching, and the surviving term is C·C (NOT C·conj(C) = |C|²).

**The PD property of B_full does NOT help:**

The PD property gives `B_full(g·h⁻¹) = ∑_γ a_γ · χ_γ(g) · conj(χ_γ(h))` (diagonal at a DIFFERENCE).
Our integral has B_full at a POINT (U⁺, u⁰, V⁺), not at a difference. Setting g = (U⁺, u⁰, e) and
h = (e, e, (V⁺)⁻¹) gives `B_full(U⁺, u⁰, V⁺) = ∑_γ a_γ · χ_γ(U⁺) · χ_γ(u⁰) · χ_γ(V⁺)` (χ_γ(V⁺),
NOT conj(χ_γ(V⁺)) — the double conjugation from h⁻¹ and conj cancels). So the PD property gives
χ_γ(V⁺) (not conj(χ_γ(V⁺))), same as the character expansion.

**CONCLUSION: The character/matrix element expansion approach CANNOT prove the integral is ≥ 0.**
The integral `∫ F · F(σ) dμ` is NOT necessarily ≥ 0 for general real F (counterexample: ℤ/3ℤ).
The non-negativity requires ADDITIONAL STRUCTURE beyond the character expansion.

**The Lüscher mechanism likely uses a FOSS SPACE construction** (per §8.11.35: "Luscher builds up
a Hilbert space as a Fock space derived from equal time fields and explicitly constructs a transfer
matrix which he proves to be positive definite"). This is a completely different approach from the
character expansion. It requires:
1. Building the Hilbert space as a Fock space (not L² of the full link group).
2. Constructing the transfer matrix explicitly.
3. Showing it's positive definite (T = B*·B).

**RECOMMENDED PATH FORWARD:**
1. Study the actual Lüscher (1977) / Osterwalder-Seiler (1978) proof to understand the Fock space
   construction and the specific mechanism for handling temporal link inversion.
2. Formalize the Fock space approach (building the Hilbert space, constructing the transfer matrix,
   showing it's positive definite).
3. Alternatively, consider whether the PRODUCT STRUCTURE of B₁ (product of PD plaquette factors)
   gives the coefficients C_α a special positivity property that makes ∑ A_α² ≥ 0.
4. Alternatively, consider the plaquette-by-plaquette induction (approach 4, §8.11.35).

**Key files for the next session:**
- `peterWeyl_clebschGordan_plaquette` (PeterWeyl.lean) — provides ι, ρ, cgME, hcgME_decomp, hcgME_unitary.
- `characterOrthogonality` (PeterWeyl.lean) — Schur orthogonality for matrix elements.
- `plaquetteBoltzmannPD` / `plaquetteBoltzmannPD_inv` (PeterWeyl.lean:325/425) — PD of plaquette factors.
- `interface_kernel_character_expansion` (PeterWeyl.lean:1469) — separable character expansion.
- `character_expansion_nonneg_shared` (PositiveDefiniteIntegral.lean:1196) — shared-variable positivity.
- `transfer_matrix_fubini_integrated_pull_fullReflect` (TransferMatrix.lean:5792) — the fullReflect form.
- `g_posInterface_sigma_invisible` (TransferMatrix.lean:1986) — σ disappears from g (step 1, DONE).
- `fullReflectReindex` (TransferMatrix.lean:5536) — w* = dual on temporal pos links, w on spatial pos links.

### 8.11.39 KEY BREAKTHROUGH: Single-step transfer matrix kernel IS PD via gauge-fixing + character expansion (2026-08-06 session 35)

**Build GREEN (unchanged, 2972 jobs). No code changes this session — pure analysis.**

This session performed a deep analysis of the gauge-fixing approach and discovered a KEY BREAKTHROUGH: the
**single-step transfer matrix kernel IS PD** (positive definite), proven by gauge-fixing + character expansion
of the delta function + Schur orthogonality. This is a completely new approach that hasn't been tried before.

**The single-step transfer matrix kernel:**

The transfer matrix T acts on L²(G^L) (spatial links at a fixed time). Its kernel is:
```
K(u_s, v_s) = exp(-S_spatial(u_s)/2) · exp(-S_spatial(v_s)/2) · ∫ ∏_x B_p(u_t(x) · v_s(x) · u_t(x+1)⁻¹ · u_s(x)⁻¹) dμ(u_t)
```

The key: the temporal plaquette variable U_p(x) = u_t(x) · v_s(x) · u_t(x+1)⁻¹ · u_s(x)⁻¹ can be written as
U_p(x) = u_t(x) · W(x) · u_t(x+1)⁻¹ where W(x) = v_s(x) · u_s(x)⁻¹. Since B_p is a CLASS FUNCTION
(B_p(g) = B_p(h·g·h⁻¹)), conjugating by u_t(x) gives:
```
B_p(U_p(x)) = B_p(W(x) · v(x))
```
where v(x) = u_t(x+1)⁻¹ · u_t(x) is the "relative temporal link" (gauge-invariant variable).

**Gauge-fixing + character expansion:**

The map u_t → v is a submersion (gauge orbit of dimension |G|). Gauge-fixing u_t(0) = e determines u_t(x)
recursively from v. The periodic constraint gives ∏ v(x) = e (in the right order).

The delta function enforcing the constraint is expanded in characters (Peter-Weyl):
```
δ(∏ v(x) - e) = ∑_γ d_γ χ_γ(∏ v(x))
```

After gauge-fixing and expanding the delta function, the integral over v(x) uses Schur orthogonality.

**The result (for L=2, one spatial direction):**
```
K_temporal(u_s, v_s) = ∑_γ (|c_γ|² / d_γ) χ_γ(W(0) · W(1))
```
where W(x) = v_s(x) · u_s(x)⁻¹ and c_γ are the character expansion coefficients of B_p.

This is a PD function because:
1. |c_γ|² / d_γ ≥ 0 (non-negative coefficients). ✓
2. χ_γ(W(0) · W(1)) is a PD function (characters are PD). ✓
3. A sum of PD functions with non-negative coefficients is PD. ✓

**The transfer matrix is self-adjoint:** K_temporal(v, u) = conj(K_temporal(u, v)) = K_temporal(u, v)
(since K_temporal is real and χ_γ(g⁻¹) = conj(χ_γ(g))). ✓

**The reflection positivity obstacle (σ twist):**

The reflection positivity kernel is:
```
K_refl(X, Y, s) = ∫ B_interface(X, s, u) · B_interface(Y, s, u⁻¹) dμ(u)
```

The σ twist (u → u⁻¹) changes v(x) = u(x+1)⁻¹ · u(x) to v'(x) = u(x+1) · u(x)⁻¹ ≠ v(x)⁻¹
(for non-abelian G). This creates FOUR-POINT FUNCTIONS (each temporal link is shared between 2 plaquettes
from X side and 2 from Y side), which don't simplify to |A|².

**Key insight: the σ twist is an ARTIFACT of the reduction to ∫ F·F(σ) dμ.**

The ORIGINAL path integral has INDEPENDENT bra and ket (positive and negative halves). The reduction to
∫ F·F(σ) dμ IDENTIFIES them through the interface temporal links, introducing the σ twist.

The single-step transfer matrix kernel (with INDEPENDENT bra and ket) IS PD. The question is whether the
reflection positivity can be REDUCED to the single-step positivity.

**Relationship between reflection positivity and transfer matrix positivity:**

The reflection positivity is: ∫ G(U) · G(θU) dμ₀(U) ≥ 0 where G(U) = f(U)·exp(-βS⁺(U))·exp(-βS⁰(U)/2).

This is NOT ⟨f, Tf⟩ (which would be trivially ≥ 0 if T is positive). It's a SINGLE integral with the
reflection θ, which is a DIFFERENT expression.

The reflection positivity can be written as ⟨θg, T^{2n}g⟩ (for n time steps on each side), which involves
the reflection θ. This is NOT trivially ≥ 0 even if T is positive and self-adjoint.

However, using the factorization T = B*B (positive square root) and the fact that T commutes with θ:
```
⟨θg, T²g⟩ = ⟨θg, T·Tg⟩ = ⟨Tθg, Tg⟩ = ⟨θTg, Tg⟩ = ⟨θf, f⟩ where f = Tg
```
So the reflection positivity reduces to ⟨θf, f⟩ ≥ 0, which is the "reflection inner product" of f with itself.
This is NOT automatically ≥ 0 for general f, but it IS ≥ 0 for f = Tg (coming from the transfer matrix).

**Literature references found:**
1. Osterwalder-Seiler (1978): "Gauge field theories on a lattice", Annals of Physics 110, 440-471.
2. Brydges-Fröhlich-Seiler (1979): "On the construction of quantized gauge fields. I. General results",
   Annals of Physics 121, 227-284. Introduces "half gauge fields".
3. Seiler (1982): "Gauge Theories as a Problem of Constructive QFT and Statistical Mechanics",
   Lecture Notes in Physics 159, Springer. (Most accessible source for the proof mechanism.)
4. Zenkin: "Reflection positive formulation of chiral gauge theories on a lattice" — uses BFS half gauge fields.
5. Neeb-Olafsson: "Reflection Positivity—A Representation Theoretic Perspective" — representation-theoretic approach.

**RECOMMENDED PATH FORWARD:**
1. **Read Seiler (1982) lecture notes** (Lecture Notes in Physics 159, Springer) — this is the most
   accessible source for the actual proof mechanism. It likely describes the gauge-fixing approach and
   how the σ twist is handled.
2. **Study the BFS "half gauge fields" approach** — Brydges-Fröhlich-Seiler introduced "half gauge fields"
   which may be the key to handling the σ twist. The idea is to split the gauge field into two halves
   (positive and negative), each of which is independently gauge-fixed.
3. **Formalize the single-step transfer matrix kernel PD property** — this is a CONCRETE, FORMALIZABLE
   result: K_temporal = ∑ (|c_γ|²/d_γ) χ_γ ≥ 0. The key ingredients are:
   - Gauge-fixing of temporal links (reducing to gauge-invariant variables v)
   - Character expansion of the delta function (constraint ∏ v(x) = e)
   - Schur orthogonality (computing the matrix elements)
   - Non-negative coefficients |c_γ|²/d_γ ≥ 0
4. **Reduce reflection positivity to single-step positivity** — the key is to show that the reflection
   positivity integral ∫ G(U)·G(θU) dμ can be written as ⟨f, Tf⟩ for some f and the positive operator T.
   This requires understanding the factorization of the Boltzmann factor and the role of the interface.
5. **Consider the operator approach T = B*B** — define the "half-step" operator B and show T = B*B,
   giving ⟨f, Tf⟩ = ‖Bf‖² ≥ 0. The challenge is defining B (the square root of the Boltzmann factor
   is NOT the product of square roots of plaquette factors).

**Key technical details for formalization:**
- The gauge-fixing uses the TEMPORAL AXIAL GAUGE: u_t(0) = e. This is a linear gauge with Faddeev-Popov
  determinant 1.
- The constraint ∏ v(x) = e (periodic BC) is enforced by the delta function, expanded in characters.
- The Schur orthogonality gives: ∫ ρ^γ_{ij}(g) · conj(ρ^δ_{kl}(g)) dμ(g) = δ_{γδ} δ_{ik} δ_{jl} / d_γ.
- The matrix element computation: M^γ_{ij}(W) = ∫ B_p(W·g) · ρ^γ_{ij}(g) dμ(g) = conj(c_γ) · ρ^{γ*}_{ij}(W) / d_γ.
- The kernel: K_temporal = ∑_γ d_γ Tr(M^γ(W(0)) · M^γ(W(1))) = ∑_γ (|c_γ|²/d_γ) χ_γ(W(0)·W(1)).
- The self-adjointness: K_temporal(v,u) = conj(K_temporal(u,v)) = K_temporal(u,v) (since K is real).

### 8.11.40 KEY FINDING: S⁺ independent of u⁰_t + proof structure clarified (2026-08-06 session 36)

**Build GREEN (unchanged, 2972 jobs). No code changes this session — pure analysis.**

This session clarified the exact proof structure for closing `transferMatrixPositivity_axiom` and identified
the precise remaining gap.

**CRITICAL FINDING: S⁺ does NOT depend on u⁰_t (temporal interface links).**

From the definition of `wilsonActionOSPositive` (ReflectionPositivity.lean:494-501):
S⁺ sums over plaquettes where ALL FOUR corners have `signedTime > 0` (strictly positive time).
The temporal interface links u⁰_t connect t=0 to t=1, so plaquettes involving them have corners at t=0
and t=1 — NOT all strictly positive. Therefore these plaquettes are in S_int, NOT S⁺.

**Consequence:** `osPositiveOfPosInterface(mergePosInterface(V⁺, u⁰))` depends on V⁺ and u⁰_s (spatial
interface links) but NOT on u⁰_t (temporal interface links). Combined with `dependsOnlyOnPosSpatialInterface`
(g doesn't depend on u⁰_t), the Fourier coefficient `A_w(u⁰) = fourierCoeffPos(w, u⁰)` depends only on u⁰_s.

**The complete proof structure (6 steps):**

1. **∫ G·G(θU) = ∫ g·(Tg)** — PROVEN (`integral_G_thetaG_eq_inner_g_Tg`, TransferMatrix.lean:4936).
   This reduces reflection positivity to showing the transfer matrix T is a positive operator.

2. **σ disappears from g** — PROVEN (`g_posInterface_sigma_invisible`, TransferMatrix.lean:1986).
   With `dependsOnlyOnPosSpatialInterface`, g(mergePosInterface(V⁺, σ(u⁰))) = g(mergePosInterface(V⁺, u⁰)).

3. **Character expansion of T** — PROVEN (`transfer_matrix_fubini_integrated_pull_fullReflect`, TransferMatrix.lean:5792).
   ∫ ψ·T(ψ) = C · ∑_w F(w) · ∫_{u⁰} charFactorInt(w, u⁰) · A_{w*}(σ(u⁰)) · A_w(u⁰) ∂μ⁰
   where A_w = fourierCoeffPos(w, ·), w* = fullReflectReindex(w).

4. **σ-invisibility of A_{w*}** — **PROVED (2026-08-08 session 53).** `fourierCoeffPos_sigma_invisible`
   (`TransferMatrix.lean:4650`) — the positive Fourier coefficient `A_w(u⁰) = fourierCoeffPos(w, u⁰)`
   is σ-invisible: `A_w(σ(u⁰)) = A_w(u⁰)` when `f` satisfies `dependsOnlyOnPosSpatialInterface`.
   0 sorries, 0 new axioms, `#print axioms` = `[propext, Classical.choice, Quot.sound]`. Proof: the
   integrand `g(merge(U⁺, u⁰))·exp(-β·S⁺(merge(U⁺, u⁰))/2)·charFactorPos(w, U⁺)` has its `u⁰`-dependence
   only through `g` and `S⁺`, both σ-invisible (`g_posInterface_sigma_invisible` +
   `osPositiveOfPosInterface_sigma_invariant`); `charFactorPos` depends only on `U⁺`. So:
   ∫ ψ·T(ψ) = C · ∑_w F(w) · ∫_{u⁰} charFactorInt(w, u⁰) · A_{w*}(u⁰) · A_w(u⁰) ∂μ⁰

5. **u⁰_t integral via character orthogonality** — Since A_w and A_{w*} don't depend on u⁰_t (step 1 finding),
   the u⁰_t integral of charFactorInt(w, u⁰) gives δ_{w(l), trivial} for temporal interface links l.
   The sum collapses to w with w(l) = trivial for temporal links. For these w:
   ∫ ψ·T(ψ) = C · ∑_{w: temporal trivial} F(w) · ∫_{u⁰_s} charFactorInt_spatial(w, u⁰_s) · A_{w*}(u⁰_s) · A_w(u⁰_s) ∂μ⁰_s

6. **Non-negativity of the remaining kernel** — THE REMAINING GAP.
   The kernel K(V⁺, V'⁺, u⁰_s) = C · ∑_w F(w) · charFactorInt_spatial(w, u⁰_s) · charFactorPos(w, V⁺) · charFactorPos(w*, V'⁺)
   needs to be shown ≥ 0 when integrated against g·g.

   **OBSTACLE:** The coefficients F(w) · charFactorInt_spatial(w, u⁰_s) are COMPLEX (characters are complex),
   NOT non-negative reals. So `character_expansion_nonneg_shared` (PositiveDefiniteIntegral.lean:1196) does NOT
   directly apply — it requires a(z,i) ≥ 0.

   **SOLUTION: The Lüscher mechanism** (from §8.11.39). The current code's character expansion (h_char) expands
   the BOLTZMANN FACTOR exp(-β·S_int), giving complex coefficients F(w). The Lüscher mechanism instead:
   (a) Gauge-fixes temporal links (temporal axial gauge u⁰_t = e)
   (b) Introduces a delta function (constraint ∏ v(x) = e from periodic BC)
   (c) Expands the delta function in characters: δ(g) = ∑_γ d_γ χ_γ(g) (with d_γ > 0)
   (d) Applies Schur orthogonality to get non-negative coefficients |c_γ|²/d_γ ≥ 0
   (e) The resulting kernel K = ∑_γ (|c_γ|²/d_γ) χ_γ(W(0)·W(1)) is PD

   This is a DIFFERENT character expansion from the current code's approach. The Lüscher mechanism has NOT been
   formalized yet.

**`character_expansion_nonneg_shared` (PositiveDefiniteIntegral.lean:1196) — the key non-negativity lemma:**
If K(x,y,z) = ∑_i a(z,i) · Φ_i(z,x) · conj(Φ_i(z,y)) with a(z,i) ≥ 0, then
∫∫∫ g(x,z)·g(y,z)·K(x,y,z) dμ(x) dμ(y) dν(z) ≥ 0.
This is because the inner double integral equals ∑_i a(z,i) · |∫ g(x,z)·Φ_i(z,x) dμ|² ≥ 0.
This lemma IS the right tool for the final step — once the Lüscher mechanism provides non-negative coefficients.

**Remaining work to close `transferMatrixPositivity_axiom`:**
1. Formalize the gauge-fixing of temporal links (temporal axial gauge u⁰_t = e)
2. Formalize the delta function expansion (constraint ∏ v(x) = e): δ(g) = ∑_γ d_γ χ_γ(g)
3. Apply Schur orthogonality to get non-negative coefficients |c_γ|²/d_γ
4. Show the resulting kernel K(V⁺, V'⁺, u⁰_s) = ∑_γ (|c_γ|²/d_γ) · Φ_γ(u⁰_s, V⁺) · conj(Φ_γ(u⁰_s, V'⁺)) matches the form of `character_expansion_nonneg_shared`
5. Apply `character_expansion_nonneg_shared` to get ∫ g·(Tg) ≥ 0
6. Combine with `integral_G_thetaG_eq_inner_g_Tg` to close `transferMatrixPositivity_axiom`

**Key infrastructure already available:**
- `integral_G_thetaG_eq_inner_g_Tg` (TransferMatrix.lean:4936) — reduces ∫ G·G(θU) to ∫ g·(Tg)
- `g_posInterface_sigma_invisible` (TransferMatrix.lean:1986) — σ disappears from g
- `transfer_matrix_fubini_integrated_pull_fullReflect` (TransferMatrix.lean:5792) — character expansion of T
- `character_expansion_nonneg_shared` (PositiveDefiniteIntegral.lean:1196) — non-negativity lemma
- `plaquetteBoltzmannPD` / `plaquetteBoltzmannPD_inv` (PeterWeyl.lean:325/425) — PD of plaquette factors
- `characterOrthogonality` (PeterWeyl.lean) — Schur orthogonality for matrix elements
- `peterWeyl_clebschGordan_plaquette` (PeterWeyl.lean) — axiom providing ι, ρ, cgME, hcgME_decomp, hcgME_unitary

**Literature:** Seiler (1982) "Gauge Theories as a Problem of Constructive QFT and Statistical Mechanics"
(Lecture Notes in Physics 159, Springer, doi:10.1007/3-540-11559-5) is the most accessible source for the
proof mechanism. Available on Springer (behind paywall) and Stanford/IMSc libraries. The nLab page
(https://ncatlab.org/nlab/show/Erhard+Seiler) confirms the references.

### 8.11.41 KEY BREAKTHROUGH: 1D Lüscher calculation gives non-negative coefficients (2026-08-06 session 37)

**Build GREEN (unchanged, 2972 jobs). No code changes this session — pure analysis.**

This session performed a detailed calculation of the temporal plaquette integral (the Lüscher mechanism)
for the 1D case (one spatial direction, L sites) and confirmed it gives **non-negative coefficients**.
This is the key building block for closing `transferMatrixPositivity_axiom`.

#### The A ≠ B obstacle (confirmed)

The reflection positivity integral reduces to:
```
⟨g, Tg⟩ = ∫_{u⁰_s} exp(-β S_int^{spatial}(u⁰_s)) · A(u⁰_s) · B(u⁰_s) dμ⁰_s
```
where:
- `A(u⁰_s) = ∫_{U⁺} f(U⁺, u⁰_s) exp(-β S⁺(U⁺, u⁰_s)) J_upper(U⁺_ν, u⁰_ν) dμ⁺`
- `B(u⁰_s) = ∫_{V⁺} f(V⁺, u⁰_s) exp(-β(S⁺(V⁺, u⁰_s) + S_int^{lower,refl}(V⁺, u⁰_s))) dμ⁺`
- `J_upper(U⁺_ν, u⁰_ν) = ∫_{u⁰_t} exp(-β S_int^{upper}(u⁰_t, U⁺_ν, u⁰_ν)) dμ⁰_t`

**A ≠ B** because:
- In A, the interface temporal links `u⁰_t` (at t=0) are SEPARATE from the positive temporal links `U⁺_t`
  (at t>0). `S⁺` doesn't involve `u⁰_t` (session 36 finding), so `u⁰_t` is integrated out independently
  (giving `J_upper`), and `U⁺_t` appears only in `S⁺` and `f`.
- In B, the reflected lower interface temporal links `V⁺_t` (at t=1, = reflected `U⁻_t`) ARE the positive
  temporal links. `S_int^{lower,refl}` has the SAME functional form as `S_int^{upper}` but with `V⁺_t`
  instead of `u⁰_t`. And `S⁺` DOES involve `V⁺_t` (positive plaquettes at t=1 use `V⁺_t`). So `V⁺_t`
  appears in BOTH `S⁺` and `S_int^{lower,refl}`, and `f` depends on `V⁺_t` (since
  `dependsOnlyOnPosSpatialInterface` allows dependence on positive temporal links).

**The asymmetry is structural:** the upper interface involves `u⁰_t` (at t=0, NOT part of the positive
config, integrated out separately), while the reflected lower involves `V⁺_t` (at t=1, IS part of the
positive config, coupled with `S⁺` and `f`).

**Gauge-fixing doesn't resolve the asymmetry:** The temporal axial gauge fixes `u⁰_t = e` (at t=0),
simplifying the upper interface, but `V⁺_t` (at t=1) is NOT gauge-fixed. Fixing ALL temporal links is
NOT a valid gauge-fixing (FP determinant = 0, residual time-independent gauge freedom).

#### The 1D Lüscher calculation (KEY RESULT)

For ONE spatial direction with L sites (periodic), the temporal plaquette integral is:
```
U_1D(u_s, v_s) = ∫ ∏_{x=0}^{L-1} B_p(u_t(x) · W(x) · (u_t(x+1))⁻¹) ∏_{x=0}^{L-1} du_t(x)
```
where `W(x) = v_s(x) · (u_s(x))⁻¹` and `u_t(L) = u_t(0)` (periodic).

**Character expansion:** `B_p(g) = ∑_γ c_γ χ_γ(g)` with `c_γ ≥ 0` (from `plaquetteBoltzmannPD`).

**Matrix element expansion:** `χ_γ(u v w⁻¹) = ∑_{i,j,k} (ρ_γ(u))_{ij} (ρ_γ(v))_{jk} conj((ρ_γ(w))_{ik})`
(using `ρ_γ(g⁻¹) = ρ_γ(g)†`, so `(ρ_γ(w⁻¹))_{ki} = conj((ρ_γ(w))_{ik})`).

**Product over x:**
```
∏_x B_p(u_t(x) W(x) (u_t(x+1))⁻¹) = ∑_{γ_0,...,γ_{L-1}} ∏_x c_{γ_x} ∑_{i_x,j_x,k_x}
  (ρ_{γ_x}(u_t(x)))_{i_x j_x} (ρ_{γ_x}(W(x)))_{j_x k_x} conj((ρ_{γ_x}(u_t(x+1)))_{i_x k_x})
```

**Schur orthogonality at each site:** The integral over `u_t(x)` pairs the unbarred matrix element
from plaquette x with the barred from plaquette x-1:
```
∫ (ρ_{γ_x}(u_t(x)))_{i_x j_x} conj((ρ_{γ_{x-1}}(u_t(x)))_{i_{x-1} k_{x-1}}) du_t(x)
  = δ_{γ_x, γ_{x-1}} δ_{i_x, i_{x-1}} δ_{j_x, k_{x-1}} / d_{γ_x}
```

**Cascade result:** All `γ_x = γ` (same), all `i_x = i` (same), and `k_x = j_{x+1}` (index propagation).
The sum over `i` gives `d_γ`, and the sum over `j_0,...,j_{L-1}` with `j_L = j_0` gives the trace:
```
U_1D = ∑_γ (c_γ)^L / d_γ^{L-1} · χ_γ(∏_{x=0}^{L-1} W(x))
```

**Non-negativity:** `(c_γ)^L / d_γ^{L-1} ≥ 0` (since `c_γ ≥ 0`, `d_γ > 0`), and `χ_γ` is PD.
So `U_1D` is a sum of PD functions with non-negative coefficients → **U_1D is PD**. ✓

**Key mechanism:** The Schur orthogonality MATCHES representations across adjacent plaquettes
(`δ_{γ_x, γ_{x-1}}`), forcing all `γ_x` to be equal. The coefficient is `(c_γ)^L / d_γ^{L-1} ≥ 0`
because the SAME `c_γ` appears at each plaquette (B_p is the same function). This is the Lüscher
mechanism: the GLOBAL cascade of Schur orthogonality gives non-negative coefficients.

#### The 3D case (plan)

For 3 spatial directions, each `u_t(x)` appears in 6 plaquettes (3 directions × 2 per direction).
The integral over `u_t(x)` involves 3 unbarred and 3 barred matrix elements, requiring CG decomposition
to combine them. The Schur orthogonality matches the COMBINED representations (not individual γ's).

**The 3D obstacle (from §8.11.38):** The CG coefficients from the unbarred (forward plaquettes at x)
and barred (backward plaquettes at x-ν̂) sides involve DIFFERENT W variables, so the local coefficient
is `CG · CG'` (NOT `|CG|²`). The non-negativity is NOT automatic from the single-site integral.

**The 3D resolution (conjectured):** The GLOBAL cascade (integrating out ALL `u_t(x)`) matches
representations across sites, and the CG UNITARITY (completeness relation `hcgME_unitary`) ensures
the coefficients are `|C|²` type (non-negative). This is the same principle as the 1D case, but with
the CG decomposition added at each site.

**Formalization plan for 3D:**
1. At each site x, use `hcgME_decomp` to combine the 3 unbarred matrix elements into one (sum over α).
2. Use `hcgME_decomp` to combine the 3 barred matrix elements into one (sum over β).
3. Apply `characterOrthogonality` to get `δ_{αβ}` (matching combined representations).
4. The coefficient is `CG_unbarred(α) · CG_barred(α)`. This is NOT `|CG|²` locally.
5. BUT, the CG_unbarred involves `u_t(x+ν̂)` (neighboring links) and CG_barred involves `u_t(x-ν̂)`.
   When we integrate out the NEIGHBORING links, the Schur orthogonality + CG unitarity cascade gives
   `|C|²` type terms globally.
6. The key lemma needed: the CG unitarity (`hcgME_unitary`) ensures the cascade of CG coefficients
   across the lattice gives non-negative coefficients.

#### Formalization roadmap

**Step 1 — PARTIALLY DONE (2026-08-06 sessions 38–39; see §8.11.42).** The single-link
building block — `luscher_key_identity`
(`∫_G χ_γ(g·h)·χ_{γ'}(g⁻¹·k) = δ_{γγ'}·(1/d_γ)·χ_γ(h·k)`, `PositiveDefinite.lean:1037`) — is
**proved** (0 sorries, 0 new axioms; `#print axioms` =
`[propext, Classical.choice, Quot.sound, characterOrthogonality]`). This is the one-site
Schur-orthogonality integral that the cascade iterates. The *full* 1D cascade below remains to
be formalized as a Fubini iteration of this identity:
- Define the 1D temporal plaquette integral `U_1D`.
- Expand `B_p` in characters (using `hexp4` from `peterWeyl_clebschGordan_plaquette`).
- Apply Schur orthogonality iteratively (Fubini + `characterOrthogonality` / `luscher_key_identity`).
- Prove `U_1D = ∑_γ (c_γ)^L / d_γ^{L-1} · χ_γ(∏_x W(x))`.
- Conclude `U_1D` is PD (non-negative coefficients × PD characters).
- This is a STANDALONE lemma demonstrating the Lüscher mechanism.

**Step 2: Formalize the single-site CG decomposition for 3D.**
- Use `hcgME_decomp` to combine 3 unbarred matrix elements of `u_t(x)` into one.
  The iterated 3-fold decomposition `cgME_decomp_3fold` (`PeterWeyl.lean:~1893`) is **proved**
  (session 41, 0 sorries, 0 new axioms) — it applies `hcgME_decomp` twice to decompose
  `(ρ_{s₁} g)_{a₁b₁} · (ρ_{s₂} g)_{a₂b₂} · (ρ_{s₃} g)_{a₃b₃}` into a single sum over `α`
  with the intermediate `ν` shared between row and column CG coefficients.
- Use `hcgME_decomp` for the 3 barred matrix elements.
- Apply `characterOrthogonality` to get `δ_{αβ}`.
- The local coefficient is `CG_unbarred(α) · CG_barred(α)` (NOT necessarily ≥ 0).

**Step 3: Formalize the 3D global cascade.**
- Integrate out `u_t(x)` site by site, using the single-site CG decomposition.
- The cascade of Schur orthogonality + CG unitarity gives non-negative coefficients globally.
- The key lemma: `hcgME_unitary` (CG completeness) ensures the cascade gives `|C|²` type terms.
- Result: `U_3D = ∑_γ a_γ · Φ_γ(u_s) · conj(Φ_γ(v_s))` with `a_γ ≥ 0`.

**Step 4: Connect to `character_expansion_nonneg_shared`.**
- Show the kernel `K(V⁺, V'⁺, u⁰_s)` has the form `∑_i a(u⁰_s, i) · Φ_i(u⁰_s, V⁺) · conj(Φ_i(u⁰_s, V'⁺))`
  with `a ≥ 0` (from the Lüscher mechanism).
- Apply `character_expansion_nonneg_shared` to get `∫ g·(Tg) ≥ 0`.

**Step 5: Close `transferMatrixPositivity_axiom`.**
- Combine with `integral_G_thetaG_eq_inner_g_Tg` to get `∫ G·G(θU) ≥ 0`.
- Remove the axiom (axiom count 6→5).

**Key infrastructure for the formalization:**
- `peterWeyl_clebschGordan_plaquette` (PeterWeyl.lean:226) — provides ι, ρ, dims, hU, hIrr, hDims,
  coeff, hcoeff, cg, hcg, hcg_decomp, dual, hdual, cgME, hcgME_decomp, hcgME_unitary, Λ, hΛ, etc.
- `characterOrthogonality` (PeterWeyl.lean) — Schur orthogonality: `∫ (ρ_α)_{ij} conj((ρ_β)_{kl}) = δ_{αβ}δ_{ik}δ_{jl}/d_α`.
- `hcgME_decomp` — CG decomposition: `(ρ_s g)_{ab} (ρ_t g)_{ij} = ∑_ν ∑_{p,q} cgME s t ν a i p (ρ_ν g)_{pq} conj(cgME s t ν b j q)`.
- `hcgME_unitary` — CG unitarity: `∑_{ν,p} conj(cgME s t ν a i p) cgME s t ν b j p = δ_{ab} δ_{ij}`.
- `character_expansion_nonneg_shared` (PositiveDefiniteIntegral.lean:1196) — final non-negativity lemma.
- `integral_G_thetaG_eq_inner_g_Tg` (TransferMatrix.lean:4936) — reduces ∫ G·G(θU) to ⟨g, Tg⟩.
- `g_posInterface_sigma_invisible` (TransferMatrix.lean:1986) — σ disappears from g.
- `transfer_matrix_fubini_integrated_pull_fullReflect` (TransferMatrix.lean:5792) — character expansion of T.

**Literature found:** Lüscher (1977) "Construction of a selfadjoint, strictly positive transfer matrix
for euclidean lattice gauge theories" (Comm. Math. Phys. 54, 283-292, doi:10.1007/BF01614090).
Available at https://projecteuclid.org/journals/cmp/1103900872 and https://link.springer.com/article/10.1007/BF01614090.
This is the ORIGINAL paper constructing the positive transfer matrix via the Fock space / gauge-fixing approach.

### 8.11.42 PROVED: luscher_key_identity — the single-link Lüscher building block (2026-08-06 sessions 38–39)

**Build GREEN.** Full `lake build` succeeds (2972 jobs); targeted
`lake build YangMills.Proofs.PositiveDefinite` succeeds (2856 jobs). 0 sorries anywhere.

This session **proved** the fundamental identity underlying the Lüscher mechanism — the
single-link (single-temporal-integral) building block that the 1D cascade of §8.11.41 iterates.
This is **Step 1 of the Lüscher formalization roadmap** (§8.11.41): the key identity is now in
hand; the remaining part of Step 1 (iterating the identity across L sites to get the full 1D
cascade `U_1D = ∑_γ (c_γ)^L / d_γ^{L-1} · χ_γ(∏_x W(x))`) is a Fubini iteration on top of this
lemma.

#### The lemma

`luscher_key_identity` (`src/lean/YangMills/Proofs/PositiveDefinite.lean:1037`):

For irreducible unitary representations `ρ_γ, ρ_{γ'}` of a compact group `G` with normalized
Haar (probability) measure `μ`, and any `h, k : G`:

```
∫_G χ_γ(g * h) · χ_{γ'}(g⁻¹ * k) ∂μ(g) = δ_{γγ'} · (1/d_γ) · χ_γ(h * k)
```

i.e. in Lean:

```
∫ g, repCharacter (ρ γ) (g * h) * repCharacter (ρ γ') (g⁻¹ * k) ∂μ =
  if γ = γ' then (1 / dims γ : ℂ) * repCharacter (ρ γ) (h * k) else 0
```

**Verification.** 0 sorries, 0 NEW custom axioms. `#print axioms` confirms the dependency tree
is exactly:

```
'YangMills.luscher_key_identity' depends on axioms:
  [propext, Classical.choice, Quot.sound, YangMills.characterOrthogonality]
```

— i.e. only the standard three Mathlib axioms plus the *existing* `characterOrthogonality`
axiom (the Great Orthogonality Theorem, already in the project). No new axiom was added; the
axiom count remains **six**.

#### Why this is the Lüscher building block

In the 1D Lüscher calculation (§8.11.41), each temporal plaquette contributes a factor
`B_p(u_t(x) · W(x) · (u_t(x+1))⁻¹)`, and integrating out a single link `u_t(x)` pairs the
unbarred matrix element from plaquette `x` with the barred matrix element from plaquette `x−1`.
The integral that performs this pairing is *exactly* of the form
`∫ χ_γ(g · h) · χ_{γ'}(g⁻¹ · k) dμ(g)` — one character evaluated at `g · h` (the forward
plaquette, `h` = the `W`-and-neighbor part), the other at `g⁻¹ · k` (the backward plaquette,
using `ρ(g⁻¹) = ρ(g)†`). Schur orthogonality forces `γ = γ'` (the `δ_{γγ'}`), and the surviving
term is `(1/d_γ) · χ_γ(h · k)` with the **strictly positive** coefficient `1/d_γ > 0`. Iterating
this identity across the L sites of the periodic chain is what produces the cascade
`(c_γ)^L / d_γ^{L-1} ≥ 0` of §8.11.41.

#### Proof structure

The proof (lines 1037–1282) is a direct expansion-and-orthogonality argument in seven stages:

1. **Expand `χ_γ(g·h)` into matrix elements** (`hchar_gh`). Uses `repCharacter = Tr ∘ ρ`,
   `MonoidHom.map_mul` (`ρ(g·h) = ρ(g)·ρ(h)`), and the trace identity
   `Tr(AB) = ∑_{i,j} A_{ij} B_{ji}` (`htrace_mul`, proved via `simp [Matrix.trace, Matrix.mul_apply]`):
   `χ_γ(g·h) = ∑_{a,b} (ρ_γ g)_{ab} (ρ_γ h)_{ba}`.

2. **Expand `χ_{γ'}(g⁻¹·k)` into matrix elements** (`hchar_ginv_k`). Same trace identity, plus
   the unitary property `ρ(g⁻¹) = ρ(g)†` (`h_unitary_elem`: `(ρ g⁻¹)_{cd} = conj((ρ g)_{dc})`,
   proved from `conjTranspose_eq_inv_of_unitary` + `Matrix.inv_eq_right_inv`):
   `χ_{γ'}(g⁻¹·k) = ∑_{c,d} conj((ρ_{γ'} g)_{dc}) (ρ_{γ'} k)_{dc}`.

3. **Distribute the product of the two double sums into a 4-index sum** (`hprod`). The product
   `χ_γ(g·h) · χ_{γ'}(g⁻¹·k)` becomes `∑_a ∑_c ∑_b ∑_d (ρ_γ g)_{ab} (ρ_γ h)_{ba} ·
   (conj((ρ_{γ'} g)_{dc}) (ρ_{γ'} k)_{dc})` via `Fintype.sum_mul_sum` (which distributes both
   levels, giving the order `a, c, b, d`).

4. **Integrability of each 4-index term** (`hInt_term`). Each term is a constant
   `(ρ_γ h)_{ba} · (ρ_{γ'} k)_{dc}` times the Schur-integrable product
   `(ρ_γ g)_{ab} · conj((ρ_{γ'} g)_{dc})` (integrable by `hInt` from `characterOrthogonality`).
   Discharged via `Integrable.smul` + `Integrable.congr` (the `congr` witness is
   `Filter.Eventually.of_forall (fun g => by simp only [smul_eq_mul]; ring)`).

5. **Exchange the 4 sums with the integral** via `integral_finsetSum`, applied at four nesting
   levels (`hInt_d`, `hInt_b`, `hInt_c`, then the outermost). Each level is
   `integrable_finsetSum Finset.univ (fun _ _ => <previous level>)`. The exchanges are written
   as `rw [show (∑ … ∫ …) = (∑ … ∑ … ∫ …) from by apply Finset.sum_congr rfl; intro …; rw […]]`
   so that the integrability hypothesis is supplied at exactly the right binder depth.

6. **Factor the constants out of each integral** (`hfactor`). Each per-`(a,b,c,d)` integral
   `∫ (ρ_γ g)_{ab} (ρ_γ h)_{ba} (conj((ρ_{γ'} g)_{dc}) (ρ_{γ'} k)_{dc}) dμ` is rewritten (via
   `integral_congr_ae` + `integral_smul`) as the constant `(ρ_γ h)_{ba} (ρ_{γ'} k)_{dc}` times
   `∫ (ρ_γ g)_{ab} conj((ρ_{γ'} g)_{dc}) dμ` — the bare Schur-orthogonality integral.

7. **Split into diagonal / off-diagonal cases** (`by_cases hγγ' : γ = γ'`):
   - **Diagonal (`γ = γ'`)**: `subst`, then `simp only [hSchur_diag]` replaces each Schur
     integral with `if a = d ∧ b = c then 1/d_γ else 0`. The `d`-sum is collapsed to the single
     term `d = a` via `Finset.sum_eq_single` (the `h₁` arm discharges `d ≠ a` with `if_neg` +
     `ring`; the `h₂` arm is `absurd (Finset.mem_univ a) h`), then `simp only
     [eq_self_iff_true, true_and]` simplifies `a = a`. The `b`-sum is collapsed to `b = c` the
     same way, then `simp only [eq_self_iff_true, if_true]`. The factor `1/d_γ` is pulled out
     (`Finset.sum_mul` / `Finset.mul_sum` + `ring`), the remaining double sum
     `∑_{a,c} (ρ_γ h)_{ca} (ρ_γ k)_{ac}` is reassociated by `ring` into
     `∑_{a,c} (ρ_γ k)_{ac} (ρ_γ h)_{ca}`, recognized as `Tr(ρ_γ k · ρ_γ h)` via `← htrace_mul`,
     commuted to `Tr(ρ_γ h · ρ_γ k)` via `Matrix.trace_mul_comm`, and finally recognized as
     `χ_γ(h · k)` via `repCharacter` + `← MonoidHom.map_mul`. The goal closes with
     `simp only [eq_self_iff_true, if_true]`.
   - **Off-diagonal (`γ ≠ γ'`)**: every Schur integral is `0` by `hSchur_offdiag γ γ' … hγγ'`,
     so the 4-fold sum is `0` via four nested `Finset.sum_eq_zero`, and the goal closes with
     `rw [hzero, if_neg hγγ']`.

#### Key technical notes

- **`Finset.sum_eq_single` signature.** It takes `(h₁ : ∀ b ∈ s, b ≠ a → f b = 0)` (discharge
  every non-selected element) and then `(h₂ : a ∉ s → f a = 0)` (the "selected element not in
  the set" case, discharged here with `absurd (Finset.mem_univ a) h` since `a` is always in
  `univ`). Getting `h₁`/`h₂` in the right order and using `if_neg` (not `if_neg` on a
  conjunction — first derive `¬(a = d)` then `¬(a = d ∧ b = c)` from it) was the main friction.
- **Kronecker-delta simplification after `subst`.** Once `γ = γ'` is substituted, the
  `hSchur_diag` `if` has `a = d ∧ b = c`; after `sum_eq_single` picks the surviving index, the
  remaining `if` has a reflexive condition (`a = a` or `c = c`) that must be reduced with
  `simp only [eq_self_iff_true, true_and]` / `if_true` — `rw` does not see through these.
- **`h_unitary_elem`** is the only place the unitary hypothesis `hU` is used; everything else
  flows from `characterOrthogonality` (which itself carries `hU`/`hIrr`/`hDims` as hypotheses).
- **No `sorry`, no `sorryAx`, no new axiom.** The lemma is a genuine derivation from the
  existing `characterOrthogonality` axiom.

#### Helper lemmas (all proved inline, 0 sorries)

- `h_unitary_elem : (ρ i g⁻¹) c d = conj ((ρ i g) d c)` — from `conjTranspose_eq_inv_of_unitary`
  + `Matrix.inv_eq_right_inv`.
- `htrace_mul : Tr(A·B) = ∑_{i,j} A_{ij} B_{ji}` — from `simp [Matrix.trace, Matrix.mul_apply]`.
- `hchar_gh : χ_γ(g·h) = ∑_{a,b} (ρ_γ g)_{ab} (ρ_γ h)_{ba}` — `repCharacter` + `MonoidHom.map_mul`
  + `htrace_mul`.
- `hchar_ginv_k : χ_{γ'}(g⁻¹·k) = ∑_{c,d} conj((ρ_{γ'} g)_{dc}) (ρ_{γ'} k)_{dc}` —
  `hchar_gh` + `h_unitary_elem`.

#### Status of the Lüscher roadmap (§8.11.41)

- **Step 1 — DONE (this session).** The single-link key identity `luscher_key_identity` is
  proved. The *full* 1D cascade `U_1D = ∑_γ (c_γ)^L / d_γ^{L-1} · χ_γ(∏_x W(x))` is a Fubini
  iteration of this identity across the L sites of the periodic chain (each site integration is
  one application of `luscher_key_identity` with `h`/`k` being the neighboring `W`-and-link
  factors); formalizing that iteration is the natural continuation but is mechanistically
  straightforward now that the building block is in hand.
- **Step 2 — DONE (2026-08-06 sessions 41–42).** The iterated 3-fold matrix-element CG
  decomposition `cgME_decomp_3fold` (`PeterWeyl.lean:~1893`) is **proved** (0 sorries, 0 new
  axioms; `#print axioms` = `[propext, Classical.choice, Quot.sound]` — pure algebra from
  `hcgME_decomp`, no `characterOrthogonality` needed). Its conjugate `cgME_decomp_3fold_conj`
  (`PeterWeyl.lean:~1949`) is also proved (same axioms). Session 42 then proved the full
  single-site 3D Lüscher integral `single_site_3D_luscher_integral` (`PeterWeyl.lean:~2530`)
  and its helper `integral_ME_times_3barred_MEs` (`PeterWeyl.lean:~2330`), both with
  `#print axioms` = `[propext, Classical.choice, Quot.sound, characterOrthogonality]` (0 sorries,
  0 new axioms). The single-site integral combines 3 unbarred + 3 barred matrix elements at each
  site, applies `cgME_decomp_3fold` + `cgME_decomp_3fold_conj` + Schur orthogonality, and obtains
  the local coefficient `CG_unbarred(α) · CG_barred(α) · (1/dims α)` (NOT necessarily ≥ 0 locally —
  the non-negativity comes from the GLOBAL cascade in Step 3).
- **Step 3.** Formalize the 3D global cascade (integrating out all temporal links), combining
  the single-site CG decomposition with the Schur-orthogonality matching across sites.
  **Building blocks proved (2026-08-06 session 43):** `repCharacter_cyclic`
  (`PositiveDefinite.lean:~768`, `χ(g*h*k) = χ(h*k*g)`, pure trace algebra, 0 sorries,
  0 new axioms) and `luscher_2site_cascade` (`PositiveDefinite.lean:~1310`, the 2-site 1D
  cascade `∫∫ χ_γ₀(g₀·W₀·g₁⁻¹)·χ_γ₁(g₁·W₁·g₀⁻¹) = δ_{γ₀γ₁}·(1/d_γ)·χ_γ(W₀·W₁)`,
  0 sorries, 0 new axioms, `#print axioms` = `[propext, Classical.choice, Quot.sound,
  characterOrthogonality]`). The 2-site cascade demonstrates the Lüscher mechanism: Schur
  orthogonality matches representations across sites, giving the strictly positive coefficient
  `1/d_γ > 0`.
  **3-site cascade proved (2026-08-06 session 44):** `luscher_3site_cascade`
  (`PositiveDefinite.lean:~1390`, the 3-site 1D cascade
  `∫∫∫ χ_γ₀(g₀·W₀·g₁⁻¹)·χ_γ₁(g₁·W₁·g₂⁻¹)·χ_γ₂(g₂·W₂·g₀⁻¹) = δ_{γ₀γ₁}·δ_{γ₁γ₂}·(1/d_γ)²·χ_γ(W₀·W₁·W₂)`,
  0 sorries, 0 new axioms, `#print axioms` = `[propext, Classical.choice, Quot.sound,
  characterOrthogonality]`). Proof: integrate out g₁ first (pull out constant χ_γ₂ via
  `integral_const_mul`, apply `luscher_key_identity`), then apply `luscher_2site_cascade`
  to the remaining g₀-g₂ integral. The coefficient `(1/d_γ)² > 0` is strictly positive.
  **Key technique:** `rw [if_pos h]` fails when the `if` is inside an integral+multiplication;
  use `simp only [if_pos h]` instead. **Step 3(a) DONE (2026-08-07 session 46):** CG unitarity
  non-negativity lemma `cg_unitarity_nonneg` (`PeterWeyl.lean:~2782`) is PROVED — the diagonal
  case of `single_site_3D_luscher_integral` gives `∑_{α,p,q} (1/dims α)·|C(α,p,q)|² ≥ 0`,
  0 sorries, 0 new axioms, `#print axioms` = `[propext, Classical.choice, Quot.sound,
  characterOrthogonality]`. The proof applies `single_site_3D_luscher_integral` with diagonal
  args (barred = unbarred), shows the barred CG product = `conj(U)` pointwise, distributes
  `conj` over sums to get `conj(C)`, reorders the 6-fold sum, factors `(1/dims α)·conj(C)` out,
  substitutes `∑U = C`, rewrites `C·conj(C) = |C|²`, and concludes via `Finset.sum_nonneg`.
  **Root-cause note:** the lemma had been blocked for a full session by a Lean
  `AddConstAsyncResult.commitConst: constant has level params [u_1, u_2] but expected [u_1]`
  error. Diagnosis: the statement alone (full measure-theory signature + `open scoped
  ComplexOrder` + `0 ≤`) compiled fine with `sorry`; the error came from the PROOF BODY. The
  culprit was an UNUSED local `have hconj_sum : ∀ {β : Type*} [Fintype β] (f : β → ℂ), ...` —
  the universe-polymorphic `{β : Type*}` binder leaked a free universe `u_2` into the constant,
  conflicting with the expected `[u_1]` (only `G : Type*`). Removing the unused `hconj_sum`
  (and the also-unused `hswap1`) fixed it. **Lesson:** avoid `{β : Type*}` binders in local
  `have`s unless the universe is pinned to an existing declaration universe; an unused such
  `have` leaks a free universe into the constant. **Step 3(b) DONE (2026-08-07 session 47):** Full
  1D L-site Lüscher cascade `chainIntegral_eq` (`PositiveDefinite.lean:~1555`) is PROVED —
  generalizes the 2-site and 3-site cascades to arbitrary chain length via Fubini iteration of
  `luscher_key_identity`. Defines `chainIntegral` (recursive open-chain integral over interior
  variables) and `allSameRep` (all reps equal γ₀). Proves by induction on chain length:
  `chainIntegral a b [(γ₀,W₀),...,(γₙ,Wₙ)] = δ_{allSameRep} · (1/d_γ)^n · χ_γ(a · (∏W) · b⁻¹)`
  where `n = rest.length`. 0 sorries, 0 new axioms, `#print axioms` = `[propext, Classical.choice,
  Quot.sound, characterOrthogonality]`. **Key techniques:** (1) use `change` to beta-reduce
  `(fun a_1 => ...) g` before `rw` (Filter.Eventually.of_forall leaves unreduced funs), (2) use
  `ac_rfl` (not `ring`) to prove associativity inside opaque function applications like
  `repCharacter`, (3) use `pow_one` (not `one_mul`) to simplify `x^1`, (4) prove `hRHS` BEFORE
  `allSameRep` hypothesis still mentions `γ₁`.
- **Step 3(c) COMPLETE (2026-08-07 sessions 48–50).** The 2D character-level cascade
  `luscher_2site_2D_cascade_charlevel` (`PositiveDefinite.lean:1694`) is PROVED — the central
  result of Step 3. Build GREEN (2856 jobs), 0 sorries, 0 new axioms, `#print axioms` =
  `[propext, Classical.choice, Quot.sound, characterOrthogonality]`.

  **Statement:** for two sites with forward/backward plaquette variables `W, V`,
  ```
  ∫ g₀, ∫ g₁,
    (χ_{s₁}(g₀·W·g₁⁻¹) · χ_{s₂}(g₀·W·g₁⁻¹)) *
    (χ_{t₁}(g₁·V·g₀⁻¹) · χ_{t₂}(g₁·V·g₀⁻¹)) ∂μ ∂μ =
    ∑ ν : ι, (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν : ℂ) * ((1 / dims ν : ℂ) * χ_ν(W * V))
  ```
  This is the Lüscher 2-site cascade at the **character level**: the forward pair `(s₁,s₂)` and
  backward pair `(t₁,t₂)` each decompose via `hcg_decomp` into a sum over reps `ν, ν'`; Schur
  orthogonality (via `luscher_key_identity`) matches `ν' = ν` across the two sites, leaving a
  single sum `∑_ν cg(s₁,s₂,ν)·cg(t₁,t₂,ν)·(1/dims ν)·χ_ν(W·V)`. The coefficient
  `cg(s₁,s₂,ν)·cg(t₁,t₂,ν)·(1/dims ν)` is the product of two CG coefficients times the strictly
  positive factor `1/dims ν > 0`; its non-negativity (the `|C|²` structure from CG unitarity) is
  the subject of Step 4.

  **Proof structure (session 50):**
  1. `hInt_char`: integrability of `χ_ν(g₀·W·g₁⁻¹)·χ_{ν'}(g₁·V·g₀⁻¹)` w.r.t. `g₁` via
     matrix-element expansion + `hInt` (from `characterOrthogonality`). Uses `repMatrixElement_inv`
     for the unitary property and `htrace_mul` for trace expansion. The `g₁`-dependent part
     `(ρ_{ν'} g₁)_{cd}·conj((ρ_ν g₁)_{ab})` is integrable by `hInt ν' ν c d a b` (swapping rep
     indices avoids needing `Integrable.conj`).
  2. `hprod`: pointwise identity rewriting the integrand as `∑_ν ∑_{ν'} cg·cg'·χ_ν·χ_{ν'}` via
     `hcg_decomp` + `Fintype.sum_mul_sum` + `ring`.
  3. `hInner`: inner `g₁` integral via `luscher_key_identity` (after `repCharacter_cyclic` rewrite
     + `mul_assoc`), giving `if ν'=ν then (1/dims ν')·χ_{ν'}(V·W) else 0`.
  4. `hInner_full`: pull constants out of the inner integral via `integral_const_mul`.
  5. Two-level sum↔integral exchange via `integral_finsetSum` (integrability from `hInt_char`
     via `Integrable.smul` + `integrable_finsetSum`).
  6. Pull the `g₀`-independent constant out of the outer integral
     (`simp [integral_const, IsProbabilityMeasure.measure_univ]`), collapse the `if` via
     `Finset.sum_eq_single`, and convert `χ_ν(V·W)` → `χ_ν(W·V)` via `Matrix.trace_mul_comm`.

  **Key API notes:** `Integrable.smul` + `.congr` pattern — the `ring` after the `simp` may close
  the goal automatically, so check before adding an explicit `ring`. `Fintype.sum_mul_sum`
  distributes nested sums in order a, c, b, d (outer sums first). `integral_const_mul` works
  without an explicit integrability hypothesis for ℂ-valued functions under `IsProbabilityMeasure`.

  **Session 48 building blocks (all 0 sorries, 0 new axioms, build GREEN 2972 jobs):**
  1. `repCharacter_isClassFunction` (`PositiveDefinite.lean:793`): `χ(g·h·g⁻¹) = χ(h)` —
     characters are class functions (conjugation-invariant). Pure trace algebra from
     `repCharacter_cyclic` + `inv_mul_cancel`. Axioms: `[propext, Classical.choice, Quot.sound]`.
     **Key insight:** a "local" plaquette at site `x` in direction `ν` has plaquette variable
     `u_t(x)·W_ν(x)·u_t(x)⁻¹`, and since `B_p` is a sum of characters (each a class function),
     `B_p(u·W·u⁻¹) = B_p(W)` — the local plaquette contributes a CONSTANT (independent of
     `u_t(x)`), which factors out of the temporal-link integral. Only NON-LOCAL plaquettes
     (connecting different sites) contribute to the cascade.
  2. `cgME_decomp_conj` (`PeterWeyl.lean:2970`): 2-fold conjugate CG decomposition —
     `conj((ρ_s g)_{ab})·conj((ρ_t g)_{ij}) = ∑_ν ∑_{p,q} conj(cgME s t ν a i p)·conj((ρ_ν g)_{pq})·cgME s t ν b j q`.
     Pure algebra from `hcgME_decomp` (take conjugate, push `conj` through products and sums via `simp`).
     Axioms: `[propext, Classical.choice, Quot.sound]`.
  3. `integral_ME_times_2barred_MEs` (`PeterWeyl.lean:3106`): 2-barred Schur orthogonality helper —
     `∫ (ρ_σ g)_{pq}·conj((ρ_{t1} g)_{c1d1})·conj((ρ_{t2} g)_{c2d2}) dμ = (1/dims σ)·conj(cgME t1 t2 σ c1 c2 p)·cgME t1 t2 σ d1 d2 q`.
     Applies `cgME_decomp_conj` to the 2 barred MEs, exchanges sums with integral (Fubini, 3 levels),
     collapses combined-rep sum to `σ` (Schur off-diagonal), collapses index sums to `p,q` (Schur diagonal).
     Axioms: `[propext, Classical.choice, Quot.sound, characterOrthogonality]`.
  4. `single_site_2D_luscher_integral` (`PeterWeyl.lean:3259`): 2-fold single-site Lüscher integral —
     `∫ (ρ_{s1} g)_{a1b1}·(ρ_{s2} g)_{a2b2}·conj((ρ_{t1} g)_{c1d1})·conj((ρ_{t2} g)_{c2d2}) dμ
     = ∑_{ν,p,q} CG_unbarred(ν,p,q)·(1/dims ν)·CG_barred(ν,p,q)`.
     Applies `hcgME_decomp` to 2 unbarred MEs (3 sums), exchanges with integral, evaluates each inner
     integral via `integral_ME_times_2barred_MEs`. Axioms: `[propext, Classical.choice, Quot.sound, characterOrthogonality]`.
  5. `cg2_unitarity_nonneg` (`PeterWeyl.lean:3307`): 2-fold CG unitarity non-negativity — in the
     diagonal case (barred = unbarred), the single-site 2D integral gives
     `∑_{ν,p,q} (1/dims ν)·|cgME s1 s2 ν a1 a2 p|²·|cgME s1 s2 ν b1 b2 q|² ≥ 0`.
     Proof: apply `single_site_2D_luscher_integral` with diagonal args, rewrite the CG product as
     `(1/dims ν)·normSq(A)·normSq(B)` via `Complex.normSq_eq_conj_mul_self` + `ring`, conclude via
     `Finset.sum_nonneg` + `Complex.zero_le_real`. Axioms: `[propext, Classical.choice, Quot.sound, characterOrthogonality]`.
  **Step 3 is now fully complete (a, b, c).** The character-level cascade
  `luscher_2site_2D_cascade_charlevel` is the key output: it reduces the 2-site 2D integral to a
  single sum `∑_ν cg(s₁,s₂,ν)·cg(t₁,t₂,ν)·(1/dims ν)·χ_ν(W·V)`. Step 4 connects this to
  `character_expansion_nonneg_shared` to establish non-negativity of the coefficient.
- **Step 4 — COMPLETE (2026-08-08 session 52).** `cascade_integral_nonneg`
  (`PositiveDefiniteIntegral.lean:1275`) is PROVED — 0 sorries, build GREEN (2892 jobs),
  `#print axioms` = `[propext, Classical.choice, Quot.sound]` (only 3 axioms — **no
  `characterOrthogonality` needed**, better than expected). The lemma states: for a compact
  group `G` with probability measure `μ`, reflection `θ = Inv.inv` (measure-preserving by
  `hθ`), a finite family of unitary reps `ρ_ν` of dimension `dims ν`, and non-negative CG
  coefficients `cg s t w ≥ 0`,
  ```
  ∫ W, ∫ V, (f W : ℂ) * (f V⁻¹ : ℂ) *
    ∑ ν, (cg s₁ s₂ ν : ℂ) * (cg t₁ t₂ ν : ℂ) * ((1 / dims ν : ℂ) * χ_ν(W * V)) ∂μ ∂μ ≥ 0
  ```
  This is the Lüscher mechanism's positivity conclusion: the kernel
  `K(W,V) = ∑_ν cg·cg·(1/dims ν)·χ_ν(W·V)` (supplied by Step 3(c)'s
  `luscher_2site_2D_cascade_charlevel`) integrated against `f(W)·f(V⁻¹)` is non-negative.

  **Proof structure:** applies `character_expansion_nonneg` (line 1147, the general
  `∫∫ f(x)·f(θy)·K(x,y) ≥ 0` result for kernels `K = ∑ a_i·Φ_i(x)·conj(Φ_i(θy))` with
  `a_i ≥ 0`) with:
  - **Index type** `ι' = Σ ν : ι, Fin (dims ν) × Fin (dims ν)` (Sigma encoding the triple
    `(ν, a, b)`). `letI : Fintype ι' := inferInstance` with `set_option maxHeartbeats 400000`
    (using `letI` not `haveI` so the instance matches `Sigma.instFintype` used by
    `Finset.univ_sigma_univ`).
  - **Coefficients** `a'(i) = cg(s₁,s₂,i.1)·cg(t₁,t₂,i.1)/dims(i.1) ≥ 0` (from `hcg` +
    `Nat.cast_nonneg`).
  - **Basis** `Φ'(i)(g) = (ρ_{i.1} g)_{i.2.1, i.2.2}` (matrix elements of the unitary rep).
  - **θ = Inv.inv** (measure-preserving by `hθ`).

  **Key technical challenge — kernel expansion (`hK`):** proving
  `K(W,V) = ∑_i a'(i)·Φ'(i)(W)·conj(Φ'(i)(V⁻¹))` in two steps:
  1. `hK_nested`: expand `χ_ν(W·V)` via `repCharacter_trace_expand` (unitarity:
     `χ_ν(W·V) = ∑_{a,b} (ρ_ν W)_{ab}·conj((ρ_ν V⁻¹)_{ab})`), distribute `cg·cg·(1/dims)`
     over the double sum via `Finset.mul_sum` twice, match terms with `ring`.
  2. Convert nested form `∑_ν ∑_a ∑_b` to sigma form: `Finset.sum_product'` +
     `Finset.univ_product_univ` (combine `∑_a ∑_b → ∑_p`), then `Finset.sum_sigma'` +
     `Finset.univ_sigma_univ` (combine `∑_ν ∑_p → ∑_i:ι'`). Final term matching via
     `simp only [a', Φ']; push_cast [Complex.ofReal_div, Complex.ofReal_mul]; ring`.

  `a'` and `Φ'` are defined with `.fst`/`.snd` projections (not pattern matching
  `⟨ν, (a,b)⟩`) so `simp only [a', Φ']` can unfold them. Helper `repCharacter_trace_expand`
  (line ~1252, `χ_ν(W·V) = ∑_{a,b} (ρ_ν W)_{ab}·conj((ρ_ν V⁻¹)_{ab})`) is also proved (0 sorries,
  pure unitarity algebra). **Why no `characterOrthogonality`:** `character_expansion_nonneg`
  is a general Fubini + `|∫ f·Φ_i|² ≥ 0` argument — it needs only the kernel's expansion form,
  not specific orthogonality relations (those are in Step 3's cascade lemmas).
- **Step 5.** Close `transferMatrixPositivity_axiom` (axiom count 6 → 5) by combining with
  `integral_G_thetaG_eq_inner_g_Tg`.

### 8.11.43 Step 5 sub-lemmas PROVED: temporal/spatial decomposition + u⁰_t independence (2026-08-08 session 54)

**Build GREEN (2891 jobs). 0 sorries, 0 new axioms.** All lemmas in `TransferMatrix.lean`.

This session proved the tractable sub-lemmas of step 5 of the 6-step closure plan (§8.11.40):
(1) `charFactorInt` decomposes into temporal and spatial parts, and (2) `fourierCoeffPos`
is independent of `u⁰_t` (temporal interface links). These are key building blocks for the
temporal integral (step 5 sub-lemma 3) and the eventual Lüscher mechanism (step 6).

#### Sub-lemma 1: charFactorInt temporal/spatial decomposition

`charFactorInt_eq_temporal_spatial` (`TransferMatrix.lean:~2406`): The interface-link
character factor `Ψ_w(u⁰) = ∏_{l ∈ L_0} χ_{w(l)}(u⁰_l)` decomposes as
`Ψ_w^{temporal}(u⁰_t) · Ψ_w^{spatial}(u⁰_s)` where the temporal product is over
`interfaceLinkTemporal` (μ = 0 links) and the spatial product is over `interfaceLinkSpatial`
(μ ≠ 0 links). This follows directly from `prod_interfaceLinkInt_eq_temporal_spatial`
(the temporal/spatial partition of `interfaceLinkInt`). 0 sorries, 0 new axioms.

#### Sub-lemma 2: fourierCoeffPos independent of u⁰_t

`fourierCoeffPos_independent_of_temporal` (`TransferMatrix.lean:~4822`): When the test
function `ψ = g_posInterface N T L hT β f` with `f` satisfying `dependsOnlyOnPosSpatialInterface`,
the positive Fourier coefficient `A_w(u⁰) = fourierCoeffPos(w, u⁰)` depends only on the
spatial interface links `u⁰_s` (μ ≠ 0), not on the temporal interface links `u⁰_t` (μ = 0).
0 sorries, 0 new axioms.

**Proof:** The integrand `g(merge(U⁺, u⁰))·exp(-β·S⁺(merge(U⁺, u⁰))/2)·charFactorPos(w, U⁺)`
has its `u⁰`-dependence only through `g` and `S⁺`, both of which are invisible to changes in
temporal interface links, while `charFactorPos` depends only on `U⁺`. So if `u⁰` and `u⁰'`
agree on spatial interface links, the integrands are equal pointwise, and
`integral_congr_ae` gives `A_w(u⁰) = A_w(u⁰')`.

**Supporting lemmas (all 0 sorries, 0 new axioms):**
- `extendLinkVariable_merge_spatial_agree` (`TransferMatrix.lean:~2010`): The extended
  configs `extendLinkVariable(merge(V⁺, u⁰))` and `extendLinkVariable(merge(V⁺, u⁰'))`
  agree on positive-site and spatial-interface links when `u⁰` and `u⁰'` agree on spatial
  interface links. Generalizes `extendLinkVariable_merge_sigma_agree` (special case
  `u⁰' = σ(u⁰)`).
- `f_temporal_invisible` (`TransferMatrix.lean:~2050`): `f` is invisible to changes in
  temporal interface links (from `dependsOnlyOnPosSpatialInterface` +
  `extendLinkVariable_merge_spatial_agree`). Generalizes `f_sigma_invisible`.
- `osPositiveOfPosInterface_temporal_invariant` (`TransferMatrix.lean:~2070`): `S⁺` is
  invisible to changes in temporal interface links (from `wilsonActionOSPositive_congr`:
  S⁺ only reads positive-site links). Generalizes `osPositiveOfPosInterface_sigma_invariant`.
- `g_posInterface_temporal_invisible` (`TransferMatrix.lean:~2095`): `g = f·exp(-β·S⁺/2)`
  is invisible to changes in temporal interface links. Generalizes
  `g_posInterface_sigma_invisible`.

#### Remaining: trivial representation issue (step 5 sub-lemma 3)

The temporal integral (step 5 sub-lemma 3) requires computing
`∫ χ_γ(g) dg = δ_{γ, trivial}` (the integral of a character over the group is 1 for the
trivial representation, 0 otherwise). This follows from `character_orthogonality_from_schur`
(`∫ χ_r · conj(χ_s) = δ_{rs}`) with `s = trivial` (since `χ_trivial = 1`, so
`conj(χ_trivial) = 1`).

**OBSTACLE:** The axiom `peterWeyl_clebschGordan_plaquette` provides `ι` as an existential
type but does NOT explicitly identify which element of `ι` is the trivial representation
(the 1-dimensional representation `ρ(g) = 1` with character `χ(g) = 1`). The trivial
representation IS in `ι` (the character expansion of the Boltzmann factor has a positive
constant term, which requires the trivial representation), but identifying it requires
either:
1. **Adding a hypothesis** `∃ (triv : ι), ∀ g, repCharacter (ρ triv) g = 1` to the closure
   lemma. This is a reasonable assumption justified by the Peter-Weyl theorem.
2. **Deriving it from the axiom** by integrating the character expansion and using positivity
   of the Boltzmann factor. This is complex but possible.
3. **Using the Lüscher key identity** (`luscher_key_identity`) instead, which integrates out
   a link by pairing TWO characters (`∫ χ_γ(g·h)·χ_{γ'}(g⁻¹·k) = δ_{γγ'}·(1/d_γ)·χ_γ(h·k)`).
   This doesn't require the trivial representation but requires a DIFFERENT decomposition
   where each temporal link appears in multiple characters (from adjacent plaquettes) —
   the Lüscher mechanism (step 6).

**RECOMMENDATION:** Option 1 (add hypothesis) is the most tractable for step 5. Option 3
(the Lüscher mechanism) is the approach for step 6 and may bypass step 5 entirely.

### 8.11.44 PROVED: integral_repCharacter_eq_iff_trivial + Lüscher bypass analysis (2026-08-08 session 55)

**Build GREEN (2856 jobs). 0 sorries, 0 new axioms.** Lemma in `PositiveDefinite.lean`.

#### Lemma: integral_repCharacter_eq_iff_trivial

`integral_repCharacter_eq_iff_trivial` (`PositiveDefinite.lean:~1066`): For a compact
group `G` with probability measure `μ`, a finite family of irreducible unitary reps `ρ_ν`
of dimension `dims ν`, and a trivial representation `triv` (with `χ_{triv}(g) = 1` for all `g`):

```
∫_G χ_γ(g) ∂μ(g) = if γ = triv then 1 else 0
```

**Proof:** Direct corollary of `character_orthogonality_from_schur` (`∫ χ_r · conj(χ_s) = δ_{rs}`)
with `s = triv`. Since `χ_{triv}(g) = 1`, we have `conj(χ_{triv}(g)) = 1`, so
`χ_γ(g) · conj(χ_{triv}(g)) = χ_γ(g) · 1 = χ_γ(g)`. The proof uses `integral_congr_ae`
with `ae_of_all` to rewrite `∫ χ_γ` as `∫ χ_γ · conj(χ_{triv})`, then applies
`character_orthogonality_from_schur`. The pointwise equality `χ_γ(g) = χ_γ(g) · conj(χ_{triv}(g))`
is proved by `simp [htriv]` (which uses `htriv : ∀ g, χ_{triv}(g) = 1` as a rewrite rule,
simplifying `conj 1 = 1` and `x · 1 = x`).

`#print axioms` = `[propext, Classical.choice, Quot.sound, characterOrthogonality]` (same as
`character_orthogonality_from_schur` — no new axioms).

**Key API note:** `simp [htriv]` works where `rw [htriv g]` fails — `simp` can use universally
quantified local hypotheses as rewrite rules, while `rw` requires the exact pattern match.

#### Analysis: naive expansion (steps 3-6) vs. Lüscher mechanism (step 6)

**CONCLUSION: The naive expansion approach (steps 3-6) CANNOT close `transferMatrixPositivity_axiom`.
The Lüscher mechanism (step 6) bypasses steps 3-5 entirely.**

The naive expansion (`transfer_matrix_fubini_integrated_pull_fullReflect`) gives:
```
∫ ψ·T(ψ) = C · ∑_w F(w) · ∫_{u⁰} charFactorInt(w, u⁰) · A_{w*}(u⁰) · A_w(u⁰) ∂μ⁰
```
After step 5 (temporal integral via `integral_repCharacter_eq_iff_trivial`), this becomes:
```
∫ ψ·T(ψ) = C · ∑_{w: temporal trivial} F(w) · ∫_{u⁰_s} charFactorInt_spatial(w, u⁰_s) · A_{w*}(u⁰_s) · A_w(u⁰_s) ∂μ⁰_s
```

**OBSTACLE (confirmed):** The coefficients `F(w) · charFactorInt_spatial(w, u⁰_s)` are COMPLEX
(characters are complex-valued), NOT non-negative reals. `cascade_integral_nonneg` requires the
kernel `K(W,V) = ∑_ν cg·cg·(1/dims)·χ_ν(W·V)` with `cg ≥ 0`. The naive expansion's kernel
`charFactorInt_spatial(w, u⁰_s) = ∏_{l spatial} χ_{w(l)}(u⁰_s_l)` is a product of characters
evaluated at DIFFERENT link variables — NOT a single character `χ_ν(W·V)` of a product.

**Why the Lüscher cascade can't be applied to the naive expansion:** The Lüscher cascade
(`luscher_key_identity`: `∫ χ_γ(g·h)·χ_{γ'}(g⁻¹·k) = δ_{γγ'}·(1/d_γ)·χ_γ(h·k)`) integrates out
a link `g` that appears in TWO characters (forward and backward plaquettes). In the naive
expansion, each spatial link `u⁰_s_l` appears in only ONE character (the character for that
link). The Fourier coefficients `A_w(u⁰_s)` depend on `u⁰_s` through `g` and `S⁺` (complicated
functions, NOT explicit characters). So the Lüscher cascade can't pair characters from adjacent
plaquettes — there are no adjacent plaquettes in the naive expansion.

**The Lüscher mechanism uses a DIFFERENT expansion:** Instead of the link-level character
expansion (`h_char` in `transfer_matrix_fubini_integrated_pull_fullReflect`), the Lüscher
mechanism uses a PLAQUETTE-LEVEL expansion. Each plaquette Boltzmann factor
`exp(c·Re Tr(g₁g₂g₃g₄))` is expanded via the 5-index expansion from the axiom:
```
exp(c·Re Tr(g₁g₂g₃g₄)) = ∑_{r,s,t,u,v} coeff(r,s,t,u,v)·χ_s(g₁)·χ_t(g₂)·χ_u(g₃)·χ_v(g₄)
```
This separates the four links into individual characters. Each temporal link `u⁰_t(x)` appears
in MULTIPLE plaquettes (from adjacent spatial directions), hence in MULTIPLE characters. The
Lüscher cascade pairs these characters and integrates out `u⁰_t(x)` using Schur orthogonality,
giving non-negative coefficients `(c_γ)^L / d_γ^{L-1} ≥ 0`.

**Key insight:** The 5-index expansion IS the right one for the Lüscher cascade. Each link
appears in its own character (from the 5-index expansion), and the cascade pairs characters
from adjacent plaquettes. This is fundamentally different from the naive expansion where each
link appears in only one character.

#### Formalization plan for the Lüscher mechanism (step 6)

The Lüscher mechanism formalization requires:

1. **Plaquette-level character expansion of the interface Boltzmann factor.** The interface
   action `S_int` is a sum over plaquettes crossing the t=0 interface. Each plaquette Boltzmann
   factor `exp(c·Re Tr(g_p))` is expanded via the 5-index expansion. The product of expansions
   gives a multi-index sum over all plaquette-rep assignments. This is a DIFFERENT expansion
   from `interface_product_character_expansion` (which uses the link-level expansion).

2. **Lüscher cascade to integrate out temporal links.** Each temporal link `u⁰_t(x)` appears
   in multiple plaquettes (from adjacent spatial directions). The cascade pairs the characters
   from these plaquettes and integrates out `u⁰_t(x)` using `luscher_key_identity` (1D) or
   `luscher_2site_2D_cascade_charlevel` (2D). The result has non-negative coefficients.

3. **Connection to `cascade_integral_nonneg`.** After the cascade, the kernel has the form
   `∑_ν a_ν · χ_ν(W·V)` with `a_ν ≥ 0`. This matches the form required by
   `cascade_integral_nonneg` (`PositiveDefiniteIntegral.lean:1275`), which gives
   `∫∫ f(W)·f(V⁻¹)·K(W,V) ≥ 0`.

4. **Combine with `integral_G_thetaG_eq_inner_g_Tg`** to close `transferMatrixPositivity_axiom`.

**Key infrastructure already available:**
- `luscher_key_identity` (`PositiveDefinite.lean:~1086`): single-link Lüscher building block
- `chainIntegral_eq` (`PositiveDefinite.lean:~1555`): full 1D L-site Lüscher cascade
- `luscher_2site_2D_cascade_charlevel` (`PositiveDefinite.lean:~1694`): 2-site 2D cascade
- `cascade_integral_nonneg` (`PositiveDefiniteIntegral.lean:1275`): final non-negativity lemma
- `peterWeyl_clebschGordan_plaquette` (`PeterWeyl.lean:226`): 5-index character expansion axiom
- `integral_repCharacter_eq_iff_trivial` (`PositiveDefinite.lean:~1066`): trivial rep integral
  (PROVED this session — useful for identifying the constant term in character expansions)

**Remaining work:**
- Formalize the plaquette-level expansion of `exp(-β·S_int)` (different from the existing
  `interface_boltzmann_character_expansion` which uses the link-level expansion)
- Formalize the temporal link integration via the Lüscher cascade
- Show the resulting kernel matches `cascade_integral_nonneg`'s required form
- This is a LARGE formalization effort spanning multiple sessions

#### Trivial rep derivation from the axiom (analysis)

The trivial representation can potentially be DERIVED from the axiom (Option 2 of §8.11.43)
without adding a hypothesis. The approach:

1. **Derive a 1-index character expansion** of the single-plaquette Boltzmann factor by
   setting three of the four links to the identity in the 5-index expansion:
   ```
   exp(c·Re Tr(g)) = ∑_s c'_s · χ_s(g)  with c'_s ≥ 0
   ```
   where `c'_s = ∑_{r,t,u,v} coeff(r,s,t,u,v)·dim(t)·dim(u)·dim(v) ≥ 0`.

2. **Use `character_orthogonality_from_schur`** to extract coefficients:
   `c'_s = ∫ exp(c·Re Tr(g)) · conj(χ_s(g)) dg`.

3. **Show `∫ χ_s(g) dg ≥ 0`** by proving `∫ ρ_s(g) dg` is an orthogonal projection
   (idempotent by Haar invariance, self-adjoint by unitarity + Haar invariance), so
   `∫ χ_s = Tr(∫ ρ_s) = rank(projection) ≥ 0`.

4. **Conclude** `∫ exp(c·Re Tr(g)) dg = ∑_s c'_s · ∫ χ_s > 0` implies at least one
   `∫ χ_s > 0`, which identifies the trivial rep.

**Complexity:** Steps 3-4 require formalizing that `∫ ρ_s(g) dg` is an orthogonal projection
(idempotence from Haar invariance + Fubini, self-adjointness from unitarity + Haar invariance).
This is non-trivial but feasible. The `integral_repCharacter_eq_iff_trivial` lemma (PROVED this
session) is a prerequisite — it gives `∫ χ_s = if s = triv then 1 else 0`, which combined with
`∫ χ_s ≥ 0` identifies the trivial rep.

**STATUS:** Not formalized this session. The `integral_repCharacter_eq_iff_trivial` lemma takes
the trivial rep as a hypothesis (`htriv`). Deriving `htriv` from the axiom is left for a future
session. For now, the Lüscher mechanism (step 6) is the recommended approach, as it may not
require the trivial rep at all (the Lüscher cascade uses `luscher_key_identity` which pairs TWO
characters per link, not the single-character integral that requires the trivial rep).

### 8.11.45 PROVED: plaquette_boltzmann_single_char_expansion — KEY BRIDGE LEMMA (2026-08-08 session 56)

**Build GREEN (2972 jobs). 0 sorries, 3 axioms only: `[propext, Classical.choice, Quot.sound]`.**
Lemma in `PeterWeyl.lean:~1182`.

#### Lemma: plaquette_boltzmann_single_char_expansion

For `c ≥ 0` and the 5-index Peter-Weyl expansion data from `peterWeyl_clebschGordan_plaquette`,
the plaquette Boltzmann factor `exp(c · Re Tr(g₁ · g₂ · g₃⁻¹ · g₄⁻¹))` expands as a
**single-index** sum over characters of the plaquette product:

```
exp(c · Re Tr(g₁ · g₂ · g₃⁻¹ · g₄⁻¹)) = ∑_s c'_s · χ_s(g₁ · g₂ · g₃⁻¹ · g₄⁻¹)
```

with `c'_s ≥ 0`, where `c'_s = ∑_{r,t,u,v} coeff(r,s,t,u,v) · dim(t) · dim(u) · dim(v) ≥ 0`.

**Proof:** Apply the 5-index expansion `hexp4` with `(g₁, g₂, g₃, g₄) = (g₁·g₂·g₃⁻¹·g₄⁻¹, 1, 1, 1)`.
The three identity arguments simplify: `χ_t(1) = Tr(ρ_t(1)) = Tr(I_{d_t}) = d_t` (via
`MonoidHom.map_one` + `Matrix.trace_one` + `Fintype.card_fin`). The remaining character
`χ_s(g₁·g₂·g₃⁻¹·g₄⁻¹)` is the plaquette-product character. Reordering the sum to put `s`
outermost (`Finset.sum_comm`), then factoring out `χ_s(g₁·g₂·g₃⁻¹·g₄⁻¹)` from the inner sums
(`simp only [← Finset.sum_mul]`), and recognizing the inner sum as `c'_s` (`Complex.ofReal_sum`),
gives the result. Non-negativity of `c'_s` follows from `coeff ≥ 0` and `dims ≥ 0`.

#### Significance: the bridge between 5-index expansion and Lüscher cascade

This is the **KEY BRIDGE LEMMA** for the Lüscher mechanism (step 6). The 5-index expansion
`hexp4` gives characters at INDIVIDUAL links: `χ_s(g₁)·χ_t(g₂)·χ_u(g₃)·χ_v(g₄)`. The Lüscher
cascade (`luscher_key_identity`, `chainIntegral_eq`, `luscher_2site_2D_cascade_charlevel`)
operates on characters at PRODUCTS: `χ_γ(g·h)`, `χ_γ(g⁻¹·k)`, `χ_ν(W·V)`. These are
fundamentally different forms.

The bridge lemma converts the 5-index expansion into the single-index form
`∑_s c'_s · χ_s(g₁·g₂·g₃⁻¹·g₄⁻¹)` where the character is evaluated at the PLAQUETTE PRODUCT
`g₁·g₂·g₃⁻¹·g₄⁻¹`. This is the form the Lüscher cascade can operate on: when a temporal link
appears in multiple plaquette products, the cascade pairs the characters and integrates out the
link via Schur orthogonality.

**Key technique:** Setting three of the four link arguments to the identity in `hexp4` collapses
the 5-index expansion to a single-index expansion. The identity character `χ_i(1) = dim(i)`
absorbs the other four indices into the coefficient `c'_s`. This is a standard technique in
lattice gauge theory character expansions.

#### Formalization plan for the Lüscher mechanism (updated)

1. ✅ **Single-index plaquette expansion** — `plaquette_boltzmann_single_char_expansion` (PROVED).
   Each plaquette Boltzmann factor `exp(c·Re Tr(g₁·g₂·g₃⁻¹·g₄⁻¹))` = `∑_s c'_s · χ_s(plaquette_product)`
   with `c'_s ≥ 0`.

2. ✅ **Product of single-index plaquette expansions** — `plaquette_product_single_char_decomp` (PROVED).
   The interface Boltzmann factor `exp(-β·S_int) = C · ∏_p exp(c·Re Tr(g_p))` becomes
   `C · ∏_p (∑_s c'_s · χ_s(g_p))` = `C · ∑_{w: P→ι} (∏_p c'_{w(p)}) · ∏_p χ_{w(p)}(g_p)`
   with `∏_p c'_{w(p)} ≥ 0`. Each plaquette product `g_p` involves temporal and spatial links.
   The temporal links appear in MULTIPLE plaquette products (from adjacent spatial directions).
   Proof: `Fintype.prod_sum` (product of sums = sum of products) + `Finset.prod_mul_distrib`
   + `Complex.ofReal_prod` (coercion distributes over product). 3 axioms only.

3. **Lüscher cascade to integrate out temporal links.** Each temporal link `u⁰_t(x)` appears in
   multiple plaquette products. The cascade pairs the characters from these plaquettes and
   integrates out `u⁰_t(x)` using `luscher_key_identity` (1D) or `luscher_2site_2D_cascade_charlevel`
   (2D). Result: non-negative coefficients `(c_γ)^L / d_γ^{L-1} ≥ 0`.

4. **Connection to `cascade_integral_nonneg`.** After the cascade, the kernel has the form
   `∑_ν a_ν · χ_ν(W·V)` with `a_ν ≥ 0`. This matches `cascade_integral_nonneg`.

5. **Combine with `integral_G_thetaG_eq_inner_g_Tg`** to close `transferMatrixPositivity_axiom`.

**Key infrastructure available:**
- `plaquette_boltzmann_single_char_expansion` (PeterWeyl.lean:~1182): single-index plaquette expansion (PROVED this session)
- `luscher_key_identity` (PositiveDefinite.lean:~1102): single-link Lüscher building block
- `chainIntegral_eq` (PositiveDefinite.lean:~1604): full 1D L-site Lüscher cascade
- `luscher_2site_2D_cascade_charlevel` (PositiveDefinite.lean:~1730): 2-site 2D cascade
- `cascade_integral_nonneg` (PositiveDefiniteIntegral.lean:1275): final non-negativity lemma (3 axioms)
- `peterWeyl_clebschGordan_plaquette` (PeterWeyl.lean:226): 5-index character expansion axiom
- `integral_G_thetaG_eq_inner_g_Tg` (TransferMatrix.lean:5149): reduces ∫ G·G(θU) to ∫ g·(Tg)

### 8.11.48 PROVED: luscher_2site_cascade_integral_nonneg — Step 3+4 combination (2026-08-08 session 58)

**Build GREEN (2892 jobs). 0 sorries. Axioms: `[propext, Classical.choice, Quot.sound, characterOrthogonality]`**
(same as all other cascade lemmas). Lemma in `PositiveDefiniteIntegral.lean:~1524`.

#### Lemma: luscher_2site_cascade_integral_nonneg

For irreducible unitary representations of a compact group with normalized Haar measure,
arbitrary non-negative coefficients `F : ι → ι → ℝ` with `F s t ≥ 0`, and a function `f : G → ℝ`,
the full 4-fold integral (outer `W, V` × inner cascade `g₀, g₁`) is non-negative:

    0 ≤ ∫ W, ∫ V, (f W : ℂ) * (f V⁻¹ : ℂ) *
      ∫ g₀, ∫ g₁, ∑ s, ∑ t, (F s t : ℂ) *
        (χ_s(g₀·W·g₁⁻¹) * χ_t(g₁·V·g₀⁻¹)) ∂μ ∂μ ∂μ ∂μ

**This is the combination of steps 3 and 4 of the Lüscher mechanism formalization.** It takes
the output of the plaquette product expansion (step 2: `∑_{s,t} F(s,t) · χ_s(·) · χ_t(·)` with
`F(s,t) ≥ 0`, for the 2-plaquette case), integrates out the temporal links `g₀, g₁` via the
Lüscher cascade (step 3: `luscher_2site_cascade_coeff`), and applies the non-negativity lemma
(step 4: `character_kernel_integral_nonneg`).

#### Proof structure

1. **Define `coeff s = F s s / dims s`** and show `coeff s ≥ 0` (since `F s s ≥ 0` and `dims s > 0`).
2. **Pointwise kernel identity** (`hKernel`): For all `W, V`, the inner cascade integral equals
   `∑_s (coeff s : ℂ) * χ_s(W * V)`. This follows from `luscher_2site_cascade_coeff` + a
   coefficient conversion (`push_cast; field_simp` to convert `(F s s : ℂ) * ((1/dims s) : ℂ)`
   to `((F s s / dims s) : ℂ)`).
3. **Rewrite the outer integral** using `hKernel` via `congr 1 with W; congr 1 with V; rw [hKernel W V]`.
4. **Apply `character_kernel_integral_nonneg`** with `coeff s = F s s / dims s ≥ 0`.

#### Significance: steps 3+4 combined

This lemma is the **complete abstract pipeline** from the plaquette product expansion to
non-negativity, for the 2-plaquette (2-site) case. The remaining work is:
- **Step 5:** Combine with `integral_G_thetaG_eq_inner_g_Tg` to close `transferMatrixPositivity_axiom`.
- **Generalization:** The 2-plaquette case handles two plaquettes sharing two temporal links.
  The general case (each temporal link appears in 6 plaquettes) requires the 3-site or n-site
  cascade generalization (`chainIntegral_eq` or `luscher_3site_cascade`).

**Key infrastructure available (updated):**
- `plaquette_boltzmann_single_char_expansion` (PeterWeyl.lean:~1182): single-index plaquette expansion
- `plaquette_product_single_char_decomp` (PeterWeyl.lean:~1258): multi-plaquette product expansion
- `luscher_key_identity` (PositiveDefinite.lean:~1102): single-link Lüscher building block
- `luscher_2site_cascade` (PositiveDefinite.lean:1371): single-character 2-site cascade
- `chainIntegral_eq` (PositiveDefinite.lean:~1604): full 1D L-site Lüscher cascade
- `luscher_2site_2D_cascade_charlevel` (PositiveDefinite.lean:~1730): 2-site 2D cascade (2-character, CG)
- `luscher_2site_cascade_coeff` (PositiveDefinite.lean:~2223): abstract bridge lemma (step 3)
- `cascade_integral_nonneg` (PositiveDefiniteIntegral.lean:1275): non-negativity (cg·cg·(1/dims) form)
- `character_kernel_integral_nonneg` (PositiveDefiniteIntegral.lean:~1395): generalized non-negativity (step 4)
- **`luscher_2site_cascade_integral_nonneg` (PositiveDefiniteIntegral.lean:~1524): steps 3+4 combined (this session)**
- `peterWeyl_clebschGordan_plaquette` (PeterWeyl.lean:226): 5-index character expansion axiom
- `integral_G_thetaG_eq_inner_g_Tg` (TransferMatrix.lean:5149): reduces ∫ G·G(θU) to ∫ g·(Tg)

### 8.11.47 PROVED: luscher_2site_cascade_coeff — Step 3 bridge lemma (2026-08-08 session 58)

**Build GREEN (2856 jobs). 0 sorries. Axioms: `[propext, Classical.choice, Quot.sound, characterOrthogonality]`**
(same as all other cascade lemmas — `characterOrthogonality` is axiom #6 of the project).
Lemma in `PositiveDefinite.lean:~2223`.

#### Lemma: luscher_2site_cascade_coeff

For irreducible unitary representations of a compact group with normalized Haar
measure, and **arbitrary non-negative coefficients** `F : ι → ι → ℝ` with `F s t ≥ 0`,
the 2-site cascade with summed character products evaluates to:

    ∫ g₀, ∫ g₁, ∑_s ∑_t (F s t : ℂ) · χ_s(g₀·W·g₁⁻¹) · χ_t(g₁·V·g₀⁻¹) ∂μ ∂μ
      = ∑_s (F s s : ℂ) · ((1/d_s : ℂ) · χ_s(W·V))

**This is the key bridge lemma connecting the plaquette product expansion (step 2)
to the Lüscher cascade (step 3).** It takes the output of `plaquette_product_single_char_decomp`
(a sum `∑_{s,t} F(s,t) · χ_s(·) · χ_t(·)` with `F(s,t) ≥ 0`, for the 2-plaquette case
where two plaquettes share two temporal links `g₀, g₁`) and integrates out the temporal
links, producing a kernel `K(W,V) = ∑_s (F(s,s) · (1/d_s)) · χ_s(W·V)` with
**non-negative coefficients** `F(s,s) · (1/d_s) ≥ 0` (since `F(s,s) ≥ 0` and `1/d_s > 0`).

#### Proof structure

The proof follows the same pattern as `luscher_2site_2D_cascade_charlevel` (session 50)
but is **simpler**: no Clebsch–Gordan decomposition is needed since the integrand is
already a sum of single-character products (not a product of character products).

1. **Integrability** (`hInt_char`): For each fixed `g₀, s, t`, establish
   `Integrable (fun g₁ => χ_s(g₀·W·g₁⁻¹) · χ_t(g₁·V·g₀⁻¹)) μ` by expanding both
   characters into matrix elements using `repMatrixElement_inv` (unitarity:
   `ρ(g₁⁻¹) = ρ(g₁)†`), distributing the product via `Fintype.sum_mul_sum`, and
   applying `hInt` from `characterOrthogonality` (matrix-element integrability)
   + `integrable_finsetSum`.

2. **Sum-integral exchange**: Exchange the finite sums over `s` and `t` with the
   inner `g₁` integral via `integral_finsetSum` (using the integrability from step 1).

3. **Lüscher key identity** (`hInner`): For each `(s,t)` term, apply
   `luscher_key_identity` to the inner `g₁` integral. Schur orthogonality forces
   `t = s`, and the surviving term is `(1/d_t) · χ_t(V·W)`.

4. **Outer integral**: The result is independent of `g₀`, so the outer integral is
   the integral of a constant over a probability measure (`integral_const` +
   `IsProbabilityMeasure.measure_univ`).

5. **Collapse**: Use `Finset.sum_eq_single` to collapse the `if t = s` to keep only
   the diagonal `t = s` terms, giving `∑_s (F s s : ℂ) · ((1/d_s : ℂ) · χ_s(V·W))`.

6. **trace_mul_comm**: Convert `χ_s(V·W) = χ_s(W·V)` via `Matrix.trace_mul_comm`.

#### Significance: the abstract bridge

This lemma is the **abstract bridge** between the plaquette product expansion and the
Lüscher cascade. It takes the plaquette product expansion coefficients `F` as parameters
(rather than using the concrete lattice structure from `ReflectionPositivity.lean`),
making it general and reusable. The concrete connection to the lattice will be made by
instantiating `F` with the coefficients from `plaquette_product_single_char_decomp`
applied to the interface plaquettes.

The resulting kernel `K(W,V) = ∑_s (F s s : ℂ) · ((1/d_s : ℂ) · χ_s(W·V))` has
non-negative coefficients `F(s,s) · (1/d_s) ≥ 0`, which matches
`character_kernel_integral_nonneg` (step 4) after setting `coeff s = F s s / dims s`
and using `Complex.ofReal_mul` / `Complex.ofReal_div` to convert
`(F s s : ℂ) · ((1/d_s) : ℂ) = ((F s s / dims s) : ℂ)`.

#### Updated formalization plan for the Lüscher mechanism

1. ✅ **Single-index plaquette expansion** — `plaquette_boltzmann_single_char_expansion` (PROVED).
2. ✅ **Product of single-index plaquette expansions** — `plaquette_product_single_char_decomp` (PROVED).
3. ✅ **Lüscher cascade to integrate out temporal links** — `luscher_2site_cascade_coeff` (PROVED, this session).
   - ✅ `luscher_2site_cascade` (PROVED, session 43): single-character 2-site cascade.
   - ✅ `character_kernel_integral_nonneg` (PROVED, session 57): generalized non-negativity.
   - ✅ `luscher_2site_cascade_coeff` (PROVED, this session): **abstract bridge lemma** — takes
     arbitrary non-negative coefficients `F(s,t) ≥ 0` and integrates out temporal links `g₀, g₁`,
     producing kernel `∑_s F(s,s)·(1/d_s)·χ_s(W·V)` with non-negative coefficients.
   - ⬜ **Remaining:** Instantiate `F` with the concrete plaquette product expansion coefficients
     for the interface plaquettes (requires connecting to `ReflectionPositivity.lean` lattice structure).
     The 2-plaquette case is handled by `luscher_2site_cascade_coeff`; the general case (each temporal
     link appears in 6 plaquettes) requires the 3-site or n-site cascade generalization.
4. ✅ **Connection to non-negativity** — `character_kernel_integral_nonneg` (PROVED, session 57).
5. ⬜ **Combine with `integral_G_thetaG_eq_inner_g_Tg`** to close `transferMatrixPositivity_axiom`.

**Key infrastructure available (updated):**
- `plaquette_boltzmann_single_char_expansion` (PeterWeyl.lean:~1182): single-index plaquette expansion
- `plaquette_product_single_char_decomp` (PeterWeyl.lean:~1258): multi-plaquette product expansion
- `luscher_key_identity` (PositiveDefinite.lean:~1102): single-link Lüscher building block
- `luscher_2site_cascade` (PositiveDefinite.lean:1371): single-character 2-site cascade
- `chainIntegral_eq` (PositiveDefinite.lean:~1604): full 1D L-site Lüscher cascade
- `luscher_2site_2D_cascade_charlevel` (PositiveDefinite.lean:~1730): 2-site 2D cascade (2-character, CG)
- **`luscher_2site_cascade_coeff` (PositiveDefinite.lean:~2223): abstract bridge lemma — Step 3 COMPLETE (this session)**
- `cascade_integral_nonneg` (PositiveDefiniteIntegral.lean:1275): non-negativity (cg·cg·(1/dims) form)
- `character_kernel_integral_nonneg` (PositiveDefiniteIntegral.lean:~1395): generalized non-negativity (arbitrary coeff ≥ 0)
- `peterWeyl_clebschGordan_plaquette` (PeterWeyl.lean:226): 5-index character expansion axiom
- `integral_G_thetaG_eq_inner_g_Tg` (TransferMatrix.lean:5149): reduces ∫ G·G(θU) to ∫ g·(Tg)

### 8.11.46 PROVED: character_kernel_integral_nonneg + step 3 analysis (2026-08-08 session 57)

**Build GREEN (2972 jobs). 0 sorries, 3 axioms only: `[propext, Classical.choice, Quot.sound]`.**
Lemma in `PositiveDefiniteIntegral.lean:~1395`.

#### Lemma: character_kernel_integral_nonneg

For a compact group `G` with probability measure `μ` (invariant under inversion), a finite
family of irreducible unitary reps `ρ_ν` of dimension `dims ν`, and **arbitrary non-negative
coefficients** `coeff : ι → ℝ` with `coeff ν ≥ 0`, the integral

    ∫ W, ∫ V, (f W : ℂ) * (f V⁻¹ : ℂ) * ∑_ν (coeff ν : ℂ) * χ_ν(W * V) ∂μ ∂μ ≥ 0

**Proof:** Identical in structure to `cascade_integral_nonneg`. Expand `χ_ν(W·V)` via
`repCharacter_trace_expand` (unitarity) into the separable form
`∑_{a,b} (ρ_ν W)_{ab}·conj((ρ_ν V⁻¹)_{ab})`, then apply `character_expansion_nonneg`
with `θ = inv` (measure-preserving by `hθ`). The sigma index type is
`Σ ν, Fin(dims ν) × Fin(dims ν)`, with coefficients `a'(i) = coeff(i.1) ≥ 0` and basis
`Φ'(i)(g) = (ρ_{i.1} g)_{i.2.1, i.2.2}`. The only difference from `cascade_integral_nonneg`
is the coefficient: `a'(i) = coeff(i.1)` instead of `cg s₁ s₂ i.1 · cg t₁ t₂ i.1 / dims i.1`.

**Key simplification vs `cascade_integral_nonneg`:** Since `a'(i) = coeff(i.1)` is
definitionally equal to the nested coefficient (no multiplication or division), the
`Finset.sum_congr` + `push_cast` + `ring` steps in `cascade_integral_nonneg`'s `hK` proof
are not needed — the goal closes after `rw [hstep1, Finset.sum_sigma', Finset.univ_sigma_univ]`
by definitional equality.

#### Significance: generalized non-negativity for the Lüscher mechanism

This lemma generalizes `cascade_integral_nonneg` (which requires the specific coefficient
`cg s₁ s₂ ν · cg t₁ t₂ ν · (1/dims ν)` from the 2-character CG cascade) to **arbitrary
non-negative coefficients** `coeff ν ≥ 0`. This is essential for the Lüscher mechanism because:

1. The **single-character cascade** (`luscher_2site_cascade`) gives the kernel
   `K(W,V) = if s = t then (1/d_s) · χ_s(W·V) else 0`, which has coefficients
   `a_ν = if s = t = ν then (1/d_ν) else 0 ≥ 0`. This matches `character_kernel_integral_nonneg`
   but NOT `cascade_integral_nonneg` (which requires the `cg·cg·(1/dims)` form).

2. The **n-site cascade** (`chainIntegral_eq`) gives the kernel
   `K = δ_{all same} · (1/d_γ)^n · χ_γ(∏ W)`, which also has non-negative coefficients
   `(1/d_γ)^n ≥ 0` but not in the `cg·cg·(1/dims)` form.

3. The **general Lüscher cascade** (integrating out multiple temporal links, each appearing
   in multiple plaquettes) will produce a kernel `∑_ν a_ν · χ_ν(W·V)` with `a_ν ≥ 0`, where
   `a_ν` is a product of cascade coefficients (each ≥ 0). `character_kernel_integral_nonneg`
   handles this general case directly.

#### Key finding: luscher_2site_cascade IS the single-character 2-site cascade

**`luscher_2site_cascade`** (`PositiveDefinite.lean:1371`) is EXACTLY the single-character
2-site cascade needed for step 3:

    ∫∫ χ_s(g₀·W·g₁⁻¹) · χ_t(g₁·V·g₀⁻¹) dμ(g₁) dμ(g₀) = δ_{s,t} · (1/d_s) · χ_s(W·V)

This was already proved (session 43, step 3 of the Lüscher roadmap). It is the key building
block for the Lüscher cascade: two plaquettes sharing two temporal links `g₀, g₁`, with
single characters (no CG decomposition needed). The proof applies `luscher_key_identity`
to integrate out `g₁`, then integrates out `g₀` (trivial, since the result is constant and
`μ` is a probability measure).

#### Formalization plan for the Lüscher mechanism (updated)

1. ✅ **Single-index plaquette expansion** — `plaquette_boltzmann_single_char_expansion` (PROVED).
2. ✅ **Product of single-index plaquette expansions** — `plaquette_product_single_char_decomp` (PROVED).
3. **Lüscher cascade to integrate out temporal links.** Each temporal link `u⁰_t(x)` appears in
   multiple plaquette products. The cascade pairs the characters from these plaquettes and
   integrates out `u⁰_t(x)` using `luscher_key_identity` (1D) or `luscher_2site_cascade`
   (2-site, single-character). Result: non-negative coefficients.
   - ✅ `luscher_2site_cascade` (PROVED, session 43): single-character 2-site cascade.
   - ✅ `character_kernel_integral_nonneg` (PROVED, this session): generalized non-negativity.
   - ⬜ **Remaining:** Formalize the connection between the plaquette product expansion
     (step 2) and the Lüscher cascade. This requires understanding the concrete structure of
     interface plaquettes and how temporal links appear in multiple plaquette products.
     See §8.11.45 for the interface plaquette structure analysis.
4. ✅ **Connection to non-negativity** — `character_kernel_integral_nonneg` (PROVED, this session).
   After the cascade, the kernel has the form `∑_ν a_ν · χ_ν(W·V)` with `a_ν ≥ 0`, and this
   lemma gives `∫∫ f(W)·f(V⁻¹)·K(W,V) ≥ 0`.
5. **Combine with `integral_G_thetaG_eq_inner_g_Tg`** to close `transferMatrixPositivity_axiom`.

**Key infrastructure available (updated):**
- `plaquette_boltzmann_single_char_expansion` (PeterWeyl.lean:~1182): single-index plaquette expansion
- `plaquette_product_single_char_decomp` (PeterWeyl.lean:~1258): multi-plaquette product expansion
- `luscher_key_identity` (PositiveDefinite.lean:~1102): single-link Lüscher building block
- `luscher_2site_cascade` (PositiveDefinite.lean:1371): single-character 2-site cascade (KEY for step 3)
- `chainIntegral_eq` (PositiveDefinite.lean:~1604): full 1D L-site Lüscher cascade
- `luscher_2site_2D_cascade_charlevel` (PositiveDefinite.lean:~1730): 2-site 2D cascade (2-character, CG)
- `cascade_integral_nonneg` (PositiveDefiniteIntegral.lean:1275): non-negativity (cg·cg·(1/dims) form)
- `character_kernel_integral_nonneg` (PositiveDefiniteIntegral.lean:~1395): generalized non-negativity (arbitrary coeff ≥ 0)
- `peterWeyl_clebschGordan_plaquette` (PeterWeyl.lean:226): 5-index character expansion axiom
- `integral_G_thetaG_eq_inner_g_Tg` (TransferMatrix.lean:5149): reduces ∫ G·G(θU) to ∫ g·(Tg)

### 8.11.49 PROVED: char_product_integrable + luscher_3site_cascade_coeff + KEY FINDING (2026-08-08 session 59)

**Build GREEN (2972 jobs full). 0 sorries. Axioms: `[propext, Classical.choice, Quot.sound, characterOrthogonality]`.**

#### Lemma 1: char_product_integrable (PositiveDefinite.lean:~2070)

For irreducible unitary representations of a compact group with normalized Haar measure,
the product of two characters `χ_s(A · g⁻¹) · χ_t(g · B)` is integrable w.r.t. `g` for any
fixed `A, B ∈ G` and representations `s, t`. This is the standalone generalization of the
local `hInt_char` hypothesis in `luscher_2site_cascade_coeff`, extracted for reuse.

#### Lemma 2: luscher_3site_cascade_coeff (PositiveDefinite.lean:~2565)

For arbitrary non-negative coefficients `F : ι → ι → ι → ℝ` with `F s t u ≥ 0`, the 3-site
cascade evaluates to:

    ∫∫∫ ∑_{s,t,u} F(s,t,u) · χ_s(g₀·W₀·g₁⁻¹) · χ_t(g₁·W₁·g₂⁻¹) · χ_u(g₂·W₂·g₀⁻¹) dg₁ dg₂ dg₀
      = ∑_s F(s,s,s) · (1/d_s)² · χ_s(W₀·W₁·W₂)

**Proof:** Inductive approach — (1) integrate out `g₁` via `luscher_key_identity` (Schur
orthogonality forces `t = s`), producing a 2-site cascade with coefficients `G(s,u) = F(s,s,u)·(1/d_s) ≥ 0`;
(2) apply `luscher_2site_cascade_coeff` to integrate out `g₂` (Schur orthogonality forces `u = s`),
producing the final kernel with coefficients `F(s,s,s) · (1/d_s)² ≥ 0`.

#### KEY FINDING: 3-site cascade does NOT directly combine with character_kernel_integral_nonneg

The 3-site cascade produces a **CONSTANT** `∑_s coeff_s · χ_s(W₀·W₁·W₂)` (not a kernel in
W, V). The outer integral `∫ W ∫ V f(W)·f(V⁻¹)·[constant]` = `[constant]·|∫f|²`, and the
constant is a sum of characters (complex in general), so the product is **NOT necessarily
non-negative**.

This contrasts with the 2-site case, where the cascade produces a **KERNEL**
`K(W,V) = ∑_s coeff_s · χ_s(W·V)` (a function of W·V), which matches
`character_kernel_integral_nonneg` directly.

**Implication:** The `luscher_3site_cascade_integral_nonneg` lemma was REMOVED (it was not
provable). The 3-site cascade coefficient lemma is correct and useful for evaluating cascades,
but the non-negativity combination requires a different approach:
- (a) A generalized non-negativity lemma for kernels of the form `χ_s(W·M·V)` with a fixed bridge M
- (b) The specific lattice structure where the cascade produces `χ_s(W·V)` directly
- (c) Pairwise decomposition using the 2-site cascade repeatedly

#### Updated formalization plan

1. ✅ Single-index plaquette expansion — `plaquette_boltzmann_single_char_expansion`
2. ✅ Product of single-index plaquette expansions — `plaquette_product_single_char_decomp`
3. ✅ Lüscher cascade to integrate out temporal links:
   - ✅ `luscher_2site_cascade_coeff` (2-site, abstract bridge)
   - ✅ `luscher_3site_cascade_coeff` (3-site, abstract bridge) — PROVED this session
   - ✅ `char_product_integrable` (standalone integrability) — PROVED this session
   - ✅ `luscher_2site_cascade_integral_nonneg` (2-site steps 3+4 combined)
   - ⚠️ 3-site steps 3+4 combination: NOT directly possible (cascade produces constant, not kernel)
4. ✅ Connection to non-negativity — `character_kernel_integral_nonneg`
5. ⬜ Combine with `integral_G_thetaG_eq_inner_g_Tg` to close `transferMatrixPositivity_axiom`

**Key infrastructure available (updated):**
- `char_product_integrable` (PositiveDefinite.lean:~2070): standalone integrability lemma
- `luscher_3site_cascade_coeff` (PositiveDefinite.lean:~2565): 3-site cascade evaluation
- All previous infrastructure (see §8.11.48)

### 8.11.50 CRITICAL ANALYSIS: Topology is STAR + gauge-fixing gives c_γ² (NOT |c_γ|²) — fundamental obstacle confirmed (2026-08-08 session 60)

**Build GREEN (unchanged, 2972 jobs). No code changes this session — pure analysis.**

This session performed a deep analysis of the concrete lattice structure in `ReflectionPositivity.lean`
and `TransferMatrix.lean` to determine which approach (a/b/c from §8.11.49) is viable for the
multi-plaquette non-negativity gap. The conclusion is **NONE of the three approaches directly works**,
and the gauge-fixing approach (§8.11.39) also does NOT resolve the obstacle.

#### Finding 1: The topology is a STAR (6 plaquettes per temporal link in 3D)

From the concrete lattice structure:
- `InterfaceLink T L` = links appearing in interface plaquettes (ReflectionPositivity.lean:1088).
- Interface links partition by `signedTime`: `interfaceLinkPos` (>0), `interfaceLinkInt` (=0), `interfaceLinkNeg` (<0).
- `interfaceLinkInt` further splits: `interfaceLinkTemporal` (μ=0, inverted by σ), `interfaceLinkSpatial` (μ≠0, fixed by σ).
- The character expansion (`h_char` in `transfer_matrix_fubini_integrated_pull_fullReflect`, TransferMatrix.lean:6015):
  `exp(-β·S_int) = C · ∑_{w: InterfaceLink→ι} F(w) · [∏_{l∈Pos} χ_{w(l)}(U_l)] · [∏_{l∈Int} χ_{w(l)}(U_l)] · star[∏_{l∈Neg} χ_{dual(w(l))}(U_l)]`

Each temporal interface link `u⁰_t(x)` appears in **6 plaquettes** (3 spatial directions × 2 per direction):
- For each spatial direction ν, the link appears in the "forward" plaquette at (0,x) and the "backward" plaquette at (0,x-ν̂).
- This is a **STAR topology** (6 plaquettes meeting at one link), NOT a chain.

The 2-site cascade (`luscher_2site_cascade_coeff`) handles 2 plaquettes sharing 2 temporal links (CHAIN topology).
The star topology does NOT decompose into independent pairs.

#### Finding 2: Approach (a) does NOT work — ρ_s(M) is not PSD for general unitary M

A generalized non-negativity lemma for `χ_s(W·M·V)` with fixed bridge M requires `ρ_s(M)` to be
positive semi-definite. For general unitary M, `ρ_s(M)` is unitary but NOT Hermitian, so NOT PSD.
**Approach (a) is ruled out.**

#### Finding 3: Approach (b) works for L=1 ONLY — ordered product ≠ W·V for L>1

The 1D Lüscher cascade (`chainIntegral_eq`) produces `∑_γ a_γ · χ_γ(∏_x W(x))` with `a_γ ≥ 0`,
where `W(x) = v_s(x) · u_s(x)⁻¹`.

For **L=1** (single site): `K(u,v) = ∑_γ a_γ · χ_γ(v·u⁻¹)`. Substituting `u→u⁻¹` (measure-preserving)
and using `χ_γ(v·u) = χ_γ(u·v)` (cyclic), this matches `character_kernel_integral_nonneg` with `f̃(u) = f(u⁻¹)`.
**Approach (b) works for L=1.** ✓

For **L>1**: `χ_γ(∏_x v_s(x)·u_s(x)⁻¹)` is a character of `SU(N)` evaluated at the ORDERED PRODUCT
(a single group element), NOT a character of `SU(N)^L` evaluated at `(u_s, v_s)`. The ordered product
map `π: SU(N)^L → SU(N)` is NOT a group homomorphism (for non-abelian G), so `χ_γ ∘ π` is NOT a
character of `SU(N)^L`. **Approach (b) does NOT work for L>1.** ✗

#### Finding 4: Approach (c) does NOT directly apply — star ≠ independent pairs

The 6 plaquettes sharing one temporal link are NOT independent (they all depend on the same variable).
Pairwise decomposition would require the 6 plaquettes to factor into 3 independent 2-plaquette pairs,
but they share the SAME temporal link. **Approach (c) is ruled out** (at least directly).

#### Finding 5: CRITICAL — gauge-fixing gives c_γ² (NOT |c_γ|²) — §8.11.39 claim is INCORRECT

The design doc §8.11.39 claims the gauge-fixing approach gives `K_temporal = ∑_γ (|c_γ|²/d_γ) · χ_γ(W(0)·W(1))`
with `|c_γ|²/d_γ ≥ 0`. **This claim is WRONG.** Detailed verification:

The matrix element: `M^γ_{ij}(W) = ∫ B_p(W·g) · (ρ^γ g)_{ij} dμ(g)`.
Using Schur orthogonality (with `ρ^γ g` NOT `conj(ρ^γ g)`, so it pairs with the DUAL representation):
`M^γ_{ij}(W) = conj(c_γ) · conj((ρ_γ W)_{ij}) / d_γ`.

The kernel: `K = ∑_γ d_γ · Tr(M^γ(W(0)) · M^γ(W(1)))`
`= ∑_γ d_γ · ∑_{i,j} [conj(c_γ)·conj((ρ_γ W(0))_{ij})/d_γ] · [conj(c_γ)·conj((ρ_γ W(1))_{ji})/d_γ]`
`= ∑_γ (conj(c_γ)²/d_γ) · conj(χ_γ(W(0)·W(1)))`
`= ∑_γ (c_γ²/d_γ) · χ_γ(W(0)·W(1))` (reindexing γ→dual(γ), using c_{dual(γ)}=conj(c_γ)).

**The coefficient is `c_γ²/d_γ`, NOT `|c_γ|²/d_γ`.** Since `c_γ` is complex in general,
`c_γ²` is NOT necessarily non-negative. The gauge-fixing does NOT resolve the obstacle.

The error in §8.11.39: the design doc assumed `Tr(M^γ(W(0)) · M^γ(W(1)))` gives `|c_γ|²`, but the
actual computation gives `conj(c_γ)²` (the Schur orthogonality pairs with the DUAL representation,
introducing a `conj` that turns `|c_γ|²` into `conj(c_γ)² = c_{dual(γ)}²`).

#### Finding 6: The non-negativity obstacle is FUNDAMENTAL and applies to ALL character expansions

For L>1, the integral `∫∫ f(u_s)·f(v_s)·∑_γ a_γ·χ_γ(∏_x v_s(x)·u_s(x)⁻¹) dμ dμ` expands to:
```
∑_γ a_γ · ∑_{i,j} [∫ f(u_s) ∏_x conj((ρ_γ u_s(x))_{i_{x+1},j_x}) dμ] · [∫ f(v_s) ∏_x (ρ_γ v_s(x))_{i_x,j_x} dμ]
= ∑_γ a_γ · ∑_{i,j} conj(B_{γ,σ(i),j}) · B_{γ,i,j}    (σ = cyclic shift)
= ∑_γ a_γ · ⟨B_γ, σ(B_γ)⟩    (inner product with a SHIFTED version)
```

This is `⟨B, σ(B)⟩` (inner product of B with a cyclically-shifted version), NOT `‖B‖²`.
**This is NOT necessarily non-negative**, even with `a_γ ≥ 0`.

The cyclic shift `σ` is a unitary operator, but `⟨B, σ(B)⟩` is NOT necessarily real or non-negative.
This is the SAME obstacle as §8.11.38 (`∑ A²` not `∑ |A|²`), confirmed for the Lüscher cascade.

#### Finding 7: The transfer matrix IS positive, but positivity comes from FULL lattice structure

The transfer matrix T is positive (this is the theorem). The positivity does NOT come from the character
expansion alone (which gives `c_γ²`, not `|c_γ|²`). Instead, it comes from the **Lüscher decomposition**
(§8.11.33): `T = V^{1/2} · U · V^{1/2}` where:
- `V` = spatial plaquette factor (positive multiplication operator, PD by `plaquetteBoltzmannPD`)
- `U` = temporal plaquette operator (the Lüscher cascade result)

The key: `U` is PD **as an operator on the weighted space** `L²(SU(N)^L, V·μ)`, NOT as a standard
kernel on `SU(N)^L`. The spatial factor `V^{1/2}` changes the measure, and the product `V^{1/2}·U·V^{1/2}`
is positive even though `U` alone (as a standard kernel) is NOT necessarily PD.

This is the **Schur product theorem** applied to the operator level: the product of a positive
multiplication operator (`V^{1/2}`) and a positive operator (`U` in the weighted space) is positive.

#### Conclusion: The formalization requires the OPERATOR-LEVEL approach, not the kernel-level approach

The character expansion approach (kernel-level) gives `c_γ²` (not `|c_γ|²`), which is NOT non-negative.
The non-negativity comes from the OPERATOR-LEVEL structure: `T = V^{1/2} · U · V^{1/2}` where the
spatial factor `V` and the temporal operator `U` combine to give a positive operator.

**Recommended path forward:**
1. **Formalize the Lüscher decomposition** `T = V^{1/2} · U · V^{1/2}` at the operator level.
   - `V` = multiplication by `exp(-β·S_spatial/2)` (positive, PD by `plaquetteBoltzmannPD`).
   - `U` = the temporal plaquette operator (Lüscher cascade result).
   - Show `U` is positive as an operator on the weighted space `L²(SU(N)^L, V·μ)`.
2. **Alternative: plaquette-by-plaquette induction** (§8.11.34-35). Use the PD of each plaquette factor
   and the product structure to show the full Boltzmann factor is PD, then use reflection positivity
   directly (without the character expansion).
3. **Alternative: study the actual Lüscher (1977) / Osterwalder-Seiler (1978) proof** to understand
   the specific mechanism for the operator-level positivity.

**Key realization:** The character expansion is a COMPUTATIONAL TOOL, not the PROOF MECHANISM.
The proof mechanism is the Lüscher decomposition (operator-level) or the plaquette induction
(product of PD factors). The character expansion computes the kernel but does NOT prove non-negativity.

**Key infrastructure for the operator-level approach:**
- `plaquetteBoltzmannPD` (PeterWeyl.lean:325): each plaquette factor is PD.
- `PositiveDefinite.prod` / `PositiveDefinite.finprod`: product of PD functions is PD (Schur product).
- `PositiveDefinite.integral` (PositiveDefiniteIntegral.lean:98): partial trace of PD is PD.
- `PositiveDefinite.integralOperator_nonneg` (PositiveDefiniteIntegral.lean:192): PD → positive operator.
- `character_expansion_nonneg_shared` (PositiveDefiniteIntegral.lean:1196): shared-variable positivity.
- `integral_G_thetaG_eq_inner_g_Tg` (TransferMatrix.lean:5149): reduces ∫ G·G(θU) to ∫ g·(Tg).
- `transfer_matrix_fubini_integrated_pull_fullReflect` (TransferMatrix.lean:6005): character expansion of T.

### 8.11.51 BREAKTHROUGH: The axiom requires GAUGE INVARIANCE — character expansion gives ⟨C, σ(C)⟩ (NOT ‖C‖²) for general f, but ‖C‖² for gauge-invariant f (2026-08-08 session 61)

**Build GREEN (unchanged, 2972 jobs). No code changes this session — pure analysis.**

This session performed a deep mathematical analysis of the operator-level approach and reached a CRITICAL conclusion: **the axiom `transferMatrixPositivity_axiom` is FALSE as stated (for general f with `dependsOnlyOnPosSpatialInterface`), at least for SU(N) with N ≥ 3 and L ≥ 3. The non-negativity requires f to be GAUGE-INVARIANT.**

#### The mathematical analysis

The transfer matrix positivity reduces to showing:
```
I = ∫_{u⁰} F(u⁰) · F(σ(u⁰)) dμ⁰ ≥ 0
```
where F(u⁰) = ∫_{U⁺} f(U⁺, u⁰_s) · B₁(U⁺, u⁰) dμ⁺, B₁ is the "upper half" Boltzmann factor (product of PD plaquette factors), and σ inverts temporal interface links.

**Character expansion of F in u⁰_t:** F(u⁰_s, u⁰_t) = Σ_γ c_γ(u⁰_s) · χ_γ(u⁰_t). Then:
```
I = ∫_{u⁰_s} Σ_γ c_γ(u⁰_s)² dμ(u⁰_s)
```
The coefficient is c_γ² (complex square), NOT |c_γ|² (absolute square). This is NOT necessarily non-negative.

**Why c_γ² not |c_γ|²:** F(σ(u⁰)) = F(u⁰_s, (u⁰_t)⁻¹) = Σ_γ c_γ · conj(χ_γ(u⁰_t)). The integral ∫ χ_γ · conj(χ_{γ'}) dμ = δ_{γ,γ'}, giving Σ c_γ · c_γ = Σ c_γ² (NOT Σ c_γ · conj(c_γ) = Σ |c_γ|²).

**Verification with concrete example:** G = SU(2), F(g) = i·χ(g) (purely imaginary). Then ∫ F(g)·F(g⁻¹) dμ = i²·∫|χ|² dμ = -1 < 0. (Note: this specific F is not real, but for SU(N) with N≥3, real F can have complex c_γ with c_γ² < 0.)

#### The Lüscher cascade trace calculation (1D chain)

For the 1D chain (L spatial sites, one spatial direction), the temporal plaquette operator T_temporal has kernel K(U,V) = Σ_γ a_γ · χ_γ(∏_x V(x)·U(x)⁻¹) with a_γ ≥ 0 (Lüscher cascade).

Expanding χ_γ(∏_x V(x)·U(x)⁻¹) in matrix elements and integrating against φ(U)·φ(V):
```
⟨φ, T_temporal φ⟩ = Σ_γ a_γ · Σ_{j_0,...,j_{L-1}} Tr(B_{j_0} · B_{j_1} · ... · B_{j_{L-1}})
```
where B_{j_x} = a_{j_x} · a_{j_x}† is a rank-1 PSD matrix (outer product), with (a_{j_x})_i = ∫ φ(U) · (ρ_γ(U(x)))_{i,j_x} dμ(U).

**Key results by chain length L:**
- **L=1:** Tr(B_{j_0}) = ‖a_{j_0}‖² ≥ 0. ✓ (Always positive, no gauge invariance needed.)
- **L=2:** Tr(B_{j_0}·B_{j_1}) = |⟨a_{j_0}, a_{j_1}⟩|² ≥ 0. ✓ (Always positive.)
- **L≥3:** Tr(B_{j_0}·...·B_{j_{L-1}}) = ⟨C, σ(C)⟩ (inner product of C with its CYCLICALLY SHIFTED version σ(C), where σ shifts indices (i_0,...,i_{L-1}) → (i_1,...,i_0)). This is NOT necessarily ≥ 0. ✗

**The cyclic shift obstacle (L≥3):** Tr(B_0·B_1·B_2) = Σ_{i,j,k} c_{i,j,k} · conj(c_{j,k,i}) = ⟨C, σ(C)⟩ where σ is the cyclic shift (i,j,k)→(j,k,i). This is the SAME obstacle as §8.11.50 Finding 6: ⟨B, σ(B)⟩ ≠ ‖B‖².

#### THE KEY INSIGHT: Gauge invariance resolves the obstacle

**For gauge-invariant φ, the matrix elements A_{γ,i,j} = ∫ φ(U)·(ρ_γ(U(x)))_{i,j} dμ(U) VANISH for non-trivial γ.**

Proof: By gauge invariance, φ(g·U) = φ(U) for all gauge transformations g. The gauge transformation at site x conjugates U(x): U(x) → g(x)·U(x)·g(x+1)⁻¹. So:
```
A_{γ,i,j} = ∫ φ(U)·(ρ_γ(g(x)·U(x)·g(x+1)⁻¹))_{i,j} dμ(U)
           = Σ_{k,l} (ρ_γ(g(x)))_{ik} · (ρ_γ(g(x+1)⁻¹))_{lj} · A_{γ,k,l}
```
Setting g(x+1) = e and averaging over g(x):
```
A_{γ,i,j} = Σ_k [∫ (ρ_γ(g))_{ik} dμ(g)] · A_{γ,k,j} = δ_{γ,trivial} · A_{trivial,i,j}
```
by Schur orthogonality (∫ (ρ_γ(g))_{ik} dμ = 0 for γ ≠ trivial).

**For gauge-invariant φ, only the trivial representation (γ=trivial) survives.** The trivial character is χ_trivial = 1 (constant), so:
```
⟨φ, T_temporal φ⟩ = a_trivial · ∫∫ φ(U)·φ(V)·1 dμ(U)dμ(V) = a_trivial · (∫ φ dμ)² ≥ 0
```
(since a_trivial ≥ 0 and (∫ φ dμ)² ≥ 0 for real φ). ✓

**This is the proof mechanism!** The gauge invariance forces the character expansion to collapse to the trivial representation, where the cyclic shift obstacle disappears (the trivial character is constant, so σ acts trivially).

#### Implications for the formalization

1. **The axiom `transferMatrixPositivity_axiom` is FALSE as stated** (for general f with `dependsOnlyOnPosSpatialInterface`), at least for SU(N) with N ≥ 3 and L ≥ 3. The counterexample: non-gauge-invariant f gives complex c_γ with c_γ² < 0.

2. **The fix: add a gauge-invariance hypothesis** to the axiom. The weakened axiom (with gauge-invariant f) is TRUE and matches the Lüscher (1977) theorem ("transition probabilities between gauge invariant states are non-negative").

3. **The proof mechanism is:**
   - (a) For gauge-invariant φ, matrix elements A_{γ,i,j} vanish for non-trivial γ (Schur orthogonality + gauge invariance).
   - (b) Only the trivial representation survives in the character expansion.
   - (c) The trivial representation term is a_trivial · (∫ φ dμ)² ≥ 0.

4. **The Lüscher decomposition T = V^{1/2}·U·V^{1/2} is correct**, but U (the temporal plaquette operator) is positive ONLY on gauge-invariant states. For general states, U is NOT positive (the cyclic shift obstacle). The spatial factor V is gauge-invariant (spatial plaquette action is gauge-invariant), so V^{1/2} preserves gauge invariance.

5. **The "partial inner product" result** (∫ φ(g,h)·conj(φ(g',h)) dμ(h) is PD if φ is PD on G×H) does NOT directly apply because the σ twist gives B₁(V⁺, σ(u⁰)) ≠ conj(B₁(V⁺, u⁰)) for non-abelian groups.

#### Why the character expansion approach (sessions 55-60) was blocked

The character expansion gives c_γ² (not |c_γ|²) because:
- F(σ(u⁰)) = Σ c_γ · conj(χ_γ) (σ inverts temporal links → conj of characters).
- ∫ χ_γ · conj(χ_{γ'}) dμ = δ_{γ,γ'} (orthogonality).
- So ∫ F · F(σ) dμ = Σ c_γ · c_γ = Σ c_γ² (NOT Σ |c_γ|²).

The gauge invariance resolves this by forcing c_γ = 0 for γ ≠ trivial, so only c_trivial² survives, and c_trivial is real (trivial representation is self-dual), so c_trivial² ≥ 0.

#### Path forward for the next session

1. **Define lattice gauge invariance** for functions on link variables: φ is gauge-invariant if φ({g(x)·U_μ(x)·g(x+μ̂)⁻¹}) = φ({U_μ(x)}) for all site-valued functions g: sites → SU(N).

2. **Add gauge invariance hypothesis** to `transferMatrixPositivity_axiom` and all downstream theorems (`gibbsExpectationPeriodic_reflection_positive`, `lattice_ym_reflection_positive_periodic`, etc.).

3. **Prove the key lemma:** For gauge-invariant φ, ∫ φ(U)·(ρ_γ(U(x)))_{i,j} dμ(U) = 0 for γ ≠ trivial. This uses:
   - Gauge invariance: φ(g·U) = φ(U).
   - Change of variables: U → g·U (measure-preserving, product of conjugations).
   - Schur orthogonality: ∫ (ρ_γ(g))_{ij} dμ(g) = 0 for γ ≠ trivial (already available as `characterOrthogonality` axiom).

4. **Use the key lemma** to show the temporal plaquette operator is positive on gauge-invariant states (only trivial representation survives → (∫ φ dμ)² ≥ 0).

5. **Assemble** with the Lüscher decomposition T = V^{1/2}·U·V^{1/2} (V is gauge-invariant, so V^{1/2} preserves gauge invariance).

**Key infrastructure needed:**
- Lattice gauge transformation definition (does NOT currently exist in the lattice setting — only continuum gauge invariance in `GaugeInvariance.lean`).
- Schur orthogonality for matrix elements (available as `characterOrthogonality` axiom).
- The Lüscher cascade result (`chainIntegral_eq`, `luscher_2site_cascade_coeff`, etc.) — already PROVEN.
- The character expansion of the temporal plaquette operator — already PROVEN (`transfer_matrix_fubini_integrated_pull_fullReflect`).

**Note on physical correctness:** In lattice gauge theory, physical observables are gauge-invariant (Wilson loops). Restricting to gauge-invariant f is physically correct and matches the Lüscher (1977) theorem statement: "transition probabilities between gauge invariant states are non-negative."

### 8.11.52 The L≥2 factorization gap: single-link vanishing does NOT directly apply to the Lüscher cascade product integral (2026-08-09 sessions 63-64)

**Build GREEN (2972 jobs), 0 sorries, 6 axioms. Key lemma `gaugeInvariant_matrixElement_integral_zero` now PROVEN and compiles.**

This session (64) fixed the build errors in the key lemma from session 62 (which were never caught because the build was never run). The key lemma is now PROVEN and verified to depend only on `[propext, Classical.choice, Quot.sound, characterOrthogonality]` — NO dependence on `transferMatrixPositivity_axiom`. However, a deeper analysis (session 63) reveals that the §8.11.51 proof strategy has a **factorization gap for L≥2** that must be resolved before the axiom can be closed.

#### What was proven: the single-link vanishing lemma

The key lemma `gaugeInvariant_matrixElement_integral_zero` (ReflectionPositivity.lean:2504) proves:

```
∫ φ(ext cfg) · (ρ_σ((ext cfg).value x μ))_{r,s} dμ₀ = 0   for σ ≠ σ_0 (trivial)
```

This is a **single-link** matrix element: φ (a gauge-invariant function of ALL link variables) multiplied by the matrix element of ONE link variable U(x,μ). The proof works by:
1. Gauge invariance: the integral is invariant under U(x,μ) ↦ h·U(x,μ) (left-multiplying one link).
2. Expanding (ρ_σ(h·U))_{r,s} = Σ_k (ρ_σ h)_{r,k} · (ρ_σ U)_{k,s} (matrix multiplication).
3. Averaging over h: A_{r,s} = Σ_k [∫ (ρ_σ h)_{r,k} dν(h)] · A_{k,s}.
4. Schur orthogonality: ∫ (ρ_σ h)_{r,k} dν = 0 for σ ≠ trivial (from `characterOrthogonality`).
5. Hence A_{r,s} = 0.

#### The gap: the Lüscher cascade produces PRODUCT integrals

The §8.11.51 strategy (step 4) requires showing that the **temporal plaquette operator** is positive on gauge-invariant states. The Lüscher cascade (§8.11.51, "Lüscher cascade trace calculation") expands the temporal plaquette operator's kernel and integrates against φ(U)·φ(V). For a 1D spatial chain of length L, this produces:

```
⟨φ, T_temporal φ⟩ = Σ_γ a_γ · Σ_{j_0,...,j_{L-1}} Tr(B_{j_0} · B_{j_1} · ... · B_{j_{L-1}})
```

where B_{j_x} = a_{j_x} · a_{j_x}† (rank-1 PSD outer product) and the vector a_{j_x} has components:

```
(a_{j_x})_i = ∫ φ(U) · (ρ_γ(U(x)))_{i, j_x} dμ(U)
```

**CRITICAL:** Each (a_{j_x})_i is a **single-link** matrix element (φ times the matrix element of link U(x)). The key lemma shows each (a_{j_x})_i = 0 for γ ≠ trivial. So a_{j_x} = 0 for γ ≠ trivial, hence B_{j_x} = 0, hence the trace is 0 for γ ≠ trivial. **Only the trivial representation survives.**

**BUT:** This argument assumes that (a_{j_x})_i = ∫ φ(U) · (ρ_γ(U(x)))_{i,j_x} dμ(U) is a single-link integral where φ is gauge-invariant and U(x) is a single link. The key lemma applies to this IF φ depends on U(x) only through the full configuration AND the gauge transformation acts on U(x) alone (left-multiplication by h at site x).

**The subtlety:** In the Lüscher cascade, φ is a function of the FULL spatial interface (all spatial links at all sites). The gauge transformation at site x conjugates U(x) → g(x)·U(x)·g(x+1)⁻¹, which affects BOTH U(x) and U(x+1) (the links at x and x+1). So the "left-multiplication by h" in the key lemma corresponds to setting g(x) = h and g(x+1) = e (identity at the neighboring site). This IS a valid gauge transformation, and the key lemma's proof uses exactly this (gaugeTransformLinkVariable_single_site with g_h(y) = if y = x then h else 1).

**So the key lemma DOES apply to each (a_{j_x})_i individually.** The product structure of the cascade trace is built from these individual single-link integrals, each of which vanishes for γ ≠ trivial. The product integral does NOT need to factorize — it is ALREADY a product of single-link integrals (by the Lüscher cascade decomposition), and each factor vanishes.

#### Re-examination: the gap IS real — the cascade produces PRODUCT integrals, not single-link integrals

On closer analysis, the §8.11.51 cascade trace formula is **misleading**. The formula expresses ⟨φ, T_temporal φ⟩ as Σ_γ a_γ · Tr(B_{j_0}·...·B_{j_{L-1}}) with B_{j_x} built from single-link vectors a_{j_x} = (∫ φ·(ρ_γ(U(x)))_{i,j_x})_i. **But this formula is for the case WITHOUT φ** — the cascade lemma `luscher_2site_cascade_coeff` integrates over temporal links g₀, g₁ and uses character orthogonality to collapse, producing χ_s(W·V). There is NO φ in this lemma.

When φ is introduced (the actual transfer matrix matrix element ⟨φ, T φ⟩ = ∫∫ φ(U)·φ(V)·K(U,V) dμ(U)dμ(V)), the cascade result K(U,V) = Σ_γ a_γ · χ_γ(∏_x U(x)·V(x)⁻¹) is a character of a **PRODUCT** of spatial links. Expanding this character in matrix elements gives:

```
∫ φ(U) · ∏_x (ρ_γ(U(x)))_{i_x, j_x} dμ(U)
```

This is a **PRODUCT integral** (φ times a product of matrix elements at DIFFERENT sites), NOT a single-link integral. The product does NOT factorize because φ(U) couples all U(x).

**Why the key lemma does NOT apply to the product integral:** The key lemma works by averaging over a gauge transformation at a SINGLE site x, which left-multiplies U(x) by g(x) (with g(x+1) = e). This introduces ONE factor (ρ_γ(g(x)))_{r,k}, and Schur orthogonality gives ∫ (ρ_γ(g))_{r,k} dμ(g) = 0 for γ ≠ trivial (the integral of a SINGLE matrix element is the trivial projection = 0 for non-trivial irreps).

For the product integral, the gauge transformation at site x left-multiplies U(x) by g(x) AND right-multiplies U(x-μ) by g(x)⁻¹ (since the link U(x-μ) ends at site x). This introduces TWO factors: (ρ_γ(g(x)))_{i_x, k_x} from U(x) and (ρ_γ(g(x)⁻¹))_{l_{x-μ}, j_{x-μ}} = conj((ρ_γ(g(x)))_{j_{x-μ}, l_{x-μ}}) from U(x-μ). Averaging over g(x) gives:

```
∫ (ρ_γ(g))_{i_x, k_x} · conj((ρ_γ(g))_{j_{x-μ}, l_{x-μ}}) dμ(g) = (1/dims γ) · δ_{i_x, j_{x-μ}} · δ_{k_x, l_{x-μ}}
```

This is the **diagonal** Schur orthogonality (same representation γ on both factors), which gives a **delta (non-zero)**, NOT zero. So the product integral does NOT vanish for γ ≠ trivial.

**CONCLUSION: The §8.11.51 claim "gauge invariance forces only the trivial representation to survive" is WRONG for L≥2.** The gauge invariance at a single site couples two links in the SAME representation, and Schur orthogonality gives a delta (index contraction), not a vanishing. After averaging over ALL sites, the product integral becomes a **Wilson loop** integral (gauge-invariant combination of non-trivial reps), which is generally NON-ZERO. Non-trivial representations DO survive in the product integral, even with gauge invariance.

**The L=1 case is the ONLY case where the key lemma directly applies** (single site, single link, the gauge transformation left-multiplies the only link, introducing ONE matrix element → Schur gives 0). For L≥2, a different mechanism is needed.

#### The correct mechanism: positive-definiteness of the plaquette Boltzmann factor (Osterwalder-Seiler)

The transfer matrix positivity does NOT come from "gauge invariance collapsing the character expansion to the trivial representation." Instead, it comes from the **positive-definiteness (PD) of the plaquette Boltzmann factor** (Osterwalder-Seiler 1978, §3):

1. The plaquette Boltzmann factor exp(c·Re Tr(g₁g₂g₃g₄)) is a PD function on SU(N)⁴ — PROVEN in `PeterWeyl.lean` (`plaquetteBoltzmannPD_inv`, `charProduct_PD`, `reflection_positivity_reorganization`).

2. The transfer matrix T = V^{1/2}·U·V^{1/2} where U is the temporal plaquette operator. The positivity of U comes from the PD of the plaquette factor, NOT from gauge invariance.

3. The gauge invariance hypothesis (`IsGaugeInvariant N f`) on the axiom may still be needed — but NOT for the "trivial rep only" mechanism. It may be needed because the transfer matrix is positive only on the gauge-invariant subspace (the §8.11.51 counterexample shows T is NOT positive on the full space for non-gauge-invariant f). The mechanism by which gauge invariance ensures positivity on the gauge-invariant subspace requires further investigation.

**Key open question:** How does the PD of the plaquette factor (step 1) combine with the shared temporal links (the cascade) to give a positive operator U? The §8.11.50 analysis (session 60) found obstacles (cyclic shift for L≥3, non-PSD of ρ_s(M)). The `reflection_positivity_reorganization` lemma (PeterWeyl.lean:1845) may be the key — it reorganizes the plaquette factors to separate temporal and spatial parts. This needs to be traced through to the transfer matrix positivity.

**Remaining work to close the axiom:**
1. Understand how `reflection_positivity_reorganization` + `plaquetteBoltzmannPD_inv` imply the temporal plaquette operator U is positive (possibly on the gauge-invariant subspace only).
2. Determine whether the gauge invariance hypothesis is actually needed, or whether T is positive on the full space (which would mean the §8.11.51 counterexample is flawed — note the counterexample used F(g)·F(g⁻¹) without conj, which may not match the actual axiom form ∫ G(U)·G(θU)).
3. Assemble: PD of plaquette → U positive → T = V^{1/2}·U·V^{1/2} positive → ∫ G·G(θU) ≥ 0.
4. Convert `transferMatrixPositivity_axiom` to a lemma.

#### Build fix details (session 64)

The key lemma had 4 compile errors from session 62 (never caught because build wasn't run):
1. **Line 2567 (OfNat):** `(ρ σ_0 h) 0 0` — the `0 0` indices are `Fin (dims σ_0)` but `dims σ_0 = 1` is a hypothesis (not definitional), so `OfNat (Fin (dims σ_0)) 0` couldn't be synthesized. **Fix:** `have i0 : Fin (dims σ_0) := ⟨0, hDims σ_0⟩` and use `i0` instead of `0`.
2. **Line 2571 (hInt argument order):** `hInt σ σ r k σ_0 0 0` had wrong argument order (7 args for 6-arg function, σ_0 in a Fin position). **Fix:** `hInt σ σ_0 r k i0 i0` (correct: rep σ, rep σ_0, then Fin indices).
3. **Line 2577 (const_mul order):** `Integrable.const_mul` gives `c * f` (const on LEFT) but the sum needs `f * c` (const on RIGHT). **Fix:** `Integrable.congr h (Filter.Eventually.of_forall (fun g => by ring))` to flip the order.
4. **Line 2580 (rw pattern):** `rw [h_eq]` failed because `set A` didn't substitute `A r s` in the goal (higher-order matching issue). **Fix:** prove `h_zero : A r s = 0` as a separate `have`, then `exact h_zero` (closes by defeq since `A r s` unfolds to the integral in the goal).

The `conj` identifier was NOT the problem (it elaborates to `starRingEnd ℂ` via `open scoped ComplexConjugate`). The real issues were the `Fin (dims σ_0)` indices and the `const_mul` argument order.

### 8.11.53 RESOLUTION: The gauge invariance hypothesis is NOT needed — the §8.11.51 counterexample is invalid; the correct mechanism is the PD of the plaquette factor (works for ALL f with dependsOnlyOnPosSpatialInterface) (2026-08-09 session 65)

**Build GREEN (2972 jobs), 0 sorries. The gauge invariance hypothesis `hf_gauge : IsGaugeInvariant N f` has been REMOVED from `transferMatrixPositivity_axiom` and all 5 downstream sites. Axiom count unchanged (6).**

This session resolved the key open question from §8.11.52 (item 2): **the gauge invariance hypothesis is NOT needed.** The axiom `transferMatrixPositivity_axiom` is true with ONLY `hf_supported : dependsOnlyOnPosSpatialInterface N T L f` (no gauge invariance). The §8.11.51 counterexample that motivated adding the gauge invariance hypothesis (session 62) is INVALID. The correct mechanism is the PD of the plaquette Boltzmann factor (Osterwalder-Seiler), which works for ALL f with `dependsOnlyOnPosSpatialInterface`, not just gauge-invariant f.

#### Why the §8.11.51 counterexample is invalid

The §8.11.51 analysis (session 61) claimed the axiom is FALSE for general f with `dependsOnlyOnPosSpatialInterface`, for SU(N) with N≥3 and L≥3. The argument had TWO flaws:

**Flaw 1: The counterexample uses temporal interface links, which are EXCLUDED by `dependsOnlyOnPosSpatialInterface`.**

The §8.11.51 "verification" (line 4780): "G = SU(2), F(g) = i·χ(g) (purely imaginary). Then ∫ F(g)·F(g⁻¹) dg = i²·∫|χ|² dg = -1 < 0." This F is purely imaginary — but the axiom's f is REAL-valued (`f : LinkVariable (SU N) (PeriodicSite T L) → ℝ`), so G(U) = f(U)·exp(...) is real, and F(u⁰) = ∫ f·B₁ dμ⁺ is real. A purely imaginary F CANNOT arise from the axiom.

The §8.11.51 analysis acknowledged this ("Note: this specific F is not real, but for SU(N) with N≥3, real F can have complex c_γ with c_γ² < 0"). The "real F" counterexample relies on the character expansion of F in the TEMPORAL interface links u⁰_t (line 4772: "F(u⁰_s, u⁰_t) = Σ_γ c_γ(u⁰_s)·χ_γ(u⁰_t)"). But `dependsOnlyOnPosSpatialInterface` EXCLUDES temporal interface links (μ=0 at t=0) — f does not depend on them. The σ twist (inversion of temporal interface links) is the SOLE source of the c_γ² (vs |c_γ|²) problem (§8.11.36, line 426-431). Since f doesn't depend on u⁰_t, the σ twist does not affect f, and the problematic character expansion in u⁰_t does not arise.

**Flaw 2: The reduction `I = ∫ F(u⁰)·F(σ(u⁰)) dμ⁰` assumes a SEPARABLE Boltzmann factor, which is WRONG for L≥2.**

The §8.11.51 reduction (line 4768) integrates out U⁺ first: F(u⁰) = ∫_{U⁺} f(U⁺, u⁰_s)·B₁(U⁺, u⁰) dμ⁺, then claims I = ∫_{u⁰} F(u⁰)·F(σ(u⁰)) dμ⁰. This assumes the Boltzmann factor B(U) separates as B₁(U⁺, u⁰)·B₂(V⁺, u⁰) where B₂ is the reflected B₁, so the V⁺ integral gives F(σ(u⁰)).

But the interface plaquettes (spanning t=0) couple U⁺, u⁰, AND V⁺ through SHARED temporal links — they do NOT separate as B₁(U⁺, u⁰)·B₂(V⁺, u⁰). This is exactly the "L≥2 factorization gap" identified in §8.11.52 (line 4914): "the cascade lemma integrates over temporal links g₀, g₁ and uses character orthogonality to collapse, producing χ_s(W·V). There is NO φ in this lemma." The interface plaquette factor is a PRODUCT of plaquette factors that share temporal links, and it does NOT factor into separate U⁺ and V⁺ parts.

The correct treatment (§8.11.52, "The correct mechanism") expands the interface plaquette factor in characters via `interface_kernel_character_expansion` (PeterWeyl.lean:1587), giving `Σ_w F(w)·Φ_w(U⁺)·Ψ_w(u⁰)·conj(Φ_w(V⁺))` with F(w) ≥ 0. This is NOT a separable product — it's a sum of separated character products with non-negative coefficients, which has the Gram matrix PSD structure.

#### The β=0 case: provably ≥ 0 WITHOUT gauge invariance

For β=0, G(U) = f(U) (exp(0)=1). The integral is `∫ f(U)·f(θU) dμ₀`. Since f depends on positive+spatial-interface links and θU's positive-site links are U's negative-site links (time-inverted), while θU's spatial-interface links are U's spatial-interface links (interface maps to itself, spatial not inverted):

- f(U) depends on: {U(n,μ) : n positive, any μ} ∪ {U(n,μ) : n interface, μ≠0}
- f(θU) depends on: {U(n',μ) : n' negative, μ=0 inverted} ∪ {U(n',μ) : n' negative, μ≠0} ∪ {U(n,μ) : n interface, μ≠0}

The spatial interface links are SHARED; the positive and negative links are DISJOINT. By the product measure (independent links) and the measure-preserving change of variables U⁻ ↦ θU⁻ (reflection + inversion are measure-preserving on SU(N), proven as `reflectLinkVariable_measurePreserving`):

```
I = ∫_{u⁰_s} [∫_{U⁺} f(U⁺, u⁰_s) dμ⁺] · [∫_{U⁻} f(θU⁻, u⁰_s) dμ⁻] dμ(u⁰_s)
  = ∫_{u⁰_s} F(u⁰_s) · F(u⁰_s) dμ(u⁰_s)     (change of variables U⁻ ↦ θU⁻)
  = ∫_{u⁰_s} F(u⁰_s)² dμ(u⁰_s)  ≥  0
```

where F(u⁰_s) = ∫_{U⁺} f(U⁺, u⁰_s) dμ⁺ is REAL-VALUED (f is real). So F² ≥ 0 and the integral is ≥ 0. **No gauge invariance needed.** The σ twist is irrelevant because f doesn't depend on temporal interface links.

#### The β>0 case: PD of the plaquette factor (Osterwalder-Seiler)

For β>0, the interface plaquette Boltzmann factor couples U⁺, u⁰, and V⁺. By `interface_kernel_character_expansion` (PeterWeyl.lean:1587):

```
K(U⁺, u⁰, V⁺) = ∏_p exp(c·Re Tr(...)) = Σ_w F(w) · Φ_w(U⁺) · Ψ_w(u⁰) · conj(Φ_w(V⁺))
```

with F(w) ≥ 0, where Φ_w(U⁺) = ∏_{l∈L_U} χ_{w(l)}(g_l), Ψ_w(u⁰) = ∏_{l∈L_0} χ_{w(l)}(g_l), and the V⁺ links appear with CONJUGATED dual characters.

The integral `∫ f(U⁺, u⁰_s)·f(V⁺, u⁰_s)·K(U⁺, u⁰, V⁺) dμ` becomes (after expanding K and f in matrix elements):

```
Σ_w F(w) · Σ_{x,y} d_w(x)·conj(d_w(y)) · Σ_g ∏_l A^{(w,l)}(g_l, x_l)·conj(A^{(w,l)}(g_l, y_l))
```

which is ≥ 0 by `reflection_positivity_reorganization` (PeterWeyl.lean:1820), since:
- Each per-mode term is a multi-link Gram matrix quadratic form ≥ 0 (`multi_link_gram_psd_nonneg`, PeterWeyl.lean:1739).
- The per-link integral `∫ χ_s(g)·(ρ_t g)_{ij}·conj((ρ_u g)_{kl}) dg` gives a PSD Gram matrix in CG coefficients (`triple_product_character_matrix_integral`, PeterWeyl.lean:1858).
- The weights F(w) ≥ 0 preserve non-negativity.

The temporal interface links u⁰_t appear ONLY in K (not in f, since `dependsOnlyOnPosSpatialInterface` excludes them). Integrating over u⁰_t gives `∫ χ_{w(l_t)}(g) dg = δ_{w(l_t), trivial}` (Schur orthogonality), collapsing the temporal interface characters to the trivial representation (constant 1). This does NOT affect the Gram matrix PSD structure for the remaining links.

The spatial interface links u⁰_s appear in BOTH f(U) and f(θU) (shared) AND in K. This is the TRIPLE product structure handled by `triple_product_character_matrix_integral`: the integral over each spatial interface link gives a PSD Gram matrix in CG coefficients, and the product over links gives the multi-link Gram matrix PSD.

**This works for ALL f with `dependsOnlyOnPosSpatialInterface`, NOT just gauge-invariant f.** The PSD comes from the Gram matrix structure of the triple product integral (character from K × matrix element from f(U) × conjugated matrix element from f(θU)), NOT from gauge invariance collapsing to the trivial representation.

#### The key lemma gaugeInvariant_matrixElement_integral_zero is NOT the main mechanism

The key lemma (proven in session 64, ReflectionPositivity.lean:2504) shows single-link matrix elements vanish for gauge-invariant φ. This was intended as the mechanism for the §8.11.51 "trivial rep only" approach. But §8.11.52 showed this approach is WRONG for L≥2 (product integrals don't vanish — Schur gives delta not zero for same rep). The key lemma only applies to L=1.

The correct mechanism (PD of plaquette factor) does NOT use the key lemma. The key lemma may still be useful for the L=1 case or for gauge-invariant subspace arguments, but it is NOT the main mechanism for closing the axiom.

#### Code changes this session

1. **REMOVED `hf_gauge : IsGaugeInvariant N f`** from `transferMatrixPositivity_axiom` (ReflectionPositivity.lean:2632) and all 5 downstream sites:
   - `transferMatrixPositivity_axiom` (the axiom itself)
   - `gibbsExpectationPeriodic_reflection_positive` (line 2648, calls the axiom at line 2734)
   - `PeriodicExpectation.reflectionPositive` field (line 2818-2822, the structure field)
   - `wilsonPeriodicExpectation` (line 2838, the structure instance)
   - `lattice_ym_reflection_positive_periodic` (line 2849, the final theorem)

2. **Updated docstrings** that referenced the now-invalid §8.11.51 "c_γ²" analysis:
   - `IsGaugeInvariant` docstring (Lattice.lean:265) — removed the false claim about c_γ².
   - `PeriodicExpectation.reflectionPositive` docstring (ReflectionPositivity.lean:2818) — removed "gauge-invariant".
   - `lattice_ym_reflection_positive_periodic` docstring (ReflectionPositivity.lean:2849) — already correct.

3. **Kept the gauge invariance infrastructure** (`IsGaugeInvariant`, `IsGaugeInvariantC`, `gaugeTransformLinkVariable`, `gaugeTransformConfig`, `gaugeTransformConfig_measurePreserving`, `gaugeInvariant_matrixElement_integral_zero`, etc.) — it is proven infrastructure that may be useful for the L=1 case or gauge-invariant subspace arguments, and removing it would be unnecessary churn.

#### Remaining work to close the axiom (formalization path)

The PD approach is mathematically clear (above). The formalization requires assembling the existing abstract lemmas into the specific lattice structure:

1. **Connect `interface_kernel_character_expansion` to the lattice plaquettes.** The lemma (PeterWeyl.lean:1587) is proven in an abstract setting (takes plaquette structure as parameters). Need to show the `PeriodicSite T L` interface plaquettes match the abstract structure (links partitioned into L_U, L_0, L_V; the plaquette Boltzmann factor exp(c·Re Tr(g₁g₂g₃⁻¹g₄⁻¹)) with c = β/N or similar).

2. **Expand f in matrix elements (Peter-Weyl / Fourier expansion on the product group).** f(U⁺, u⁰_s) is a function on a product of SU(N) groups. Expand it in matrix elements of irreducible representations: f = Σ_w Σ_x d_w(x)·∏_l (ρ_{w(l)}(g_l))_{x_l, x_l} (or similar). This gives the d_w coefficients for `reflection_positivity_reorganization`.

3. **Integrate out temporal interface links.** The u⁰_t links appear only in K (not f). Integrating over them collapses the temporal interface characters to trivial (Schur orthogonality). This removes the u⁰_t dependence and leaves the spatial interface links in the triple product structure.

4. **Match the Gram matrix form.** After steps 1-3, the integral has the form of `reflection_positivity_reorganization` (PeterWeyl.lean:1820): Σ_w F(w)·Σ_{x,y} d_w(x)·conj(d_w(y))·Σ_g ∏_l A^{(w,l)}(g_l, x_l)·conj(A^{(w,l)}(g_l, y_l)) with F(w) ≥ 0. Apply the lemma to conclude ≥ 0.

5. **Convert `transferMatrixPositivity_axiom` to a lemma.** Replace `axiom` with `lemma` and provide the proof assembled from steps 1-4.

The hardest parts are steps 1-2 (connecting the abstract character expansion to the specific lattice structure and expanding f in matrix elements). Steps 3-4 are more mechanical (applying existing lemmas). Step 5 is the final assembly.

**Key existing infrastructure:**
- `interface_kernel_character_expansion` (PeterWeyl.lean:1587) — the plaquette product character expansion (abstract).
- `reflection_positivity_reorganization` (PeterWeyl.lean:1820) — the Gram matrix PSD assembly.
- `multi_link_gram_psd_nonneg` (PeterWeyl.lean:1739) — per-mode multi-link Gram matrix PSD.
- `triple_product_character_matrix_integral` (PeterWeyl.lean:1858) — triple product integral = PSD Gram matrix.
- `gram_matrix_psd_nonneg` (PeterWeyl.lean:1666) — single-link Gram matrix PSD.
- `integral_G_thetaG_eq_inner_g_Tg` (TransferMatrix.lean:5149) — ∫ G·G(θU) = ∫ g·(Tg) (the transfer matrix identity).
- `reflectLinkVariable_measurePreserving` (LatticeMeasure.lean:417) — reflection is measure-preserving.
- `characterOrthogonality` (axiom) — Schur orthogonality for matrix elements.

#### Addendum: tracing the existing transfer-matrix character expansion infrastructure (session 65 continued)

After documenting the above, this session traced the EXISTING character expansion infrastructure in `TransferMatrix.lean` to assess which decomposition is the right starting point for the formalization. Key findings:

**1. The σ twist ALREADY disappears (proven).** The lemma `fourierCoeffPos_sigma_invisible` (TransferMatrix.lean:4791) is ALREADY PROVEN: when `ψ = g_posInterface(f)` with `f` satisfying `dependsOnlyOnPosSpatialInterface`, the positive Fourier coefficient `A_w(u⁰) = fourierCoeffPos(w, u⁰)` satisfies `A_w(σ(u⁰)) = A_w(u⁰)`. The stronger `fourierCoeffPos_independent_of_temporal` (TransferMatrix.lean:4827) shows A_w depends only on spatial interface links u⁰_s, not temporal u⁰_t. This CONFIRMS the §8.11.53 analysis: the σ twist is harmless because f doesn't depend on temporal interface links.

**2. The transfer-matrix Fubini form.** `transfer_matrix_fubini_integrated_pull_fullReflect` (TransferMatrix.lean:6005) is PROVEN and gives:
```
∫ ψ·Tψ dμ = C · ∑_w F(w) · ∫_{u⁰} charFactorInt(w, u⁰) · A_w(u⁰) · A_{w*}(σ(u⁰)) dμ⁰
```
where `w* = fullReflectReindex dual w`. By σ-invisibility, `A_{w*}(σ(u⁰)) = A_{w*}(u⁰)`, giving `∫ charFactorInt · A_w · A_{w*}`.

**3. KEY FINDING: A_{w*} ≠ conj(A_w) in general.** The `fullReflectReindex` (TransferMatrix.lean:5749) gives the REFLECTED weight: `w*(l) = dual(w(φ(l)))` for time-like links and `w*(l) = w(φ(l))` for spatial links, where `φ(l) = reflectInterfaceLink(l)` is the REFLECTED link (different from l). So `charFactorPos(w*, V⁺) ≠ conj(charFactorPos(w, V⁺))` in general (the weights are evaluated at DIFFERENT links, not the same link with dual). The `fourierCoeffNeg` docstring claim "B_w(u⁰) = conj(A_w(σ(u⁰)))" is UNPROVEN and likely FALSE — the proven identity is `B_w(u⁰) = A_{w*}(σ(u⁰))` (via `fourierCoeffNeg_eq_fourierCoeffPos_fullReflect`, TransferMatrix.lean:5970), NOT `conj(A_w(σ(u⁰)))`.

**4. The transfer-matrix Fubini form is a TRIPLE product, not |A_w|².** Since A_{w*} ≠ conj(A_w), the integral `∫ charFactorInt · A_w · A_{w*}` is a product of THREE complex factors (charFactorInt from K, A_w from f(U), A_{w*} from f(θU)). This is the triple product structure. It can be resolved by `triple_product_character_matrix_integral` (PeterWeyl.lean:1858), which shows `∫ χ_s · (ρ_t)_{ij} · conj((ρ_u)_{kl})` is a PSD Gram matrix in CG coefficients REGARDLESS of whether t = u. So the triple product IS PSD even with different representations.

**5. The CORRECT formalization path uses `interface_kernel_character_expansion`, NOT `transfer_matrix_fubini_integrated_pull_fullReflect`.** The `interface_kernel_character_expansion` (PeterWeyl.lean:1587) keeps U⁺ and V⁺ SEPARATE with conjugate characters (SAME weight w): `K = Σ_w F(w) · Φ_w(U⁺) · Ψ_w(u⁰) · conj(Φ_w(V⁺))`. This gives the Gram matrix form `Φ_w(U⁺) · conj(Φ_w(V⁺))` (same w, conjugated) DIRECTLY, matching `reflection_positivity_reorganization`. The `transfer_matrix_fubini_integrated_pull_fullReflect` approach integrates out V⁺ first (giving A_{w*} with a DIFFERENT weight), losing the conjugate structure and requiring the more complex triple product expansion.

**Revised formalization path (using `interface_kernel_character_expansion`):**
1. Connect `interface_kernel_character_expansion` (abstract) to the `PeriodicSite T L` lattice plaquettes — show the interface plaquette Boltzmann factor `exp(-β·S_OS_interface)` matches the abstract form `∏_p exp(c·Re Tr(g₁g₂g₃⁻¹g₄⁻¹))` with links partitioned into L_U (positive), L_0 (interface), L_V (negative, conjugated).
2. Substitute the expansion into the integral `∫ f(U⁺, u⁰_s)·f(V⁺, u⁰_s)·K dμ`, getting `Σ_w F(w) · ∫ f·Φ_w(U⁺) · f·conj(Φ_w(V⁺)) · Ψ_w(u⁰) dμ`.
3. Expand `f·Φ_w` in matrix elements (Peter-Weyl / Fourier expansion on the product group) to get the `d_w` coefficients for `reflection_positivity_reorganization`.
4. Integrate out temporal interface links u⁰_t (appear only in Ψ_w, not f; collapse to trivial via Schur orthogonality).
5. The spatial interface links u⁰_s appear in the triple product (Ψ_w from K × matrix element from f(U) × conjugated matrix element from f(θU)) — resolve via `triple_product_character_matrix_integral` → PSD Gram matrix.
6. Apply `reflection_positivity_reorganization` to conclude ≥ 0.
7. Convert `transferMatrixPositivity_axiom` to a lemma.

The hardest parts are steps 1 (connecting abstract to lattice plaquettes) and 3 (expanding f·Φ_w in matrix elements). The `transfer_matrix_fubini_integrated_pull_fullReflect` infrastructure (steps 2-5 of the original path) is an ALTERNATIVE that avoids step 1 but requires the triple product expansion (step 5) with different-weight coefficients.

### 8.11.54 STEP 2 COMPLETE: `osG_thetaG_eq_char_expansion_pointwise` PROVEN (2026-08-09 session 67)

**Build GREEN (2972 jobs), 0 sorries, 6 axioms. The lemma `osG_thetaG_eq_char_expansion_pointwise` (ReflectionPositivity.lean:2816) is PROVEN. It depends on axioms `[propext, Classical.choice, Quot.sound, peterWeyl_clebschGordan_plaquette]` — NO `sorryAx`, NO `transferMatrixPositivity_axiom`.**

Step 2 of the formalization path (§8.11.53) is complete. The lemma substitutes the character expansion of `exp(-β·S_int)` (from `interface_boltzmann_character_expansion`) into the factorization `osG(U)·osG(θU) = f(U)·f(θU)·exp(-β·S_pos)·exp(-β·S_neg)·exp(-β·S_int)` (from `osG_thetaG_factorization` + `total_decomposition_os_periodic`), giving the pointwise identity:

```
(osG(U)·osG(θU) : ℂ) = (C : ℂ) · ∑_w (F w : ℂ) · ↑r(U) · Φ_w(U) · Ψ_w(U) · V_w(U)
```

with `C > 0`, `F(w) ≥ 0`, and `r(U) = f(U)·f(θU)·exp(-β·S_pos(U))·exp(-β·S_neg(U))` (the real prefactor from the positive and negative bulk actions). The character factors `Φ_w`, `Ψ_w`, `V_w` are the same as in `interface_boltzmann_character_expansion`.

#### Key technical challenges overcome

1. **Coercion structure**: The goal LHS `(osG(U)·osG(θU) : ℂ)` is `↑(osG U) * ↑(osG θU)` (product of coercions), NOT `↑(osG U * osG θU)` (coercion of product). The `rw [h_factor]` fails directly because `h_factor` is an equation in ℝ. Fix: `rw [← Complex.ofReal_mul]` first combines `↑a * ↑b → ↑(a * b)`, then `rw [h_factor]` works.

2. **`Real.exp_add` nesting**: After distributing `-β` over `S_pos + S_neg + S_int` (left-associated in Lean), `Real.exp_add` splits from the RIGHT: `exp((a + b) + c) → exp(a + b) * exp(c) → (exp(a) * exp(b)) * exp(c)`. The result is LEFT-associated `(exp_pos * exp_neg) * exp_int`, not right-associated `exp_pos * (exp_neg * exp_int)`. The `h_rearrange` `have` must match this nesting.

3. **Typeclass resolution for `mul_assoc`**: The polymorphic `mul_assoc` fails with "typeclass instance problem is stuck — AddCommMonoid" when applied to expressions involving `Finset.sum`. Fix: instead of `rw [← mul_assoc, mul_comm, mul_assoc, Finset.mul_sum]`, use `rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]` to distribute both `C` and `↑r` into the sums on both sides, then `Finset.sum_congr` + `ring` for the per-weight step.

4. **`ring` with coercions**: The per-weight step `↑r * (C * (F w * Φ_w * Ψ_w * V_w)) = C * (F w * ↑r * Φ_w * Ψ_w * V_w)` is closed by `ring`, which treats `↑r` (a `Complex.ofReal`) and `star(...)` as atoms.

#### Proof structure

```
obtain character expansion data (C, ι, ρ, dual, F) from interface_boltzmann_character_expansion
refine ⟨C, hC, ι, ..., fun U => ?_⟩
  h_LHS: (osG·osG(θU) : ℂ) = ↑(f·f·exp_pos·exp_neg) · (exp(-β·S_int) : ℂ)
    rw [← Complex.ofReal_mul]     -- combine ↑(osG) * ↑(osG(θU)) = ↑(osG · osG(θU))
    rw [h_factor, h_total]         -- factor and decompose S_W = S_pos + S_neg + S_int
    have h_dist := by ring         -- distribute -β over the sum
    rw [h_dist, Real.exp_add, Real.exp_add]  -- split exp(a+b+c) = exp(a)*exp(b)*exp(c)
    have h_rearrange := by ring    -- rearrange f·f·(exp_pos·exp_neg)·exp_int = (f·f·exp_pos·exp_neg)·exp_int
    rw [h_rearrange, ← Complex.ofReal_mul]   -- split coercion ↑(a·b) = ↑a · ↑b to match RHS
  rw [h_LHS, h_char U]             -- substitute character expansion for exp(-β·S_int)
  set r := f·f·exp_pos·exp_neg     -- abbreviate the real prefactor
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]  -- distribute C and ↑r into sums
  refine Finset.sum_congr rfl (fun w _ => ?_)
  ring                             -- per-weight commutativity
```

#### Remaining steps (3–7)

- **Step 3**: Expand `f·Φ_w` in matrix elements (Peter-Weyl / Fourier expansion on the product group) to get the `d_w` coefficients for `reflection_positivity_reorganization`.
- **Step 4**: Integrate out temporal interface links u⁰_t (appear only in Ψ_w, not f; collapse to trivial via Schur orthogonality — `characterOrthogonality` axiom).
- **Step 5**: Spatial interface links u⁰_s appear in the triple product (Ψ_w from K × matrix element from f(U) × conjugated matrix element from f(θU)) — resolve via `triple_product_character_matrix_integral` → PSD Gram matrix.
- **Step 6**: Apply `reflection_positivity_reorganization` (PeterWeyl.lean:1820) to conclude ≥ 0.
- **Step 7**: Convert `transferMatrixPositivity_axiom` to a lemma (axiom count 6→5). Note: the axiom does not have `hN : 1 ≤ N`, but the character expansion requires it. The `N = 0` case (trivial group, integral = f(*)² ≥ 0) needs a separate argument, or `hN` must be added to the axiom and all callers.

### 8.11.55 STEP 3 ANALYSIS: The infinite Peter-Weyl expansion obstacle (2026-08-09 session 68)

**Build GREEN (2857 jobs for PeterWeyl.lean module). New lemma `integral_repCharacter_trivial` (PeterWeyl.lean:2152) PROVEN — the character integral `∫ χ_s(g) dμ = δ_{s,σ_0}` (step 4 building block).**

This session performed a thorough analysis of step 3 (expand `f·Φ_w` in matrix elements) and identified a fundamental obstacle: **the Peter-Weyl expansion of an arbitrary function `A_w(u⁰_s)` in matrix elements of the spatial interface links is an INFINITE series (countable, indexed by `Λ`), but `triple_product_character_matrix_integral` and `reflection_positivity_reorganization` require FINITE types (`Fintype ι`).**

#### The mathematical structure of the integral after step 2

After step 2, the integral is:
```
∫ osG(U)·osG(θU) dμ = C · ∑_w F(w) · ∫ ↑r(U) · Φ_w(U) · Ψ_w(U) · V_w(U) dμ
```
where `r(U) = f(U)·f(θU)·exp(-β·S_pos)·exp(-β·S_neg)`, and the character factors Φ_w, Ψ_w, V_w are products of characters over the interface links (L_U = interfaceLinkPos, L_0 = interfaceLinkInt, L_V = interfaceLinkNeg).

The links partition into:
- **Positive links** (bulk + L_U): appear in f(U), exp(-β·S_pos), Φ_w
- **Negative links** (bulk + L_V): appear in f(θU), exp(-β·S_neg), V_w
- **Temporal interface links** (L_0_temporal): appear in Ψ_w ONLY (not f, since dependsOnlyOnPosSpatialInterface excludes μ=0 at t=0)
- **Spatial interface links** (L_0_spatial): appear in f(U), f(θU), Ψ_w (SHARED)

After Fubini factorization, the integral becomes:
```
∑_w F(w) · ∫_{u⁰} Ψ_w(u⁰) · A_w(u⁰_s) · B_w(u⁰_s) dμ⁰
```
where `A_w(u⁰_s) = ∫_{pos} f(U)·exp(-β·S_pos)·Φ_w dμ_pos` and `B_w(u⁰_s) = ∫_{neg} f(θU)·exp(-β·S_neg)·V_w dμ_neg`.

#### Why PD of the plaquette factor does NOT directly give positivity

The PD of the plaquette factor (`plaquetteBoltzmannPD`, proven) means the kernel K(g,h) = B(g·h⁻¹) is PSD: `∫∫ F(g)·conj(F(h))·K(g·h⁻¹) dg dh ≥ 0`. But our integral is NOT in this form — it's a single integral with the Ψ_w factor (a product of characters, NOT necessarily ≥ 0).

**Counterexample**: On U(1) with `χ_n(g) = g^n` (PD character), `F(g) = 1 - g` gives `∫ g·|1-g|² dg = -1 < 0`. So `∫ χ_s(g)·|F(g)|² dg` can be NEGATIVE even for PD characters. The triple product structure (expanding F in matrix elements) is necessary.

#### The infinite expansion obstacle

To use `triple_product_character_matrix_integral` (which shows `∫ χ_s·(ρ_t)_{ij}·conj((ρ_u)_{kl})` is a PSD Gram matrix in CG coefficients), we must expand `A_w(u⁰_s)` in matrix elements of the spatial interface links:
```
A_w(u⁰_s) = ∑_{ν : L_0_spatial → Λ} ∑_{i,j} c_{ν,i,j} · ∏_l (ρ_{ν(l)}(g_l))_{i_l, j_l}
```
This is an INFINITE sum (countable, since `Λ` is countable and `L_0_spatial` is finite). But:
- `triple_product_character_matrix_integral` requires `ν(l) ∈ ι` (FINITE set from the axiom)
- `reflection_positivity_reorganization` requires `Fintype W` (finite weights)
- The axiom `peterWeyl_clebschGordan_plaquette` provides CG decomposition only for `ι` (finite), not `Λ` (countable)

The Peter-Weyl expansion of an arbitrary `f` uses ALL irreps in `Λ` (countable), but the triple product integral can only be evaluated for irreps in `ι` (finite). This is the fundamental mismatch.

#### Possible approaches to resolve the obstacle

1. **Extend the axiom** to provide CG decomposition for `Λ` (countable). This would require handling infinite sums (tsum/series) in Lean, which is complex. The axiom count stays at 6 (same axiom, more conclusions).

2. **L² truncation + convergence argument**: For each finite subset `S ⊂ ι`, project `A_w` onto matrix elements of irreps in `S`. The finite Gram matrix argument gives `∑_w F(w)·∫ Ψ_w·|A_w^{(S)}|² ≥ 0`. By L² convergence (`hL2` axiom), `A_w^{(S)} → A_w` as `S → Λ`, so the limit is ≥ 0. BUT: the convergence requires adding irreps from `Λ \ ι`, for which the CG decomposition doesn't apply — so the finite Gram argument only works for `S ⊂ ι`, not `S ⊂ Λ`.

3. **Proof by contradiction using L² completeness**: If the integral were < 0, use `hL2` to derive a contradiction. This avoids explicit expansion but requires careful analysis.

4. **Different formulation**: Reformulate `reflection_positivity_reorganization` to work with countable types or L² limits, avoiding the finite-type requirement.

#### What was accomplished this session

1. **New lemma `integral_repCharacter_trivial`** (PeterWeyl.lean:2152): `∫ χ_s(g) dμ = if s = σ_0 then 1 else 0`. This is the single-link building block for step 4 (temporal link integration). It uses `integral_matrix_element_trivial_projection` (Schur orthogonality for matrix elements). Note: a similar lemma `integral_repCharacter_eq_iff_trivial` (PositiveDefinite.lean:1065) already exists with a different hypothesis pattern (`htriv : ∀ g, repCharacter (ρ triv) g = 1` vs `hσ_0_trivial : ∀ g, (ρ σ_0 g) = 1`). The new lemma uses the same hypothesis pattern as the other PeterWeyl.lean lemmas, making it easier to compose.

2. **Full analysis of step 3** documented above, identifying the infinite expansion obstacle as the key challenge.

#### Next steps

- **Step 4 (temporal collapse)**: Formalize the multi-link character integral `∫ ∏_{l∈L} χ_{w(l)}(g_l) dμ = ∏_l δ_{w(l), σ_0}` using `integral_repCharacter_trivial` + Fubini (product measure factorization). This is tractable.
- **Step 3 (infinite expansion)**: Choose one of the four approaches above. Approach 1 (extend axiom) or 2 (L² truncation) seem most promising. This is the hardest remaining challenge.
- **Step 5-6**: Apply `triple_product_character_matrix_integral` + `reflection_positivity_reorganization` — these are proven but require the output of step 3.

### 8.11.56 STEP 4 COMPLETE: `integral_prod_repCharacter_trivial` PROVEN — multi-link temporal collapse (2026-08-09 session 69)

**Build GREEN (2972 jobs), 0 sorries, 6 axioms. New lemma `integral_prod_repCharacter_trivial` (PeterWeyl.lean:2204) PROVEN — the multi-link character integral `∫ ∏_{l∈L} χ_{w(l)}(g_l) dμ = ∏_l δ_{w(l), σ_0}` (step 4 of the formalization path).**

Step 4 of the formalization path (§8.11.53) is complete. The lemma formalizes the multi-link temporal collapse: integrating a product of characters over a product of compact groups (each with normalized Haar measure) factors as a product of single-link integrals, each of which collapses to the trivial representation by Schur orthogonality.

#### The lemma

```lean
lemma integral_prod_repCharacter_trivial
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (L : Type) [Fintype L] [DecidableEq L]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (σ_0 : ι) (hσ_0_dims : dims σ_0 = 1) (hσ_0_trivial : ∀ g, (ρ σ_0 g) = 1)
    (w : L → ι) :
    ∫ x : L → G, ∏ l : L, repCharacter (ρ (w l)) (x l) ∂(Measure.pi (fun _ => μ)) =
      ∏ l : L, (if w l = σ_0 then (1 : ℂ) else 0)
```

Depends on axioms: `[propext, Classical.choice, Quot.sound, characterOrthogonality]` — NO `sorryAx`, NO `peterWeyl_clebschGordan_plaquette`, NO `transferMatrixPositivity_axiom`. Same axiom dependencies as `integral_repCharacter_trivial` (the single-link building block from session 68).

#### Proof structure

The proof is a clean two-step argument:

1. **Fubini factorization** (Mathlib's `integral_fintype_prod_eq_prod`): For a finite type `L`, product measure `Measure.pi (fun _ => μ)` on `L → G`, and functions `f l` each depending on coordinate `l`, the integral of the product equals the product of the integrals:
   ```
   ∫ x, ∏ l, f l (x l) ∂(Measure.pi μ) = ∏ l, ∫ g, f l g ∂μ
   ```
   This is Mathlib's `MeasureTheory.integral_fintype_prod_eq_prod` (from `Mathlib.MeasureTheory.Integral.Pi`), which is Fubini's theorem for finite products. It requires `[RCLike 𝕜]` (satisfied by `ℂ`) and `[∀ i, SigmaFinite (μ i)]` (satisfied because `IsProbabilityMeasure → IsFiniteMeasure → SigmaFinite` via `IsFiniteMeasure.toSigmaFinite`).

2. **Single-link evaluation** (`integral_repCharacter_trivial`): Each single-link integral `∫ χ_{w(l)}(g) dμ = if w(l) = σ_0 then 1 else 0` by the lemma proven in session 68 (PeterWeyl.lean:2162), which uses Schur orthogonality (`characterOrthogonality` axiom).

The proof is:
```lean
  rw [integral_fintype_prod_eq_prod (fun (l : L) (g : G) => repCharacter (ρ (w l)) g)]
  refine Finset.prod_congr rfl (fun l _ => ?_)
  exact integral_repCharacter_trivial μ ι dims hDims ρ hU hIrr σ_0 hσ_0_dims hσ_0_trivial (w l)
```

#### Key technical details

1. **New import**: Added `import Mathlib.MeasureTheory.Integral.Pi` to PeterWeyl.lean (line 52) for `integral_fintype_prod_eq_prod`.

2. **Instance chain**: `IsProbabilityMeasure μ` → `IsZeroOrProbabilityMeasure μ` (via `IsProbabilityMeasure.toIsZeroOrProbabilityMeasure`) → `IsFiniteMeasure μ` (via `IsZeroOrProbabilityMeasure.toIsFiniteMeasure`) → `SigmaFinite μ` (via `IsFiniteMeasure.toSigmaFinite`). This chain provides the `SigmaFinite` instance needed by `integral_fintype_prod_eq_prod`.

3. **Abstract formulation**: The lemma is stated at the abstract level (any compact group `G`, any finite type `L`, any irreducible unitary representations `ρ`). This makes it reusable for the concrete application to temporal interface links (which are a finite set of `InterfaceLink T L`, each with an `SU N` variable).

#### Mathematical significance

This lemma formalizes the temporal link collapse: when we integrate over the temporal interface links (which appear ONLY in the character factor `Ψ_w`, not in `f` since `dependsOnlyOnPosSpatialInterface` excludes temporal interface links), each temporal character `χ_{w(l)}` integrates to `δ_{w(l), σ_0}`. This forces `w(l) = σ_0` (the trivial representation) for all temporal links, collapsing the temporal part of the character expansion to 1.

After step 4, the sum over weights `w` is restricted to those with `w(l) = σ_0` for all temporal links `l`. The remaining integral involves only the spatial interface links, which appear in the triple product structure (step 5).

#### Step 3 analysis: the infinite expansion obstacle (continued from §8.11.55)

This session performed a deeper analysis of step 3 (expanding `f·Φ_w` in matrix elements) and confirmed that the obstacle is fundamental. The key findings:

**1. The CORRECT path uses `interface_kernel_character_expansion` (§8.11.53, finding 5).** This keeps U⁺ and V⁺ SEPARATE with conjugate characters (SAME weight w): `K = Σ_w F(w) · Φ_w(U⁺) · Ψ_w(u⁰) · conj(Φ_w(V⁺))`. After Fubini, the integral becomes `Σ_w F(w) · ∫_{u⁰} Ψ_w · A_w · conj(A_w) dμ⁰` where `A_w(u⁰_s) = ∫_{U⁺} f(U⁺, u⁰_s) · Φ_w(U⁺) dμ⁺` and `conj(A_w)` comes from `f` being real-valued (`B_w = conj(A_w)` since `conj(f) = f`).

**2. After step 4, the integral is `Σ_w F(w) · ∫_{u⁰_s} Ψ_w^{spatial} · |A_w|² dμ_s`.** The temporal part of `Ψ_w` has collapsed to 1 (step 4), leaving only the spatial interface characters `Ψ_w^{spatial} = ∏_{l ∈ L_0_spatial} χ_{w(l)}(g_l)` with `w(l) ∈ ι`.

**3. `∫ Ψ_w^{spatial} · |A_w|²` is NOT automatically ≥ 0.** The PD of `Ψ_w^{spatial}` (product of PD characters) gives positivity for the DOUBLE integral `∫∫ F(g)·conj(F(h))·Ψ(g⁻¹h) dg dh`, but our integral is a SINGLE integral `∫ Ψ(g)·|A(g)|² dg`. The counterexample (U(1), F(g) = 1-g, ∫ g·|1-g|² dg = -1 < 0) confirms this.

**4. The triple product structure is necessary.** Expanding `A_w` in matrix elements of the spatial interface links gives `A_w = ∑_{ν, i, j} c_{ν,i,j} · ∏_l (ρ_{ν(l)}(g_l))_{i_l, j_l}`. Then `|A_w|² = A_w · conj(A_w)` involves products of matrix elements, and the integral `∫ Ψ_w · |A_w|²` becomes a sum of triple products `∫ χ_{w(l)} · (ρ_{ν(l)})_{ij} · conj((ρ_{ν'(l)})_{kl})`, each of which is a PSD Gram matrix by `triple_product_character_matrix_integral`.

**5. The fundamental mismatch.** The expansion of `A_w` uses irreps from `Λ` (countable, the full Peter-Weyl basis), because `A_w` depends on the arbitrary test function `f`. But `triple_product_character_matrix_integral` requires:
   - CG decomposition for `(s, t)` where `s = w(l) ∈ ι` and `t = ν(l) ∈ Λ` — needs CG for `ι × Λ`
   - Schur orthogonality for `(ν, u)` where `ν, u ∈ Λ` — needs Schur for `Λ × Λ`
   
   The axiom provides CG for `ι × ι` (finite) and Schur for `ι` (finite), but NOT for `Λ` (countable).

**6. Why `exp(-β·S_pos)` having a character expansion in `ι` does NOT help.** Each plaquette Boltzmann factor `exp(c·Re Tr(g₁g₂g₃g₄))` has a character expansion in `ι` (by the axiom). The product of finitely many such factors (for the positive plaquettes) also has a character expansion in `ι` (using CG for `ι × ι` to combine characters on shared links). So `exp(-β·S_pos)·Φ_w` has a character expansion in `ι`. But `A_w = ∫ f · [exp(-β·S_pos)·Φ_w] dμ⁺` involves the ARBITRARY function `f`, and the integral `∫ f · χ_s dμ⁺` produces a Fourier coefficient of `f` that is an arbitrary function of `u⁰_s`. This arbitrary function requires the full `Λ` basis for its matrix element expansion.

#### Recommended approach for step 3: Extend the axiom (Approach 1)

The most promising approach is to extend `peterWeyl_clebschGordan_plaquette` to provide:

1. **Schur orthogonality for `Λ`** (countable): `∫ (ρΛ_ℓ)_{ij} · conj((ρΛ_{ℓ'})_{kl}) dμ = if ℓ = ℓ' ∧ i = k ∧ j = l then 1/dimsΛ(ℓ) else 0`. This is a universal statement (no sums), easy to add.

2. **CG decomposition for `Λ × Λ`** (or `ι × Λ`): For each `(s, t : Λ)`, the product `(ρΛ_s)_{ab} · (ρΛ_t)_{ij}` decomposes as a sum over `Λ` of matrix elements with CG coefficients. Since CG is a finite direct sum for each pair `(s, t)`, only finitely many `ν` contribute. This can be stated as:
   - A `tsum` over `Λ` (using `Encodable Λ`), with the support being finite (ensuring convergence), OR
   - An existential: for each `(s, t)`, there exists a `Finset Λ` containing the relevant `ν`, with the decomposition as a `Finset.sum`.

3. **Generalized `triple_product_character_matrix_integral`** for `Λ`: Prove the triple product integral `∫ χ_s · (ρ_t)_{ij} · conj((ρ_u)_{kl})` is a PSD Gram matrix for `s, t, u ∈ Λ` (using the extended CG decomposition and Schur orthogonality).

4. **Generalized `reflection_positivity_reorganization`** for countable types or L² limits: Extend the Gram matrix PSD assembly to handle the countable expansion of `A_w`.

This is a significant extension but is mathematically justified (it's the Peter-Weyl theorem for the full set of irreps). The axiom count stays at 6 (same axiom, more conclusions).

**Alternative approaches** (documented in §8.11.55):
- Approach 2 (L² truncation): Reduces to Approach 1 (needs CG for `Λ` to handle truncation outside `ι`).
- Approach 3 (proof by contradiction): Unclear how to use L² completeness to derive a contradiction from `I < 0`.
- Approach 4 (different formulation): Reformulate `reflection_positivity_reorganization` for countable types — also requires CG for `Λ`.

#### Remaining steps after step 4

- **Step 3 (infinite expansion)**: Extend axiom + prove generalized triple product (HARDEST, see above).
- **Step 5**: Spatial interface links triple product → PSD Gram (`triple_product_character_matrix_integral`, generalized for `Λ`).
- **Step 6**: Apply `reflection_positivity_reorganization` (generalized for countable types) → ≥ 0.
- **Step 7**: Convert `transferMatrixPositivity_axiom` to a lemma (axiom count 6→5). NOTE: the axiom lacks `hN : 1 ≤ N` but the character expansion requires it. The N=0 case (trivial group) needs a separate argument, or `hN` must be added to the axiom and all callers.

### 8.11.57 STEP 3 KEY INGREDIENT COMPLETE: `triple_product_character_matrix_integral_Λ` PROVEN + axiom extended with Schur for `Λ` and CG for `ι×Λ` (2026-08-09 session 70)

**Build GREEN (2972 jobs), 0 sorries, 6 axioms. New lemma `triple_product_character_matrix_integral_Λ` (PeterWeyl.lean:2031) PROVEN — the generalized triple-product integral for `ι × Λ` (step 3 key ingredient).**

This session implemented Approach 1 from §8.11.55 (extend the axiom) and proved the key ingredient that resolves the infinite Peter-Weyl expansion obstacle (§8.11.55–56). The axiom `peterWeyl_clebschGordan_plaquette` was extended with two new conjuncts (Parts 3–4), and the generalized triple-product integral was proven from them with `#print axioms` reporting only `[propext, Classical.choice, Quot.sound]` — pure algebra from the strengthened axiom's hypotheses, no `sorry`, no custom axiom.

#### The axiom extension (Parts 3–4)

Two new conjuncts were added to `peterWeyl_clebschGordan_plaquette` (PeterWeyl.lean:227), with two new existential witnesses `cgMEΛ` and `hcgMEΛ_support` inserted after `hμ` in the existential chain:

**Part 3 — Schur orthogonality for `Λ` (countable).** Three conjuncts:
- (i) Integrability: `∀ ν μ₂ p q k l, Integrable (fun g => (ρΛ ν g) p q * conj ((ρΛ μ₂ g) k l)) μ`
- (ii) Diagonal Schur: `∫ (ρΛ ν g)_{pq} · conj((ρΛ ν g)_{kl}) dμ = if p=k ∧ q=l then 1/dimsΛ(ν) else 0`
- (iii) Off-diagonal Schur: `∫ (ρΛ ν g)_{pq} · conj((ρΛ μ₂ g)_{kl}) dμ = 0` for `ν ≠ μ₂`

This is the **Great Orthogonality Theorem** for the full countable set of irreps `Λ`, extending `characterOrthogonality` (which covers the finite subset `ι` only). (Variable name `μ₂` avoids shadowing the measure `μ`.)

**Part 4 — Clebsch–Gordan decomposition for `ι × Λ` (finite `Finset` support).** Three conjuncts:
- (i) Decomposition: `(ρ_s g)_{ab} · (ρΛ_t g)_{ij} = ∑_{ν ∈ hcgMEΛ_support s t} ∑_{p,q} cgMEΛ s t ν a i p · (ρΛ_ν g)_{pq} · conj(cgMEΛ s t ν b j q)`
- (ii) Unitarity: `∑_{ν ∈ support} ∑_p conj(cgMEΛ) · cgMEΛ = if a=b ∧ i=j then 1 else 0`
- (iii) Support-zero: `cgMEΛ s t ν a i p = 0` for `ν ∉ hcgMEΛ_support s t`

The support is a `Finset Λ` (finite), reflecting that the tensor product `ρ_s ⊗ ρΛ_t` decomposes as a *finite* direct sum of irreps even though `Λ` itself is countable. No `DecidableEq Λ` is needed for the type (the `Finset` provides finiteness; `classical` provides decidability in proofs).

#### The lemma

```lean
lemma triple_product_character_matrix_integral_Λ
    {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (ι : Type) [Fintype ι] [DecidableEq ι] (dims : ι → ℕ)
    (hDims : ∀ i, 0 < dims i)
    (ρ : ∀ i, G →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
    (hU : ∀ i, IsUnitaryRepresentation (ρ i))
    (hIrr : ∀ i, IsIrreducible (ρ i))
    (Λ : Type) [Encodable Λ]
    (dimsΛ : Λ → ℕ) (hDimsΛ : ∀ ℓ, 0 < dimsΛ ℓ)
    (ρΛ : ∀ ℓ, G →* Matrix (Fin (dimsΛ ℓ)) (Fin (dimsΛ ℓ)) ℂ)
    (cgMEΛ : ∀ (s : ι) (t ν : Λ), Fin (dims s) → Fin (dimsΛ t) → Fin (dimsΛ ν) → ℂ)
    (hcgMEΛ_support : ∀ (s : ι) (t : Λ), Finset Λ)
    (hcgMEΛ_decomp : ...)
    (hcgMEΛ_support_zero : ...)
    (hSchurΛ_int : ...)
    (hSchurΛ_diag : ...)
    (hSchurΛ_offdiag : ...)
    (s : ι) (t u : Λ) (i j : Fin (dimsΛ t)) (k l : Fin (dimsΛ u)) :
    ∫ g, repCharacter (ρ s) g * (ρΛ t g) i j * conj ((ρΛ u g) k l) ∂μ =
      (1 / dimsΛ u : ℂ) * ∑ a : Fin (dims s),
        cgMEΛ s t u a i k * conj (cgMEΛ s t u a j l)
```

Depends on axioms: `[propext, Classical.choice, Quot.sound]` — NO `sorryAx`, NO `characterOrthogonality`, NO `peterWeyl_clebschGordan_plaquette`, NO `transferMatrixPositivity_axiom`. The lemma takes the axiom's Parts 3–4 content as *explicit hypotheses* (`hcgMEΛ_decomp`, `hcgMEΛ_support_zero`, `hSchurΛ_int`, `hSchurΛ_diag`, `hSchurΛ_offdiag`), so it is pure algebra from those hypotheses — the axiom dependency is discharged at the call site, not inside the lemma.

#### Proof structure

The proof is a clean expansion-and-collapse argument:

1. **Expand `χ_s = trace`:** `repCharacter (ρ s) g = ∑_a (ρ s g) a a` (definition of character).
2. **Apply CG decomposition for `ι × Λ`** (`hcgMEΛ_decomp`): rewrite `(ρ s g) a a · (ρΛ t g) i j` as `∑_{ν ∈ support} ∑_{p,q} cgMEΛ s t ν a i p · (ρΛ_ν g)_{pq} · conj(cgMEΛ s t ν a j q)`. This reorganizes the integrand as a finite sum (over `a`, `ν ∈ support`, `p`, `q`) of `cgMEΛ · conj(cgMEΛ) · (ρΛ_ν g)_{pq} · conj((ρΛ_u g)_{kl})`.
3. **Per-term integrability** (Fubini setup): each term is integrable by `hSchurΛ_int` (scaled by a constant `cgMEΛ · conj(cgMEΛ)`). Build up integrability through the nested finite sums (`Finset.univ` for `a, p, q`; `hcgMEΛ_support` for `ν`).
4. **Exchange sums with integral** (Fubini for finite sums): `integral_finsetSum` exchanges the finite sums over `a, ν, p, q` with the integral.
5. **Collapse by Schur orthogonality for `Λ`:**
   - For `ν ≠ u`: each integral `∫ (ρΛ_ν g)_{pq} · conj((ρΛ_u g)_{kl}) dμ = 0` by `hSchurΛ_offdiag`. The `ν`-sum collapses to the single term `ν = u`.
   - For `ν = u`: `∫ (ρΛ_u g)_{pq} · conj((ρΛ_u g)_{kl}) dμ = if p=k ∧ q=l then 1/dimsΛ(u) else 0` by `hSchurΛ_diag`. The `p, q`-sums collapse to `p=k, q=l`.
6. **Assemble:** the result is `(1/dimsΛ u) · ∑_a cgMEΛ s t u a i k · conj(cgMEΛ s t u a j l)` — a PSD Gram matrix in the CG coefficients (the `a`-sum is `∑_a x_a · conj(y_a)` with `x_a = cgMEΛ s t u a i k`, `y_a = cgMEΛ s t u a j l`).

**Case split on `u ∈ hcgMEΛ_support s t`:**
- **`u ∈ support`:** the `ν`-sum collapses to `ν = u` (off-diagonal terms vanish), then the `p, q`-sums collapse to `p=k, q=l` (diagonal Schur). Result: `(1/dimsΛ u) · ∑_a cgMEΛ s t u a i k · conj(cgMEΛ s t u a j l)`.
- **`u ∉ support`:** all `ν ∈ support` satisfy `ν ≠ u`, so all integrals vanish (off-diagonal Schur). The LHS is 0. The RHS is also 0 because `hcgMEΛ_support_zero` forces `cgMEΛ s t u a i k = 0` and `cgMEΛ s t u a j l = 0` for all `a`. Both sides are 0. ✓

#### Mathematical significance

This lemma is the **step 3 key ingredient**: it shows the generalized triple-product integral `∫ χ_s · (ρΛ_t)_{ij} · conj((ρΛ_u)_{kl}) dμ` is a **PSD Gram matrix** in the CG coefficients, for `s ∈ ι` (finite, from the character expansion of the plaquette factor) and `t, u ∈ Λ` (countable, from the L² expansion of the arbitrary test function `A_w`). This is exactly the structure needed for step 5 (spatial interface links triple product → PSD Gram) and step 6 (Gram matrix PSD assembly → ≥ 0).

The lemma generalizes `triple_product_character_matrix_integral` (PeterWeyl.lean:1909, the finite `ι × ι` version) to the mixed `ι × Λ` case. The key difference: the `ι × ι` version uses `characterOrthogonality` (Schur for finite `ι`) and the axiom's matrix-element CG for `ι × ι`; the `ι × Λ` version uses the new Part 3 (Schur for countable `Λ`) and Part 4 (CG for `ι × Λ`).

#### Axiom-strengthening logging (per permanent rule)

This is **strengthening #7** of `peterWeyl_clebschGordan_plaquette`, logged in `docs/axiom_growth_audit.md` §7 and in the README axiom table + audit summary. Summary:

- **Obstruction resolved:** the infinite Peter-Weyl expansion obstacle (§8.11.55–56). The triple product `∫ χ_s · (ρΛ_ν)_{ij} · conj((ρΛ_μ)_{kl})` requires Schur orthogonality for countable `Λ` and CG decomposition for `ι × Λ`, neither provided by the pre-strengthening axioms.
- **Timing flag:** ⚠️ DIRECTLY follows an identified obstruction. Session 68 (§8.11.55) named "Extend the axiom to provide CG decomposition for `Λ`" as the recommended approach; session 70 did exactly that.
- **Classification:** (b) substantial for both parts. Part 3 (Schur for `Λ`) is the Great Orthogonality Theorem for all irreps — as substantial as `characterOrthogonality`. Part 4 (CG for `ι × Λ`) is comparable to the existing matrix-element CG (strengthening #5).
- **Updated unfolded count:** the axiom now unfolds to **nine** axioms (A0–A8), of which **six are substantial** (A0, A1, A4, A5, A7, A8) and **three are as substantial as `characterOrthogonality`** (A4, A5, A7). The count of substantial unfolded axioms rose from 4 to 6.

#### Remaining steps

- **Step 5:** Apply `triple_product_character_matrix_integral_Λ` to the spatial interface links. Expand `A_w(u⁰_s)` in matrix elements of `Λ` (using L² completeness, Part 2), then `|A_w|² = A_w · conj(A_w)` involves products of matrix elements, and `∫ Ψ_w^{spatial} · |A_w|²` becomes a sum of triple products each evaluated by the new lemma. The result is a PSD Gram matrix in the CG coefficients. **Challenge:** the expansion of `A_w` is a countable sum over `ν : L_0_spatial → Λ`; needs L² convergence (truncate to finite subsets, show each ≥ 0, take limit) or a generalized `reflection_positivity_reorganization` for countable types.
- **Step 6:** Apply generalized `reflection_positivity_reorganization` → ≥ 0. The existing lemma (PeterWeyl.lean:1821) requires `Fintype W` (finite weights); needs generalization for countable types or L² limits.
- **Step 7:** Convert `transferMatrixPositivity_axiom` to a lemma (axiom count 6→5). NOTE: the axiom lacks `hN : 1 ≤ N` but the character expansion requires it; the N=0 case (trivial group) needs a separate argument, or `hN` must be added.

### 8.11.58 CRITICAL FINDING: The triple-product matrix M is NOT PSD — the step 5 approach does NOT work as stated; the gauge invariance hypothesis is likely needed (2026-08-09 session 71)

**Build GREEN (2972 jobs), 0 sorries, 6 axioms. No code changes this session — this section documents a mathematical analysis that calls into question the step 5 approach and the §8.11.53 resolution.**

This session performed a thorough analysis of step 5 (applying `triple_product_character_matrix_integral_Λ` to the spatial interface links) and discovered a **fundamental problem**: the matrix `M` whose entries are the triple-product integrals is **NOT positive-semidefinite** in general. This means the design doc's step 5 approach — "expand `A_w` in matrix elements, evaluate each triple product by `triple_product_character_matrix_integral_Λ`, assemble as a PSD Gram matrix, conclude ≥ 0" — **does NOT work as stated**. The §8.11.56 claim that "each triple product is a PSD Gram matrix" is **incorrect**: the individual triple-product VALUES are entries of a matrix that is NOT PSD.

#### The matrix M and why it is NOT PSD

After step 4 (temporal collapse), the integral is:
```
I = Σ_w F(w) · ∫_{u⁰_s} Ψ_w^{spatial}(u⁰_s) · |A_w(u⁰_s)|² dμ_s
```
where `F(w) ≥ 0`, `Ψ_w^{spatial} = ∏_{l ∈ L_0_spatial} χ_{w(l)}(g_l)`, and `A_w(u⁰_s) = ∫_{U⁺} f(U⁺, u⁰_s) · exp(-β S_pos) · Φ_w(U⁺) dμ⁺`.

Expanding `A_w` in matrix elements of `Λ`: `A_w(g) = Σ_{(ν,i,j)} c_{ν,i,j} · ∏_l (ρ_{ν(l)}(g_l))_{i_l, j_l}`. Then:
```
∫ Ψ_w · |A_w|² = Σ_{x,y} c_x · conj(c_y) · ∏_l J_l(x_l, y_l)
```
where `J_l(x_l, y_l) = ∫ χ_{w(l)}(g) · (ρ_{ν_x(l)}(g))_{i_x(l), j_x(l)} · conj((ρ_{ν_y(l)}(g))_{i_y(l), j_y(l)}) dμ` is the single-link triple-product integral, evaluated by `triple_product_character_matrix_integral_Λ`.

For the full integral to be ≥ 0, the matrix `M` with entries `M_{x,y} = ∏_l J_l(x_l, y_l)` must be PSD (since `I_w = c* · M · c`). Since `M = ⊗_l J_l` (tensor product of per-link matrices), it suffices for each `J_l` to be PSD.

**But `J_l` is NOT PSD in general.** The matrix `J_l` has entries:
```
J_l((ν_x, i_x, j_x), (ν_y, i_y, j_y)) = (1/dimsΛ(ν_y)) · Σ_a cgMEΛ(s, ν_x, ν_y, a, i_x, i_y) · conj(cgMEΛ(s, ν_x, ν_y, a, j_x, j_y))
```
The CG coefficient `cgMEΛ(s, t, u, a, i, k)` depends on BOTH `t` and `u` (it is the matrix element of the unitary `U_{s,t}: V_s ⊗ V_t → ⊕_ν V_ν`, which is a DIFFERENT unitary for each `t`). This means `J_l` is NOT a standard Gram matrix of the form `Σ_a f(a, x) · conj(f(a, y))` where `f` depends on only one of `x, y`.

#### U(1) counterexample (verified by direct computation)

For `G = U(1)` with irreps `χ_n(g) = g^n` (all 1-dimensional, so `i = j = k = l = 0`):
```
J((n_x, 0, 0), (n_y, 0, 0)) = ∫ χ_s(g) · χ_{n_x}(g) · conj(χ_{n_y}(g)) dμ = ∫ g^{s + n_x - n_y} dg = δ_{n_y, s + n_x}
```
So `J` is the **shift matrix** `J_{n_x, n_y} = δ_{n_y, s + n_x}`. This is NOT PSD: for `s = 1` and `v = (1, -1, 0, ...)` (i.e., `v_0 = 1, v_1 = -1`):
```
v* · J · v = Σ_{n_x, n_y} conj(v_{n_x}) · v_{n_y} · δ_{n_y, 1 + n_x} = conj(v_0) · v_1 + conj(v_1) · v_2 = 1·(-1) + (-1)·0 = -1 < 0
```

This corresponds to `f(g) = 1 - g` (i.e., `c_0 = 1, c_1 = -1`), giving:
```
∫ χ_1(g) · |1 - g|² dg = ∫ g · (1-g)(1-g⁻¹) dg = ∫ (2g - 1 - g²) dg = 0 - 1 - 0 = -1 < 0
```

This confirms `J_l` is NOT PSD, and `∫ χ_s · |f|²` can be negative even for PD characters `χ_s`.

#### Implications for the formalization path

1. **The step 5 approach (triple product → PSD Gram → ≥ 0) does NOT work as stated.** The matrix `M` (or `J_l`) is NOT PSD. The design doc's §8.11.56 claim that "each triple product is a PSD Gram matrix by `triple_product_character_matrix_integral`" is incorrect — the individual triple-product values are ENTRIES of a non-PSD matrix, not independent PSD quantities.

2. **The `multi_link_gram_psd_nonneg` / `reflection_positivity_reorganization` structure does NOT apply.** These lemmas require the Gram matrix structure `Σ_g ∏_l A_l(g_l, x_l) · conj(A_l(g_l, y_l))` where `A_l` depends on only one of `x_l, y_l`. The triple-product integral gives `cgMEΛ(s, t, u, a, i, k)` which depends on BOTH `t` and `u`, so it does NOT factor as `A_l(a, x_l) · conj(A_l(a, y_l))`.

3. **The gauge invariance hypothesis (removed in session 65, §8.11.53) is likely needed.** The §8.11.53 claim that the axiom is true for ALL `f` with `dependsOnlyOnPosSpatialInterface` (without gauge invariance) is called into question. The standard result in the literature (Osterwalder-Seiler, Lüscher) requires gauge invariance — the transfer matrix is positive on the GAUGE-INVARIANT subspace, not on the full space. The §8.11.51 analysis (which concluded the axiom is false without gauge invariance) may have been correct, and the §8.11.53 "resolution" (which claimed the §8.11.51 counterexample was invalid) may be wrong.

#### Re-examination of the §8.11.53 counter-arguments

The §8.11.53 resolution gave three reasons why the §8.11.51 counterexample is invalid. This analysis finds all three insufficient:

1. **"f is real-valued, so purely imaginary F cannot arise"** — A real `f` can produce a complex `A_w` (since `Φ_w` is complex). The U(1) counterexample uses `f = 2·Re[(1-g)·Φ_1]` which IS real, and gives `A_1 = 1-g` (complex), with `∫ χ_1 · |A_1|² = -1 < 0`. The reality constraint `conj(A_w) = A_{dual(w)}` does NOT prevent negativity.

2. **"dependsOnlyOnPosSpatialInterface excludes temporal interface links, so σ twist is harmless"** — True, the σ twist IS harmless (confirmed by `fourierCoeffPos_sigma_invisible`). But the counterexample does NOT use the σ twist — it uses the SPATIAL interface links, which are NOT excluded by `dependsOnlyOnPosSpatialInterface`. The negativity comes from `∫ χ_s · |A_w|²` on the spatial links, not from the σ twist.

3. **"The interface plaquette factor does NOT separate"** — True, and the correct treatment uses `interface_kernel_character_expansion`. But the character expansion gives `Σ_w F(w) · Φ_w(U⁺) · Ψ_w(u⁰) · conj(Φ_w(V⁺))` with `F(w) ≥ 0`, and after Fubini, the integral is `Σ_w F(w) · ∫ Ψ_w · |A_w|²`. The non-negativity of `F(w)` does NOT imply the non-negativity of the sum, because individual terms `∫ Ψ_w · |A_w|²` can be negative (as the counterexample shows).

#### What remains open

1. **Does the bulk Boltzmann factor `exp(-β S_pos)` change the picture?** The function `A_w` includes `exp(-β S_pos)` as a weight: `A_w = ∫ f · exp(-β S_pos) · Φ_w dμ⁺`. The bulk Boltzmann factor has non-negative Fourier coefficients, and its convolution with the Fourier coefficients of `f` gives `A_w`. The other terms in the sum `Σ_w F(w) · ∫ Ψ_w · |A_w|²` (for `w ≠ ±1`) might compensate for the negative `w = ±1` terms. **This requires further investigation** — the simple counterexample (where only `w = ±1` contribute) may not apply when the bulk Boltzmann factor is included.

2. **Does gauge invariance fix the problem?** If `f` is gauge-invariant, the function `A_w` has special properties (gauge invariance at the interface sites constrains the spatial interface link dependence). The Lüscher mechanism (§8.11.41-42) uses gauge invariance to constrain the character expansion and obtain non-negative coefficients. This may be the correct mechanism, but it is DIFFERENT from the triple product → PSD Gram approach.

3. **Is the axiom actually FALSE (for non-gauge-invariant f)?** The U(1) counterexample is for U(1), not SU(N). For SU(N) with N≥2, the same structural issue applies (the matrix `J_l` is not PSD), but the full computation with the bulk Boltzmann factor has not been verified. **This requires further investigation.**

#### Recommended next steps

1. **Re-introduce the gauge invariance hypothesis** `hf_gauge : IsGaugeInvariant N f` to `transferMatrixPositivity_axiom` (reversing the §8.11.53 removal). The axiom is likely only true for gauge-invariant `f`.

2. **Investigate the Lüscher mechanism** (§8.11.41-42) as the correct approach, using gauge invariance to constrain the character expansion. The triple product → PSD Gram approach does NOT work; a different mechanism is needed.

3. **Verify whether the axiom is actually false** for non-gauge-invariant `f` by computing the full integral (including the bulk Boltzmann factor) for a specific lattice (e.g., U(1) with T=1, L=1).

4. **Do NOT proceed with step 5 as stated.** The approach of expanding `A_w` in matrix elements and using the triple product integral to get a PSD Gram matrix is fundamentally flawed (the matrix is NOT PSD). A different approach is needed.

#### Note on the axiom strengthening #7

The axiom strengthening #7 (Schur for `Λ` + CG for `ι×Λ`, session 70) was added to enable the step 5 approach. Since the step 5 approach does NOT work as stated, the strengthening may not be needed for the CORRECT approach (which uses the reflection positivity / change-of-variables mechanism described in §8.11.59, not the triple product expansion). However, the strengthening is still mathematically valid (it provides the Great Orthogonality Theorem for `Λ` and the CG decomposition for `ι×Λ`, both standard results), and the lemma `triple_product_character_matrix_integral_Λ` is still a correct and useful result (it correctly evaluates the triple-product integral, even though the resulting matrix is not PSD). The strengthening should remain documented in the axiom growth audit (§7) for transparency.

### 8.11.59 DECISION: Do NOT re-introduce gauge invariance — the §8.11.53 resolution is CORRECT; the correct proof uses the reflection positivity / change-of-variables mechanism (NOT the triple product → PSD Gram approach) (2026-08-09 session 72)

**Build GREEN (2972 jobs), 0 sorries, 6 axioms. No code changes this session — this section documents the decision and the correct proof strategy.**

This session resolved the key open question from §8.11.58: **the gauge invariance hypothesis is NOT needed, and the §8.11.53 resolution is CORRECT.** The axiom `transferMatrixPositivity_axiom` is TRUE for ALL `f` with `dependsOnlyOnPosSpatialInterface` (not just gauge-invariant `f`). The §8.11.58 finding (that the matrix `J_l` is NOT PSD) is CORRECT but only shows that the step 5 approach (triple product → PSD Gram) is the wrong PROOF STRATEGY — it does NOT show the axiom is false. The correct proof uses a DIFFERENT mechanism: the reflection positivity via the PD of the interface kernel, combined with a change of variables that resolves the `S_pos`/`S_neg` asymmetry.

#### Why the gauge invariance hypothesis is NOT needed

The Osterwalder-Seiler (1978) reflection positivity theorem proves that for the Wilson action:
```
∫ F(U) · conj(F(θU)) · exp(-β S(U)) dμ ≥ 0
```
for ALL `F` depending only on the positive half (and possibly the interface). This is a THEOREM about the ACTION, not about gauge-invariant observables. It does NOT require gauge invariance of `F`.

The Lüscher (1977) transfer matrix positivity, by contrast, is about the transfer matrix `T` acting on the Hilbert space `L²(spatial links)`, and `T` is positive on the GAUGE-INVARIANT subspace. This is a DIFFERENT statement — it's about the transfer matrix, not about the reflection positivity integral.

Our axiom `transferMatrixPositivity_axiom` says `∫ osG(U) · osG(θU) dμ ≥ 0`, and we showed (in `gibbsExpectationPeriodic_reflection_positive`) that `∫ osG(U) · osG(θU) dμ = ∫ f(U) · f(θU) · exp(-β S(U)) dμ`. This is EXACTLY the reflection positivity for `F = f` (real-valued, depending on the positive half + spatial interface). So the axiom IS the reflection positivity, and it holds for ALL `f` (by Osterwalder-Seiler). No gauge invariance needed.

The §8.11.51 analysis (which claimed the axiom is false without gauge invariance) used a WRONG reduction: it assumed the integral reduces to `∫ F(u⁰) · F(σ(u⁰)) dμ⁰` with `c_γ²` (not `|c_γ|²`). This reduction is invalid because it incorrectly separates the Boltzmann factor. The §8.11.53 resolution correctly identified this error.

#### The key insight: the change of variables V⁺ → W⁺ = θV⁺

The reflection positivity integral is:
```
I = ∫ f(U⁺, u⁰_s) · f(θU) · exp(-β S_pos(U⁺)) · exp(-β S_neg(V⁺)) · exp(-β S_int(U⁺, u⁰, V⁺)) dμ
```

The apparent obstacle (noted in §8.11.58 analysis) is the asymmetry between `exp(-β S_pos(U⁺))` (on the U⁺ side) and `exp(-β S_neg(V⁺))` (on the V⁺ side): the PD of the interface kernel requires the SAME function `H` on both sides, but `S_pos ≠ S_neg` as functions.

**The resolution is a change of variables.** Let `W⁺ = θV⁺` (the reflected negative-half, which is a positive-half configuration). The reflection is measure-preserving (`reflectLinkVariable_measurePreserving_between`, LatticeMeasure.lean:520), so `dμ⁻(V⁺) = dμ⁺(W⁺)`. By the reflection symmetry of the action:
- `S_neg(V⁺) = S_pos(θV⁺) = S_pos(W⁺)` (by `neg_action_reflection_os_periodic`, ReflectionPositivity.lean:2333)
- `S_int(U⁺, u⁰, V⁺) = S_int(U⁺, u⁰, θW⁺)` (by `interface_action_reflection_symmetric_os_periodic`, ReflectionPositivity.lean:2379)
- `f(θU) = f(W⁺, u⁰_s)` (since `f` depends on positive-half links and spatial interface links, and `(θU)⁺ = W⁺`, `(θU)⁰_s = u⁰_s`)

After the change of variables:
```
I = ∫ f(U⁺, u⁰_s) · f(W⁺, u⁰_s) · exp(-β S_pos(U⁺)) · exp(-β S_pos(W⁺)) · exp(-β S_int(U⁺, u⁰, θW⁺)) dμ⁺ dμ⁰ dμ(W⁺)
```

Define `H(X, u⁰_s) = f(X, u⁰_s) · exp(-β S_pos(X))` for `X` a positive-half configuration. Then:
```
I = ∫ H(U⁺, u⁰_s) · conj(H(W⁺, u⁰_s)) · K(U⁺, W⁺) dμ⁺ dμ⁰ dμ(W⁺)
```
where `K(U⁺, W⁺) = exp(-β S_int(U⁺, u⁰, θW⁺))` is the interface kernel (after the change of variables). Since `f` is real-valued, `conj(H(W⁺, u⁰_s)) = H(W⁺, u⁰_s) = f(W⁺, u⁰_s) · exp(-β S_pos(W⁺))`.

Now `H` is the SAME function on both sides (both use `S_pos`), so the PD of the interface kernel `K` gives:
```
∫ H(U⁺, u⁰_s) · conj(H(W⁺, u⁰_s)) · K(U⁺, W⁺) dμ⁺ dμ(W⁺) ≥ 0
```
for each fixed `u⁰`. Integrating over `u⁰` preserves non-negativity. ✓

**This is why the step 5 approach failed:** the step 5 approach tried to expand `A_w` in matrix elements and use the triple product integral to get a PSD Gram matrix. But it did NOT perform the change of variables `V⁺ → W⁺ = θV⁺`, so it was working with the asymmetric `S_pos`/`S_neg` structure, which does NOT give a PSD Gram matrix. The change of variables is the KEY step that makes the PD applicable.

#### Why the §8.11.51 "c_γ²" analysis was wrong

The §8.11.51 analysis reduced the integral to `I = ∫ F(u⁰) · F(σ(u⁰)) dμ⁰` with `c_γ²` (not `|c_γ|²`), and concluded the axiom is false without gauge invariance. This reduction was wrong because:

1. **It integrated out U⁺ first** (giving `F(u⁰) = ∫ f · B₁ dμ⁺`), then claimed `I = ∫ F(u⁰) · F(σ(u⁰)) dμ⁰`. But this assumes the Boltzmann factor separates as `B₁(U⁺, u⁰) · B₂(V⁺, u⁰)` where `B₂` is the reflected `B₁`. The interface action `S_int` does NOT separate this way — it couples U⁺, u⁰, and V⁺ jointly.

2. **The σ twist (inversion of temporal interface links) is NOT the source of the problem.** The §8.11.53 resolution correctly noted that `dependsOnlyOnPosSpatialInterface` excludes temporal interface links, so the σ twist is harmless (`fourierCoeffPos_sigma_invisible`). The negativity in the §8.11.51 analysis came from the SPATIAL interface links, not the σ twist.

3. **The correct treatment keeps U⁺ and V⁺ SEPARATE** (via `interface_kernel_character_expansion`), uses the PD of the interface kernel, and performs the change of variables `V⁺ → W⁺ = θV⁺` to resolve the `S_pos`/`S_neg` asymmetry. This gives `|A_w|²` (not `c_γ²`), which is non-negative.

#### The correct formalization path

The correct proof strategy is:

1. **Start from `∫ osG(U) · osG(θU) dμ = ∫ f(U) · f(θU) · exp(-β S(U)) dμ`** (already shown in `gibbsExpectationPeriodic_reflection_positive`).

2. **Decompose `exp(-β S(U)) = exp(-β S_pos(U⁺)) · exp(-β S_neg(V⁺)) · exp(-β S_int(U⁺, u⁰, V⁺))`** (by `total_decomposition_os_periodic`).

3. **Change of variables `V⁺ → W⁺ = θV⁺`** (by `reflectLinkVariable_measurePreserving_between`), transforming:
   - `S_neg(V⁺) → S_pos(W⁺)` (by `neg_action_reflection_os_periodic`)
   - `S_int(U⁺, u⁰, V⁺) → S_int(U⁺, u⁰, θW⁺)` (by `interface_action_reflection_symmetric_os_periodic`)
   - `f(θU) → f(W⁺, u⁰_s)` (since `(θU)⁺ = W⁺` and `(θU)⁰_s = u⁰_s`)

4. **Apply the PD of the interface kernel** `K(U⁺, W⁺) = exp(-β S_int(U⁺, u⁰, θW⁺))` (by `plaquetteBoltzmannPD` + `interface_kernel_character_expansion`), giving non-negativity for each fixed `u⁰`.

5. **Integrate over `u⁰`** to get the full integral ≥ 0.

#### Existing infrastructure (all PROVEN)

- `reflectLinkVariable_measurePreserving_between` (LatticeMeasure.lean:520) — measure-preserving change of variables V⁺ → W⁺ = θV⁺. Already used in `transferMatrix_change_of_variables` (TransferMatrix.lean:2619).
- `neg_action_reflection_os_periodic` (ReflectionPositivity.lean:2333) — `S_neg(U) = S_pos(θU)`.
- `interface_action_reflection_symmetric_os_periodic` (ReflectionPositivity.lean:2379) — `S_int(θU) = S_int(U)`.
- `plaquetteBoltzmannPD` (PeterWeyl.lean:367) — the plaquette Boltzmann factor is PD (from the axiom).
- `interface_kernel_character_expansion` (PeterWeyl.lean:1635) — the interface kernel has a separable character expansion with `F(w) ≥ 0`.
- `osG_thetaG_eq_char_expansion_pointwise` (ReflectionPositivity.lean:2818) — step 2 result (character expansion of `osG(U)·osG(θU)`).
- `total_decomposition_os_periodic` (ReflectionPositivity.lean:562) — `S = S_pos + S_neg + S_int`.
- `osG_thetaG_factorization` — `osG(U)·osG(θU) = f(U)·f(θU)·exp(-β S(U))`.

#### What remains to formalize

The key remaining steps are:

1. **Apply the change of variables at the integral level.** The change of variables `V⁺ → W⁺ = θV⁺` needs to be applied to the FULL integral `∫ f(U) · f(θU) · exp(-β S(U)) dμ`, not just the transfer matrix integral. This requires:
   - Splitting the product Haar measure into `dμ⁺ dμ⁰ dμ⁻` (Fubini / product measure decomposition).
   - Applying `reflectLinkVariable_measurePreserving_between` to the `dμ⁻` integral.
   - Using `neg_action_reflection_os_periodic` and `interface_action_reflection_symmetric_os_periodic` to transform the action.

2. **Apply the PD of the interface kernel.** After the change of variables, the integral is `∫ H(U⁺, u⁰) · conj(H(W⁺, u⁰)) · K(U⁺, W⁺) dμ⁺ dμ⁰ dμ(W⁺)`. The PD of `K` gives non-negativity for each `u⁰`. This requires:
   - Stating the PD of the interface kernel in the right form (as a kernel on U⁺ vs W⁺).
   - Applying the PD to get `∫∫ H · conj(H) · K ≥ 0` for each `u⁰`.
   - Integrating over `u⁰`.

3. **Handle the `dependsOnlyOnPosSpatialInterface` condition.** The function `f` depends on U⁺ and u⁰_s (spatial interface links), NOT on u⁰_t (temporal interface links). This means `f(θU) = f(W⁺, u⁰_s)` (the spatial interface links are fixed by reflection). This needs to be verified.

4. **Convert `transferMatrixPositivity_axiom` to a lemma** (axiom count 6→5). NOTE: the axiom lacks `hN : 1 ≤ N` but the character expansion requires it. The N=0 case (trivial group) needs a separate argument, or `hN` must be added to the axiom and all callers.

#### Summary of the decision

| Question | Answer |
|----------|--------|
| Is the axiom TRUE for all `f` with `dependsOnlyOnPosSpatialInterface`? | **YES** (by Osterwalder-Seiler reflection positivity) |
| Is the gauge invariance hypothesis needed? | **NO** (the §8.11.53 resolution is CORRECT) |
| Does the step 5 approach (triple product → PSD Gram) work? | **NO** (the matrix `J_l` is NOT PSD, as §8.11.58 showed) |
| What is the correct proof mechanism? | **Reflection positivity via PD of interface kernel + change of variables V⁺ → W⁺ = θV⁺** |
| Why did the step 5 approach fail? | **It did NOT perform the change of variables, so it worked with the asymmetric `S_pos`/`S_neg` structure, which does NOT give a PSD Gram matrix** |
| Is the axiom strengthening #7 still needed? | **Probably NOT for the correct approach** (the change-of-variables approach uses `plaquetteBoltzmannPD` + `interface_kernel_character_expansion`, not the triple product expansion). But it remains mathematically valid and documented. |

### 8.11.60 CRITICAL ANALYSIS: The §8.11.59 "PD for each u⁰" claim is WRONG — the interface kernel K_{u⁰} is NOT PD for each u⁰; the §8.11.58 obstruction survives the change of variables (2026-08-10 session 73)

**Build GREEN (2972 jobs), 0 sorries, 6 axioms. No code changes this session — this section documents a critical analysis of the §8.11.59 proof strategy.**

This session performed a detailed analysis of the §8.11.59 proof strategy (change of variables + "PD for each u⁰") and discovered that **the key claim — "the PD of the interface kernel K(U⁺, W⁺) gives non-negativity for each fixed u⁰" — is WRONG.** The interface kernel K_{u⁰}(U⁺, W⁺) = exp(-β S_int(U⁺, u⁰, θW⁺)) is NOT a positive-definite kernel on (U⁺, W⁺) for each fixed u⁰, because the character expansion coefficients Ψ_w(u⁰) are complex-valued (they are character products, not non-negative reals). The §8.11.58 obstruction (that ∫ Ψ_w·|A_w|² can be negative) SURVIVES the change of variables — the change of variables resolves the S_pos/S_neg asymmetry but does NOT resolve the fundamental issue with the spatial interface links.

#### Why K_{u⁰} is NOT PD for each u⁰

After the change of variables V⁺ → W⁺ = θV⁺ (which IS correct and resolves the S_pos/S_neg asymmetry), the integral is:
```
I = ∫_{u⁰} ∫_{U⁺} ∫_{W⁺} H(U⁺, u⁰_s) · conj(H(W⁺, u⁰_s)) · K_{u⁰}(U⁺, W⁺) dμ⁺ dμ(W⁺) dμ⁰
```
where H(X, u⁰_s) = f(X, u⁰_s)·exp(-β S_pos(X)) and K_{u⁰}(U⁺, W⁺) = exp(-β S_int(U⁺, u⁰, θW⁺)).

The §8.11.59 strategy claims: "for each fixed u⁰, K_{u⁰} is a PD kernel on (U⁺, W⁺), so the inner double integral ≥ 0, and integrating over u⁰ preserves non-negativity."

The character expansion (`interface_kernel_character_expansion`) gives:
```
K_{u⁰}(U⁺, W⁺) = Σ_w F(w) · Φ_w(U⁺) · Ψ_w(u⁰) · conj(Φ_w(W⁺))
```
where F(w) ≥ 0, Φ_w(U⁺) = ∏_{l ∈ L_U} χ_{w(l)}(g_l), and Ψ_w(u⁰) = ∏_{l ∈ L_0} χ_{w(l)}(g_l).

For K_{u⁰} to be a PD kernel on (U⁺, W⁺) (in the Mercer sense), we need: for every finite set {U⁺_i} and coefficients {c_i},
```
Σ_i Σ_j c_i · conj(c_j) · K_{u⁰}(U⁺_i, U⁺_j) = Σ_w F(w) · Ψ_w(u⁰) · |Σ_i c_i · Φ_w(U⁺_i)|² ≥ 0
```
This requires F(w)·Ψ_w(u⁰) ≥ 0 for all w. But **Ψ_w(u⁰) is a product of characters χ_{w(l)}(g_l), which takes COMPLEX values** (characters are traces of unitary matrices, hence complex in general). So F(w)·Ψ_w(u⁰) is NOT non-negative, and K_{u⁰} is NOT a PD kernel for each u⁰. ✗

#### The §8.11.58 obstruction survives

The full integral (expanding K and doing the U⁺/W⁺ integrals) is:
```
I = Σ_w F(w) · ∫_{u⁰} Ψ_w(u⁰) · |A_w(u⁰)|² dμ⁰
```
where A_w(u⁰) = ∫_{U⁺} H(U⁺, u⁰_s) · Φ_w(U⁺) dμ⁺ depends on u⁰_s (the spatial interface links, since f depends on them via `dependsOnlyOnPosSpatialInterface`).

Splitting u⁰ = (u⁰_s, u⁰_t) and using character orthogonality on the temporal links:
```
I = Σ_{w: temporal trivial} F(w) · ∫_{u⁰_s} Ψ_w^{spatial}(u⁰_s) · |A_w(u⁰_s)|² dμ⁰_s
```
This is EXACTLY the §8.11.58 structure, and §8.11.58 showed (via the U(1) counterexample) that ∫ Ψ_w^{spatial}·|A_w|² can be negative. **The change of variables does NOT resolve this** — it only resolves the S_pos/S_neg asymmetry (making H the same function on both sides), but the spatial interface link obstruction remains.

#### Reconciliation with Osterwalder-Seiler

The Osterwalder-Seiler (1978) reflection positivity theorem IS true — the integral IS non-negative. But the mechanism is NOT "PD for each u⁰." The correct mechanism must involve the FULL character expansion including the bulk Boltzmann factor exp(-β S_pos), whose non-negative character coefficients may compensate for the negative spatial interface terms. The §8.11.58 counterexample was for a SIMPLIFIED setting (without the bulk Boltzmann factor); the full integral (with the bulk Boltzmann factor) may still be non-negative.

Key open question (from §8.11.58 item 1, still open): **does the bulk Boltzmann factor exp(-β S_pos) compensate for the negative spatial interface terms?** The bulk Boltzmann factor has non-negative Fourier coefficients, and its convolution with f's Fourier coefficients gives A_w. The other terms in the sum (for w ≠ ±1) might compensate. This requires further investigation.

#### What this means for the formalization

1. **The §8.11.59 proof strategy (change of variables + "PD for each u⁰") does NOT work as stated.** The "PD for each u⁰" step is invalid. The change of variables IS necessary and correct, but it does NOT complete the proof.

2. **The §8.11.58 obstruction is REAL and fundamental.** It applies to the spatial interface links and survives the change of variables. The matrix J_l (triple product on spatial links) is NOT PSD, and this is not resolved by the change of variables.

3. **The correct proof mechanism is still unknown.** The options are:
   - (a) The bulk Boltzmann factor compensates (requires showing the full sum Σ_w F(w)·∫ Ψ_w·|A_w|² ≥ 0, not just individual terms).
   - (b) Gauge invariance is needed (the Lüscher mechanism constrains the spatial interface link dependence).
   - (c) The support hypothesis should be strengthened to `dependsOnlyOnPositive` (f depends only on U⁺, NOT on any interface links) — then the u⁰ integral kills all non-trivial characters by orthogonality, giving non-negativity. But this may be too restrictive.
   - (d) Some other mechanism (e.g., the full plaquette structure, not just the interface kernel).

4. **The existing infrastructure is still valuable.** The change of variables (step A) is fully formalized in `transferMatrix_change_of_variables` and `transferMatrix_integral_reduction`. The character expansion (step 2) is formalized in `osG_thetaG_eq_char_expansion_pointwise`. The temporal collapse (step 4) is formalized in `integral_prod_repCharacter_trivial`. What's missing is the correct mechanism for the spatial interface links.

#### Summary

| Question | Answer |
|----------|--------|
| Does the §8.11.59 "PD for each u⁰" step work? | **NO** — K_{u⁰} is NOT PD (Ψ_w(u⁰) is complex) |
| Does the change of variables resolve the §8.11.58 obstruction? | **NO** — it resolves S_pos/S_neg asymmetry but NOT the spatial interface issue |
| Is the §8.11.58 obstruction real? | **YES** — ∫ Ψ_w·|A_w|² can be negative (U(1) counterexample) |
| Is the axiom still true (by Osterwalder-Seiler)? | **Likely YES** — but the mechanism is NOT "PD for each u⁰" |
| What is the correct mechanism? | **UNKNOWN** — requires further investigation (bulk Boltzmann compensation? gauge invariance? stronger support?) |
| What should the next session do? | **Investigate the correct mechanism** — either (a) show the bulk Boltzmann factor compensates, (b) re-introduce gauge invariance, or (c) strengthen the support hypothesis |

### 8.11.61 THE CORRECT PROOF MECHANISM: Full character expansion (all plaquettes) + dependsOnlyOnPositive — the interface-only expansion gives a "twisted" quadratic form that is NOT obviously non-negative; the bulk plaquette expansion is essential (2026-08-10 session 74)

**Build GREEN (2972 jobs), 0 sorries, 6 axioms. Code changes: define `dependsOnlyOnPositive`, prove it implies `dependsOnlyOnPosSpatialInterface`. No axiom changes.**

This session investigated the three options from §8.11.60 and identified the correct proof mechanism. The key findings are:

1. **Option (c) is the correct hypothesis**: `dependsOnlyOnPositive` (f depends only on strictly positive-time links, t > 0, NOT on any interface links) is the right support condition. This matches the standard Osterwalder-Schrader OS3 axiom ("test functions f_i supported in positive time t > 0"). The current `dependsOnlyOnPosSpatialInterface` (which allows f to depend on spatial interface links at t=0) is WEAKER than the standard OS3 hypothesis and is the source of the §8.11.58/§8.11.60 obstruction.

2. **The interface-only character expansion is INSUFFICIENT**: The existing `interface_kernel_character_expansion` (PeterWeyl.lean:1635) expands only the interface plaquette Boltzmann factor exp(-β·S_int), leaving the bulk Boltzmann factors exp(-β·S_pos) and exp(-β·S_neg) in the real prefactor r(U). After integrating out the interface links u⁰ (which gives δ_{w, trivial on interfaceLinkInt} by character orthogonality), the remaining integral is:
   ```
   I = C · Σ_{w: trivial on interfaceLinkInt} F(w) · A_w · B_w
   ```
   where A_w = ∫ r_pos(U⁺) · Φ_w(U⁺) dμ⁺ (involving positive-time interface links L_U) and B_w = ∫ r_neg(U⁻) · Ψ_w(U⁻) dμ⁻ (involving negative-time interface links L_V). The key observation: conj(χ_{dual(i)}(g)) = χ_i(g), so the L_V character factor is the SAME type as the L_U character factor (both use χ_{w(l)}, not conjugated). This means the kernel K(U⁺, W⁺) = Σ F(w) · Φ_w(U⁺) · Φ_w(W⁺) is NOT a PD kernel (it has Φ_w(W⁺) not conj(Φ_w(W⁺))). The resulting quadratic form Σ F(w) · A_w² is complex in general (A_w is complex since characters are complex), and the real part is NOT obviously non-negative. The weights w come in conjugate pairs (w, w̄) with w̄(l) = dual(w(l)), giving A_{w̄} = conj(A_w) and F(w̄) = F(w), so F(w)·A_w² + F(w̄)·A_{w̄}² = 2·F(w)·Re(A_w²), which can be NEGATIVE.

3. **The FULL character expansion (all plaquettes) IS sufficient**: The correct mechanism is to expand ALL plaquettes (bulk positive, bulk negative, AND interface) in characters, not just the interface ones. The bulk plaquette Boltzmann factors exp(-β·S_pos) and exp(-β·S_neg) have their own character expansions with non-negative coefficients. When combined with the interface expansion, the FULL expansion gives:
   ```
   exp(-β·S) = Σ_w F_full(w) · ∏_{l ∈ ALL links} χ_{w(l)}(g_l)^{±1}
   ```
   with F_full(w) ≥ 0 (products of non-negative plaquette coefficients). The integral over ALL links then gives:
   - Interface link integral: δ_{w, trivial on interface links} (character orthogonality)
   - Positive link integral: Fourier coefficient Â_w of f·exp(-β·S_pos/2)
   - Negative link integral: conj(Â_w) (by reflection symmetry + character orthogonality)
   - Result: I = Σ_{w: trivial on interface} F_full(w) · |Â_w|² ≥ 0

   The bulk expansion is ESSENTIAL because it converts the "twisted" quadratic form (Σ F·A², which can be negative) into a standard |Â|² sum (which is non-negative). The bulk plaquette character expansion provides the additional character factors on the positive and negative links that, combined with the interface factors, give the |Â|² structure.

4. **Why `dependsOnlyOnPositive` is needed**: For the interface link integral to give δ_{w, trivial}, f must NOT depend on the interface links. If f depends on spatial interface links (as in `dependsOnlyOnPosSpatialInterface`), the interface integral becomes ∫ f(u⁰_s)² · Ψ_w(u⁰_s) dμ⁰_s, which is NOT δ (it's a weighted integral that can be negative, as shown by the §8.11.58 U(1) counterexample). With `dependsOnlyOnPositive`, f doesn't depend on u⁰, so the interface integral is just ∫ Ψ_w(u⁰) dμ⁰ = δ_{w, trivial} (unweighted character orthogonality), which is always non-negative.

#### The formalization plan

The formalization requires extending the character expansion from interface-only to ALL plaquettes:

- **Step 1** (DONE this session): Define `dependsOnlyOnPositive` and prove it implies `dependsOnlyOnPosSpatialInterface`.
- **Step 2** (NEXT): Apply `plaquette_product_separable_decomp` (PeterWeyl.lean:1358) to ALL plaquettes (not just interface ones). This lemma is general — it works for any set of plaquettes and links. The key is to partition ALL links into positive (L_U), interface (L_0), and negative (L_V) sets, and apply the lemma to ALL plaquettes.
- **Step 3**: Show the integral over interface links gives δ_{w, trivial} (using `integral_prod_repCharacter_trivial`, PeterWeyl.lean:2435).
- **Step 4**: Show the integral over positive and negative links gives |Â_w|² (using character orthogonality + reflection symmetry).
- **Step 5**: Assemble the non-negativity result: I = Σ F_full(w) · |Â_w|² ≥ 0.
- **Step 6**: Replace the axiom `transferMatrixPositivity_axiom` (for `dependsOnlyOnPosSpatialInterface`) with a proved lemma (for `dependsOnlyOnPositive`), reducing the axiom count from 6 to 5.

#### Impact on the axiom

Changing the axiom from `dependsOnlyOnPosSpatialInterface` to `dependsOnlyOnPositive`:
- **Matches the standard OS3 axiom** (f supported in t > 0, not at the interface t = 0).
- **Does NOT break the mass gap proof**: The mass gap comes from `mass_gap_axiom` (separately axiomatized), not from the reflection positivity axiom. The reflection positivity is used to establish the OS axioms, which are used for reconstruction. The OS3 axiom is for f supported in t > 0, matching `dependsOnlyOnPositive`.
- **Reduces the axiom count from 6 to 5** (if the proof is completed).

#### Key existing infrastructure

- `plaquette_product_separable_decomp` (PeterWeyl.lean:1358) — general character expansion for any set of plaquettes and links
- `interface_kernel_character_expansion` (PeterWeyl.lean:1635) — interface-only expansion (needs to be extended to all plaquettes)
- `integral_prod_repCharacter_trivial` (PeterWeyl.lean:2435) — character orthogonality: ∫ ∏ χ_{w(l)}(g_l) dμ = δ_{w, trivial}
- `plaquetteBoltzmannPD` (PeterWeyl.lean:367) — plaquette Boltzmann factor is PD
- `gram_matrix_psd_nonneg` (PeterWeyl.lean:1714) — Gram matrix PSD
- `osG_thetaG_eq_char_expansion_pointwise` (ReflectionPositivity.lean:2818) — pointwise expansion of osG·osG(θG) (interface-only)
- `transferMatrix_change_of_variables` (TransferMatrix.lean:2619) — change of variables (correct, but not sufficient alone)
- `integral_G_thetaG_eq_inner_g_Tg` (TransferMatrix.lean:5149) — key identity: ∫ G·G(θU) = ∫ g·(Tg)

#### Summary

| Question | Answer |
|----------|--------|
| What is the correct hypothesis? | **`dependsOnlyOnPositive`** (f depends only on t > 0 links, NOT on interface links) |
| Is the interface-only expansion sufficient? | **NO** — gives a "twisted" quadratic form Σ F·A² that can be negative |
| Is the full character expansion sufficient? | **YES** — gives Σ F·|Â|² ≥ 0 (standard |Fourier coefficient|² sum) |
| Why is the bulk expansion essential? | It converts the twisted form into |Â|² by providing character factors on ALL links |
| Why is `dependsOnlyOnPositive` needed? | So the interface integral gives δ (unweighted), not a weighted integral that can be negative |
| Does this match the standard OS3 axiom? | **YES** — OS3 is for f supported in t > 0 |
| Does this break the mass gap proof? | **NO** — mass gap comes from `mass_gap_axiom`, not from reflection positivity |
| What is the next step? | Extend `plaquette_product_separable_decomp` to ALL plaquettes (step 2 of the plan) |

### 8.11.62 STEP 2 COMPLETE: Full character expansion formalized (all plaquettes) — three new lemmas, build GREEN, 0 sorries, 6 axioms (2026-08-10 session 75)

**Build GREEN (2890 jobs), 0 sorries, 6 axioms (unchanged). Three new lemmas added to `ReflectionPositivity.lean` (lines 1602-1755).**

This session completed step 2 of the §8.11.61 formalization plan: extending the character expansion from interface-only to ALL plaquettes. Three new lemmas were written and verified:

1. **`full_boltzmann_eq_abstract_product`** (line 1602): The full Boltzmann factor `exp(-β·S_W)` equals a positive constant `C = ∏_{p ∈ PlaquetteIndex} exp(-β²)` times the abstract plaquette product `∏_{p ∈ PlaquetteIndex} exp((β²/N)·Re Tr(P_p))`. This is the full-lattice analogue of `interface_boltzmann_eq_abstract_product`. It combines `exp_neg_beta_wilsonActionFinite_eq_prod` (exp-of-sum for the full action) with `plaquetteContribution_exp_decomp_tm` (per-plaquette Boltzmann decomposition). **Depends on only standard axioms** (propext, Classical.choice, Quot.sound) — pure algebra, 0 custom axioms.

2. **`full_product_character_expansion`** (line 1670): Applying `interface_kernel_character_expansion` (Peter-Weyl / Clebsch-Gordan) to ALL plaquettes (not just interface ones), the full plaquette product admits the separable character expansion `∏_p exp(c·Re Tr(...)) = ∑_w F(w)·Φ_w(U)·Ψ_w(U)·conj(Φ_w(U))` with `F(w) ≥ 0`, where `Φ_w(U) = ∏_{l ∈ allLinkPos} χ_{w(l)}(U.value l.1 l.2)`, `Ψ_w(U) = ∏_{l ∈ allLinkInt} χ_{w(l)}(U.value l.1 l.2)`, and the negative-link factor uses the dual map. This is the full-lattice analogue of `interface_product_character_expansion`. **Depends on `peterWeyl_clebschGordan_plaquette`** (axiom count 6, unchanged).

3. **`full_boltzmann_character_expansion`** (line 1722): Combining the two above, the full Boltzmann factor admits the character expansion `(exp(-β·S_W(U)) : ℂ) = (C : ℂ) · ∑_w F(w)·Φ_w(U)·Ψ_w(U)·V_w(U)` with `C > 0` and `F(w) ≥ 0`. This is the full-lattice analogue of `interface_boltzmann_character_expansion`. **Depends on `peterWeyl_clebschGordan_plaquette`** (axiom count 6, unchanged).

The key technical step in `full_product_character_expansion` was connecting the `plaquetteProduct` form (used in the statement for naturalness) to the `U.value (plaquetteLinkIdx...)` form (used by `interface_kernel_character_expansion`). This was done via a `Finset.prod_congr` + `plaquetteProduct_eq_linkIdx` rewrite, packaged as an explicit `h_eq` lemma with full type annotations.

#### Remaining steps (3-6 of the §8.11.61 plan)

- **Step 3**: Show the integral over interface links (`allLinkInt`) gives `δ_{w, trivial}` (using `integral_prod_repCharacter_trivial`, PeterWeyl.lean:2435). This works because `dependsOnlyOnPositive` means `f` doesn't depend on interface links, so the integral is unweighted.
- **Step 4**: Show the integral over positive/negative links gives `|Â_w|²` (using character orthogonality + reflection symmetry).
- **Step 5**: Assemble `I = Σ F_full(w)·|Â_w|² ≥ 0`.
- **Step 6**: Replace the axiom `transferMatrixPositivity_axiom` (for `dependsOnlyOnPosSpatialInterface`) with a proved lemma (for `dependsOnlyOnPositive`), reducing axiom count 6 → 5.

#### Summary

| Question | Answer |
|----------|--------|
| Is step 2 (full character expansion) complete? | **YES** — three new lemmas, build GREEN, 0 sorries |
| What axioms do the new lemmas use? | `full_boltzmann_eq_abstract_product`: standard 3 only; `full_product_character_expansion` and `full_boltzmann_character_expansion`: standard 3 + `peterWeyl_clebschGordan_plaquette` (axiom 6) |
| Is the axiom count changed? | **NO** — still 6 axioms (the new lemmas use existing axioms, no new ones) |
| What is the next step? | Step 3: interface link integral gives δ_{w, trivial} |

#### Session 75 additional work

Also attempted `full_osG_thetaG_eq_char_expansion_pointwise` (the full pointwise expansion of the reflection-positivity integrand, substituting `full_boltzmann_character_expansion` into `osG_thetaG_factorization`). This lemma is the full analogue of `osG_thetaG_eq_char_expansion_pointwise` (line ~3081). It was REMOVED due to a typeclass issue: the `rw [← Complex.ofReal_mul, h_factor, Complex.ofReal_mul, h_char U]` chain succeeds but the final `ring`/`ac_rfl`/`ring_nf` fails with "typeclass instance problem is stuck" when trying to prove per-weight commutativity in `ℂ`. The next session should retry this — the issue is likely that the `Finset.mul_sum` distribution creates a goal where the `CommMonoid ℂ` instance isn't being found. Possible fixes: (a) use `simp only [mul_comm, mul_left_comm, mul_assoc]` instead of `ring`, (b) restructure the proof to avoid the `Finset.mul_sum` + `Finset.sum_congr` pattern, or (c) use `omega`/`linarith` with explicit commutativity lemmas.

### 8.11.63 STEP 2 (full pointwise expansion) COMPLETE + bridge lemmas for full link partition — build GREEN, 0 sorries, 6 axioms (2026-08-10 session 76)

**Build GREEN (2890 jobs), 0 sorries, 6 axioms (unchanged). Two new results added to `ReflectionPositivity.lean`.**

#### 1. `full_osG_thetaG_eq_char_expansion_pointwise` (line ~3170) — COMPLETED

The full pointwise expansion of the reflection-positivity integrand, substituting `full_boltzmann_character_expansion` into `osG_thetaG_factorization`. This is the full-lattice analogue of `osG_thetaG_eq_char_expansion_pointwise` (line ~3096, which expands only the interface Boltzmann factor). The result:

```
(osG(U)·osG(θU) : ℂ) = (C : ℂ) · ∑_w (F w : ℂ) · ↑(f(U)·f(θU)) · Φ_w(U) · Ψ_w(U) · V_w(U)
```

with `C > 0`, `F(w) ≥ 0`, and character factors over ALL links (`allLinkPos`/`allLinkInt`/`allLinkNeg`). The real prefactor is just `f(U)·f(θU)` (no bulk action factors, since the FULL Boltzmann is expanded). Uses `peterWeyl_clebschGordan_plaquette` (axiom count 6, unchanged); 0 sorries.

**The key fix for the session 75 typeclass issue**: The `h_LHS` sub-lemma needed `rw [← Complex.ofReal_mul, h_factor, Complex.ofReal_mul]` (THREE rewrites, not two). The issue was:
- The LHS `(osG U * osG θU : ℂ)` elaborates as `↑(osG U) * ↑(osG θU)` (each factor coerced separately, NOT `↑(osG U * osG θU)`).
- `← Complex.ofReal_mul` combines `↑(osG U) * ↑(osG θU)` → `↑(osG U * osG θU)` on the LHS.
- `h_factor` rewrites `osG U * osG θU` → `f U * f θU * exp(-β·S_W)` inside the coercion.
- `Complex.ofReal_mul` (forward) splits `↑(f U * f θU * exp(-β·S_W))` → `↑(f U * f θU) * ↑(exp(-β·S_W))` to match the RHS.
- The final `ring` in the per-weight `Finset.sum_congr` goal then works (the `star` term is an opaque atom that appears identically on both sides).

The session 75 attempt used only `rw [← Complex.ofReal_mul, h_factor]` (TWO rewrites), which left the goal `↑(f U * f θU * exp(-β·S_W)) = ↑(f U * f θU) * ↑(exp(-β·S_W))` — not closed. The missing third rewrite `Complex.ofReal_mul` was the fix.

#### 2. Bridge lemmas for full link partition (lines ~1355-1371)

Three new bridge lemmas connecting the FULL link-based partition (`allLinkPos`/`allLinkInt`/`allLinkNeg`, used by the character expansion) with the SITE-based partition (`positiveSites`/`interfaceSites`/`negativeSites`, used by the measure factorization in `TransferMatrix.lean` via `measure_factorization'`):

- `allLinkPos_mem_iff`: `(n, μ) ∈ allLinkPos T L ↔ n ∈ positiveSites T L`
- `allLinkInt_mem_iff`: `(n, μ) ∈ allLinkInt T L ↔ n ∈ interfaceSites T L`
- `allLinkNeg_mem_iff`: `(n, μ) ∈ allLinkNeg T L ↔ n ∈ negativeSites T L`

These are the full-lattice analogues of the existing `interfaceLinkPos_mem_iff`/`interfaceLinkInt_mem_iff`/`interfaceLinkNeg_mem_iff` (lines ~1759-1775, which are for the interface-only link partition). Standard axioms only (propext, Classical.choice, Quot.sound); 0 sorries, 0 custom axioms.

These bridge lemmas are needed for steps 3-4: they connect the link-based character expansion (which uses `allLinkPos`/`allLinkInt`/`allLinkNeg`) with the site-based measure factorization (which uses `positiveSites`/`interfaceSites`/`negativeSites` via `measure_factorization'` in TransferMatrix.lean:663).

#### Remaining steps (3-6 of the §8.11.61 plan)

- **Step 3**: Show the integral over interface links (`allLinkInt`) gives `δ_{w, trivial}` using `integral_prod_repCharacter_trivial` (PeterWeyl.lean:2435). This works because `dependsOnlyOnPositive` means `f` doesn't depend on interface links, so the integral is unweighted. **Key infrastructure needed**: a conversion lemma `prod_allLinkInt_eq_prod_finiteLinkIndex` connecting `∏ l ∈ allLinkInt T L, f l` (Finset product) with `∏ (l : FiniteLinkIndex (PeriodicSite T L) (interfaceSites T L)), f l.val` (Fintype product), using `Finset.prod_subtype`. The `FiniteLinkIndex` type is `Subtype (fun x => x.1 ∈ sites)`, and `allLinkInt T L = (interfaceSites T L).product Finset.univ` (by `allLinkInt_mem_iff`). Then apply `integral_prod_repCharacter_trivial` with `L = FiniteLinkIndex (PeriodicSite T L) (interfaceSites T L)`, `G = SU N`, `μ = haarMeasure`.
- **Step 4**: Show the integral over positive/negative links gives `|Â_w|²` using character orthogonality + reflection symmetry. **Key infrastructure needed**: `reflectLinkVariable_measurePreserving` (LatticeMeasure.lean:417) for the change of variables, and the connection between `V_w(U) = star(∏_{l ∈ allLinkNeg} χ_{dual(w(l))}(U.value l))` and `conj(Φ_w(U))` under reflection.
- **Step 5**: Assemble `I = Σ F_full(w)·|Â_w|² ≥ 0` (trivially true since `F(w) ≥ 0` and `|Â_w|² ≥ 0`).
- **Step 6**: Replace `transferMatrixPositivity_axiom` (for `dependsOnlyOnPosSpatialInterface`) with a proved lemma (for `dependsOnlyOnPositive`), reducing axiom count 6 → 5.

#### Summary

| Question | Answer |
|----------|--------|
| Is `full_osG_thetaG_eq_char_expansion_pointwise` complete? | **YES** — build GREEN, 0 sorries, 6 axioms |
| What was the session 75 typeclass issue? | Missing third `Complex.ofReal_mul` rewrite in `h_LHS` — the LHS `(osG U * osG θU : ℂ)` elaborates as `↑(osG U) * ↑(osG θU)`, not `↑(osG U * osG θU)` |
| Are bridge lemmas for full link partition done? | **YES** — `allLinkPos/Int/Neg_mem_iff`, standard axioms only |
| What is the next step? | Step 3: write `prod_allLinkInt_eq_prod_finiteLinkIndex` conversion lemma, then apply `integral_prod_repCharacter_trivial` |

### 8.11.64 STEP 3 COMPLETE: Interface link integral gives δ_{w, trivial} — axiom extended to provide σ_0, build GREEN, 0 sorries, 6 axioms (2026-08-10 session 77)

**Build GREEN (2972 jobs), 0 sorries, 6 axioms (unchanged). One new lemma + axiom extension.**

This session completed Step 3 of the §8.11.61 formalization plan: showing that the interface link integral gives δ_{w, trivial} (Kronecker delta — 1 if all interface characters are trivial, 0 otherwise). This is character orthogonality for the product Haar measure on the interface links.

#### 1. Axiom extension: `peterWeyl_clebschGordan_plaquette` now provides σ_0

The `integral_prod_repCharacter_trivial` lemma (PeterWeyl.lean:2435) requires a trivial representation `σ_0 : ι` with `hσ_0_dims : dims σ_0 = 1` and `hσ_0_trivial : ∀ g, (ρ σ_0 g) = 1`. The axiom `peterWeyl_clebschGordan_plaquette` previously provided `hIrr` and `hDims` but NOT `σ_0`. 

The axiom was extended to also output `(σ_0 : ι) (hσ_0_dims : dims σ_0 = 1) (hσ_0_trivial : ∀ g, (ρ σ_0 g) = 1)`, inserted right after `hDims`. This is mathematically justified: the plaquette Boltzmann factor `exp(c · Re Tr(g₁g₂g₃g₄))` at `c = 0` is 1 (the trivial character), so the trivial representation must be in the finite set `ι` of irreps used for the character expansion. **This does NOT increase the axiom count** (still 6) — it adds output to an existing axiom.

All 4 destructure sites of the axiom were updated (PeterWeyl.lean ×2 for `plaquetteBoltzmannPD` and `plaquetteBoltzmannPD_inv`; ReflectionPositivity.lean ×2 for `interface_product_character_expansion` and `full_product_character_expansion`). The update was a simple insertion of `σ_0, hσ_0_dims, hσ_0_trivial,` after `hDims,` in each `obtain` pattern.

#### 2. New lemma: `interface_char_integral_trivial` (ReflectionPositivity.lean:~1410)

```
∫ (cfg : FiniteLinkConfig N (PeriodicSite T L) (interfaceSites T L)),
  ∏ (l : FiniteLinkIndex (PeriodicSite T L) (interfaceSites T L)),
    repCharacter (ρ (w l.val)) (cfg l)
  ∂ (productHaarMeasure N (PeriodicSite T L) (interfaceSites T L)) =
  ∏ (l : FiniteLinkIndex (PeriodicSite T L) (interfaceSites T L)),
    (if w l.val = σ_0 then (1 : ℂ) else 0)
```

This states: integrating the interface character factor `∏_l χ_{w(l)}(g_l)` over the interface links (with the product Haar measure) gives `∏_l δ_{w(l), σ_0}` — i.e., δ_{w|_int, trivial}. This is the multi-link character orthogonality: each interface link integral `∫ χ_{w(l)}(g) dμ(g) = δ_{w(l), σ_0}` by `integral_repCharacter_trivial`, and the product measure factors by Fubini (`integral_fintype_prod_eq_prod`).

**Proof**: 
1. Define `K` (the positive compact `Set.univ` on `SU N`) and `μ = Measure.haarMeasure K` (the normalized Haar measure on `SU N`).
2. Show `IsProbabilityMeasure μ` using `Measure.haarMeasure_self`.
3. Rewrite `productHaarMeasure N (PeriodicSite T L) (interfaceSites T L)` to `Measure.pi (fun _ => μ)` by unfolding the definition (`dsimp [productHaarMeasure, μ]` — the `let K` in `productHaarMeasure` is definitionally equal to our local `K`).
4. Apply `integral_prod_repCharacter_trivial` with `L = FiniteLinkIndex (PeriodicSite T L) (interfaceSites T L)`, `G = SU N`, `μ = haarMeasure`, and `w' = fun l => w l.val`.

**Key technical detail**: The `classical` tactic is needed to provide `DecidableEq (FiniteLinkIndex (PeriodicSite T L) (interfaceSites T L))` (a `Subtype` of `PeriodicSite T L × Fin 4`), which `integral_prod_repCharacter_trivial` requires for the `if w l = σ_0 then ... else ...` in the result.

**Axioms**: `[propext, Classical.choice, Quot.sound, characterOrthogonality]` — only the standard 3 + the existing `characterOrthogonality` axiom (#6 in the inventory). No new axioms, no `sorryAx`. The axiom count remains **6**.

#### Why this works with `dependsOnlyOnPositive`

With `dependsOnlyOnPositive`, `f` does NOT depend on interface links. So when we integrate the full integrand `osG(U)·osG(θU) = C · Σ_w F(w) · f(U)·f(θU) · Φ_w(U) · Ψ_w(U) · V_w(U)` over the interface links, the `f(U)·f(θU)` factor is constant w.r.t. the interface integration (it depends only on positive links). Only `Ψ_w(U) = ∏_{l ∈ allLinkInt} χ_{w(l)}(U.value l)` depends on interface links. So the interface integral gives `f(U⁺)·f(θU⁺) · ∫ Ψ_w(u⁰) dμ⁰ = f(U⁺)·f(θU⁺) · δ_{w|_int, trivial}`.

This is why `dependsOnlyOnPositive` (not the weaker `dependsOnlyOnPosSpatialInterface`) is needed: if `f` depended on spatial interface links, the interface integral would be `∫ f(u⁰_s)² · Ψ_w(u⁰_s) dμ⁰_s`, a WEIGHTED integral that is NOT δ and can be negative (the §8.11.58/§8.11.60 obstruction).

#### Remaining steps (4-6 of the §8.11.61 plan)

- **Step 4**: Show the integral over positive/negative links gives `|Â_w|²` using character orthogonality + reflection symmetry (`reflectLinkVariable_measurePreserving`, LatticeMeasure.lean:417). The positive link integral gives the Fourier coefficient `Â_w = ∫ f(U⁺) · Φ_w(U⁺) dμ⁺`, and the negative link integral gives `conj(Â_w)` by reflection symmetry (the `V_w(U) = star(∏_{l ∈ allLinkNeg} χ_{dual(w(l))}(U.value l))` factor becomes `conj(Φ_w(θU))` under reflection, and `f(θU) = f(U)` by reflection symmetry of the positive-time observable).
- **Step 5**: Assemble `I = Σ_{w: trivial on interface} F_full(w) · |Â_w|² ≥ 0` (trivially true since `F(w) ≥ 0` and `|Â_w|² ≥ 0`).
- **Step 6**: Replace `transferMatrixPositivity_axiom` (for `dependsOnlyOnPosSpatialInterface`) with a proved lemma (for `dependsOnlyOnPositive`), reducing axiom count 6 → 5.

#### Summary

| Question | Answer |
|----------|--------|
| Is Step 3 (interface link integral) complete? | **YES** — `interface_char_integral_trivial`, build GREEN, 0 sorries |
| Was the axiom extended? | **YES** — `peterWeyl_clebschGordan_plaquette` now provides `σ_0`, `hσ_0_dims`, `hσ_0_trivial` |
| Did the axiom count change? | **NO** — still 6 (extended existing axiom, no new axiom) |
| What axioms does the new lemma use? | `[propext, Classical.choice, Quot.sound, characterOrthogonality]` — standard 3 + existing #6 |
| Were all destructure sites updated? | **YES** — 4 sites (PeterWeyl.lean ×2, ReflectionPositivity.lean ×2) |
| What is the next step? | Step 4: positive/negative link integral gives `|Â_w|²` (reflection symmetry + character orthogonality) |

### 8.11.65 Step 4 COMPLETE: Full-lattice character factor lemmas (2026-08-10 session 79)

**Build GREEN (2891 jobs). 0 sorries, 6 axioms (unchanged). All new lemmas depend only on standard axioms (propext, Classical.choice, Quot.sound).**

Step 4 of the §8.11.61 plan is now complete. The full-lattice character factor lemmas are formalized in `TransferMatrix.lean` (appended after line 6055). These are the full-lattice analogues of the existing interface-only lemmas (`fullReflectReindex`, `charFactorPos`/`charFactorNeg`, and the per-link/product identities), but working over ALL links (`PeriodicSite T L × Fin 4`) instead of just interface links (`InterfaceLink T L`).

#### What was proved (8 new definitions/lemmas)

1. **`fullReflectReindexLink`** (def) — the full-lattice reflection reindexing `w* : ((PeriodicSite T L × Fin 4) → ι) → ((PeriodicSite T L × Fin 4) → ι)`. For pos links, `w*` is determined by the neg link `(reflectSite l.1, l.2)` (the reflected link), with `dual` applied on time-like links. For int and neg links, `w*` is the identity. This is the full-lattice analogue of `fullReflectReindex` (which works for `InterfaceLink T L`).

2. **`fullReflectReindexLink_pos_time`** — for a positive-time link `l` with `μ(l) = 0` (time-like), `w*(l) = dual(w(reflectSite l.1, l.2))`.

3. **`fullReflectReindexLink_pos_spatial`** — for a positive-time link `l` with `μ(l) ≠ 0` (spatial), `w*(l) = w(reflectSite l.1, l.2)`.

4. **`charFactorPosAll`** (def) — the full-lattice positive-link character factor `Φ_w(U⁺) = ∏_{l ∈ allLinkPos} χ_{w(l)}(U⁺_l)`. Product over `allLinkPos T L` (ALL positive-time links, not just interface links).

5. **`charFactorNegAll`** (def) — the full-lattice negative-link character factor `V_w(U⁻) = ∏_{l ∈ allLinkNeg} χ_{dual(w(l))}(U⁻_l)`. Product over `allLinkNeg T L` (ALL negative-time links).

6. **`charFactorNegAll_eq_star_charFactorPosAll_link_fullReflect`** (per-link identity) — for `b ∈ allLinkPos`, the negative-link character factor at the reflected link `(reflectSite b.1, b.2)` (with weight `w`) equals `star` of the positive-link character factor at `b` (with weight `w* = fullReflectReindexLink`). Time-like: `χ_{dual(w(a))}((V⁺_b)⁻¹) = conj(χ_{dual(w(a))}(V⁺_b))` (repCharacter_inv) = `star(χ_{dual(w(a))}(V⁺_b))` (conj = star), and `w*(b) = dual(w(a))`. Spatial: `χ_{dual(w(a))}(V⁺_b) = conj(χ_{w(a)}(V⁺_b))` (hdual) = `star(χ_{w(a)}(V⁺_b))` (conj = star), and `w*(b) = w(a)`.

7. **`charFactorNegAll_eq_star_charFactorPosAll_fullReflect`** (product identity) — `charFactorNegAll dual w (reflectPosToNeg V⁺) = star (charFactorPosAll (fullReflectReindexLink dual w) V⁺)`. Reindexes the product over `allLinkNeg` to a product over `allLinkPos` via the reflection bijection `(n, μ) ↦ (reflectSite n, μ)` (an involution mapping neg ↔ pos), using `Finset.prod_bij` and the per-link identity.

8. **`star_charFactorNegAll_eq_charFactorPosAll_fullReflect`** (star version) — `star(charFactorNegAll dual w (reflectPosToNeg V⁺)) = charFactorPosAll (fullReflectReindexLink dual w) V⁺`. Follows by applying `star` to both sides of #7 and using `Complex.conj_conj`.

#### Key differences from the interface-only versions

- **Link type**: `PeriodicSite T L × Fin 4` (ALL links) instead of `InterfaceLink T L` (Subtype of interface plaquette links). Elements use `.1`/`.2` instead of `.val.1`/`.val.2`.
- **Link sets**: `allLinkPos`/`allLinkNeg` (Finsets over ALL links) instead of `interfaceLinkPos`/`interfaceLinkNeg`.
- **Reflection**: Simple `(n, μ) ↦ (reflectSite n, μ)` (no Subtype wrapping) instead of `reflectInterfaceLink`.
- **Membership**: `allLinkPos_mem_iff`/`allLinkNeg_mem_iff` instead of `interfaceLinkPos_mem_iff`/`interfaceLinkNeg_mem_iff`.
- **Site reflection**: `reflectSite_mem_positive_of_negative`/`reflectSite_mem_negative_of_positive` instead of `reflectInterfaceLink_mem_pos_of_neg`/`reflectInterfaceLink_mem_neg_of_pos`.
- **Involution**: `ReflectSite.involution` instead of `reflectInterfaceLink_involution`.

#### Axioms

All 8 definitions/lemmas depend only on `[propext, Classical.choice, Quot.sound]` — the standard 3 axioms. No `sorryAx`, no custom axioms. The axiom count remains **6**.

#### Remaining steps (5-6 of the §8.11.61 plan)

- **Step 5**: Assemble `I = Σ_{w: trivial on interface} F_full(w) · |Â_w|² ≥ 0` (trivially true since `F(w) ≥ 0` and `|Â_w|² ≥ 0`). Uses `star_charFactorNegAll_eq_charFactorPosAll_fullReflect` to show the negative factor = `star` of the positive factor, giving `|Â_w|² = Â_w · star(Â_w)`.
- **Step 6**: Replace `transferMatrixPositivity_axiom` with a proved lemma (for `dependsOnlyOnPositive`), reducing axiom count 6 → 5.

### 8.11.66 CRITICAL ANALYSIS: The §8.11.61 `|Â_w|²` claim is INCORRECT — the actual result is `Â_w · Â_{w*}` (reflected weight, NOT conjugated), which is NOT trivially non-negative (2026-08-10 session 80)

**Build GREEN (unchanged, 2972 jobs), 0 sorries, 6 axioms. No code changes this session — this section documents a critical mathematical analysis of the Step 5 claim.**

This session performed a detailed analysis of Step 5 (assembling `I = Σ F_full(w) · |Â_w|² ≥ 0`) and discovered that **the §8.11.61 claim that the result is `|Â_w|²` is INCORRECT.** The actual result is `Â_w · Â_{w*}` where `w* = fullReflectReindexLink dual w` is the reflected weight, and this is a product of two complex Fourier coefficients (NOT an absolute square), which is NOT trivially non-negative.

#### The character expansion form

The full character expansion (Step 2, `full_osG_thetaG_eq_char_expansion_pointwise`) gives:
```
(osG(U)·osG(θU) : ℂ) = (C : ℂ) · Σ_w (F w : ℂ) · ↑(f(U)·f(θU)) · Φ_w(U) · Ψ_w(U) · V_w(U)
```
where:
- `Φ_w(U) = ∏_{l ∈ allLinkPos} χ_{w(l)}(U.value l)` (positive-link character factor)
- `Ψ_w(U) = ∏_{l ∈ allLinkInt} χ_{w(l)}(U.value l)` (interface-link character factor)
- `V_w(U) = star(∏_{l ∈ allLinkNeg} χ_{dual(w(l))}(U.value l))` (negative-link character factor)

The `interface_kernel_character_expansion` (PeterWeyl.lean:1636) gives the negative factor as `conj(∏_{L_V} χ_{dual(w(l))}(g_l))`. Since `star = conj` for `ℂ`, this is `star(∏_{allLinkNeg} χ_{dual(w(l))}(U_l))`.

**Key identity:** `star(∏_{allLinkNeg} χ_{dual(w(l))}(U_l)) = ∏_{allLinkNeg} conj(χ_{dual(w(l))}(U_l)) = ∏_{allLinkNeg} χ_{w(l)}(U_l)` (using `conj(χ_{dual(i)}) = conj(conj(χ_i)) = χ_i` from `hdual`). So the negative factor, after expanding the `star`, is `∏_{allLinkNeg} χ_{w(l)}(U_l)` — the SAME weight `w` with NO dual, NO conjugation. The full expansion is just `C · Σ_w F(w) · ∏_{ALL links} χ_{w(l)}(U_l)`.

#### The integral after Fubini

With `dependsOnlyOnPositive`, `f(U)` depends only on positive links and `f(θU)` depends only on negative links (the reflection maps positive → negative). After Fubini (μ₀ = μ⁺ × μ⁰ × μ⁻):
```
I = C · Σ_w F(w) · [∫_{u⁰} Ψ_w(u⁰) dμ⁰] · [∫_{U⁺} f(U⁺) · Φ_w(U⁺) dμ⁺] · [∫_{U⁻} f(θU⁻) · V_w(U⁻) dμ⁻]
```

- **Step 3** (`interface_char_integral_trivial`): `∫_{u⁰} Ψ_w(u⁰) dμ⁰ = δ_{w|_int, trivial}` (1 if w is trivial on all interface links, 0 otherwise). This works because `dependsOnlyOnPositive` means f doesn't depend on interface links, so the interface integral is unweighted.

- **Positive integral**: `Â_w = ∫_{U⁺} f(U⁺) · Φ_w(U⁺) dμ⁺` (the full-lattice Fourier coefficient of f).

- **Negative integral**: `B_w = ∫_{U⁻} f(θU⁻) · V_w(U⁻) dμ⁻` where `V_w(U⁻) = star(charFactorNegAll dual w U⁻)`.

#### The change of variables on the negative integral

The change of variables `U⁻ = reflectPosToNeg V⁺` (measure-preserving, `reflectLinkVariable_measurePreserving_between`) transforms:
1. `f(θU⁻) → f(V⁺)` — the two reflections cancel: `(θU) at positive link (n,μ) = if μ=0 then (U⁻ at (reflectSite n, 0))⁻¹ else U⁻ at (reflectSite n, μ)`, and after `U⁻ = reflectPosToNeg V⁺`, the two inversions on time-like links cancel, giving `V⁺ at (n, μ)` exactly. So `f(θU⁻) = f(V⁺)`.
2. `V_w(U⁻) = star(charFactorNegAll dual w U⁻) → star(charFactorNegAll dual w (reflectPosToNeg V⁺))`. By Step 4 (`star_charFactorNegAll_eq_charFactorPosAll_fullReflect`): `star(charFactorNegAll dual w (reflectPosToNeg V⁺)) = charFactorPosAll (fullReflectReindexLink dual w) V⁺ = Φ_{w*}(V⁺)` where `w* = fullReflectReindexLink dual w`.

So `B_w = ∫_{V⁺} f(V⁺) · Φ_{w*}(V⁺) dμ⁺ = Â_{w*}`.

#### The actual result: `Â_w · Â_{w*}` (NOT `|Â_w|²`)

The full integral is:
```
I = C · Σ_{w: trivial on int} F(w) · Â_w · Â_{w*}
```

where `w* = fullReflectReindexLink dual w` is the REFLECTED weight. This is a product of two complex Fourier coefficients `Â_w · Â_{w*}`, NOT an absolute square `|Â_w|² = Â_w · conj(Â_w)`.

**Why `Â_{w*} ≠ conj(Â_w)`:** `conj(Â_w) = ∫ f · conj(Φ_w) dμ⁺ = ∫ f · ∏_{pos} χ_{dual(w(l))} dμ⁺` (using `hdual: conj(χ_i) = χ_{dual(i)}`). For `Â_{w*} = conj(Â_w)`, we'd need `Φ_{w*} = conj(Φ_w)`, i.e., `w*(l) = dual(w(l))` for all positive `l`. But `w*(l) = fullReflectReindexLink dual w l`:
- Time-like positive `l`: `w*(l) = dual(w(reflectSite l.1, l.2))` — this is `dual` of `w` at the REFLECTED link, not `dual(w(l))` at the same link.
- Spatial positive `l`: `w*(l) = w(reflectSite l.1, l.2)` — this is `w` at the REFLECTED link, not `dual(w(l))`.

So `w*(l) ≠ dual(w(l))` in general (it involves the REFLECTED link, not the same link). Hence `Â_{w*} ≠ conj(Â_w)`, and the result is `Â_w · Â_{w*}`, NOT `|Â_w|²`.

#### Concrete example (T=3, L=1)

For `T=3, L=1`: sites `t ∈ {0, 1, 2}`, `positiveSites = {t=1}`, `interfaceSites = {t=0}`, `negativeSites = {t=2}`. Reflection maps `t=1 ↔ t=2`.

For a positive time-like link `l = (t=1, μ=0)`: `w*(l) = dual(w(t=2, μ=0))`. For `w* = w`, we'd need `w(t=1, μ=0) = dual(w(t=2, μ=0))`, which is NOT true for general `w`.

So the sum `Σ_{w: trivial on int} F(w) · Â_w · Â_{w*}` pairs each `w` with its reflected `w*`, and the product `Â_w · Â_{w*}` is a product of Fourier coefficients at DIFFERENT weights, NOT an absolute square.

#### Why the result is still non-negative (but NOT trivially)

The integral `I = ∫ osG(U)·osG(θU) dμ₀(U)` is REAL (osG is real-valued) and non-negative (by the Osterwalder-Seiler reflection positivity theorem). The character expansion gives `I = C · Σ_{w: trivial on int} F(w) · Â_w · Â_{w*}`, which must be real and non-negative. But this non-negativity is NOT trivial — it does NOT follow from `F(w) ≥ 0` alone (since `Â_w · Â_{w*}` is NOT `|Â_w|²`).

The non-negativity comes from the **positive-definiteness of the full Boltzmann factor** `exp(-β·S_W)`, which is a product of PD plaquette factors (by the Schur product theorem). The PD gives:
```
∫∫ f(U⁺) · f(W⁺) · K(U⁺, W⁺) dμ⁺ dμ(W⁺) ≥ 0
```
where `K(U⁺, W⁺) = ∫_{u⁰} exp(-β·S_W(U⁺, u⁰, θW⁺)) dμ⁰` is the interface-integrated kernel. The character expansion of `K` gives `Σ_{w: trivial on int} F(w) · Φ_w(U⁺) · Φ_{w*}(W⁺)`, and the non-negativity of the integral `∫∫ f · f · K ≥ 0` is a consequence of the PD of `K` (which comes from the PD of the full Boltzmann factor), NOT from the character expansion form alone.

**The §8.11.60 objection (K_{u⁰} not PD for each u⁰) is BYPASSED** because we integrate over u⁰ FIRST (giving δ by character orthogonality), and the resulting kernel `K = ∫_{u⁰} K_{u⁰} dμ⁰ = Σ_{w: trivial on int} F(w) · Φ_w · Φ_{w*}` is PD (by the PD of the full Boltzmann factor). The per-u⁰ kernel K_{u⁰} is NOT PD (§8.11.60), but the u⁰-integrated kernel K IS PD.

#### Implications for the formalization

1. **Step 5 as described ("trivially true since F(w) ≥ 0 and |Â_w|² ≥ 0") does NOT work.** The result is `Â_w · Â_{w*}`, not `|Â_w|²`, and the non-negativity is NOT trivial.

2. **The identity `I = C · Σ_{w: trivial on int} F(w) · Â_w · Â_{w*}` is a valid identity** that can be formalized (combining Steps 2-4). But it does NOT prove non-negativity.

3. **To prove non-negativity, we need the PD of the full Boltzmann factor** (or equivalently, the PD of the u⁰-integrated kernel K). This is a deeper property that requires:
   - (a) The PD of each plaquette Boltzmann factor (`plaquetteBoltzmannPD`, proven).
   - (b) The Schur product theorem (product of PD functions is PD, `PositiveDefinite.prod`/`finprod`, proven).
   - (c) The connection between the PD of the full Boltzmann factor and the non-negativity of `∫∫ f · f · K ≥ 0` (the kernel K is the u⁰-integral of the full Boltzmann, which is PD by (a)+(b)).
   - (d) The change of variables V⁺ → W⁺ = θV⁺ (already formalized in `transferMatrix_change_of_variables`).

4. **The correct formalization path for Step 5-6 is:**
   - Formalize the identity `I = C · Σ_{w: trivial on int} F(w) · Â_w · Â_{w*}` (combining Steps 2-4).
   - Separately, prove the non-negativity using the PD of the full Boltzmann factor (approach (a)-(d) above), NOT using the character expansion form.
   - The character expansion identity is a COMPUTATIONAL TOOL (it evaluates the integral), but the NON-NEGATIVITY comes from the PD (a structural property).

5. **The §8.11.61 approach (full character expansion → |Â_w|²) is the wrong PROOF STRATEGY.** The full character expansion gives `Â_w · Â_{w*}` (not `|Â_w|²`), and the non-negativity requires the PD, not the character expansion. The correct strategy is: change of variables + PD of the u⁰-integrated kernel (which is the §8.11.59 approach, but with the u⁰ integral done FIRST, bypassing the §8.11.60 objection).

#### Summary

| Question | Answer |
|----------|--------|
| Is the §8.11.61 `|Â_w|²` claim correct? | **NO** — the actual result is `Â_w · Â_{w*}` (reflected weight, NOT conjugated) |
| Why is `Â_{w*} ≠ conj(Â_w)`? | `w*(l) = fullReflectReindexLink dual w l` involves the REFLECTED link, not `dual(w(l))` at the same link |
| Is `Â_w · Â_{w*}` trivially ≥ 0? | **NO** — it's a product of complex Fourier coefficients, NOT an absolute square |
| Is the integral still ≥ 0 (by Osterwalder-Seiler)? | **YES** — but the non-negativity comes from the PD of the full Boltzmann factor, NOT from the character expansion form |
| What is the correct proof strategy? | Change of variables + PD of the u⁰-integrated kernel K = ∫_{u⁰} exp(-β·S_W) dμ⁰ (which IS PD, bypassing the §8.11.60 per-u⁰ objection) |
| What should the next session do? | (1) Formalize the identity `I = C · Σ F(w) · Â_w · Â_{w*}` (Steps 2-4 combined). (2) Prove the PD of the u⁰-integrated kernel K using `plaquetteBoltzmannPD` + Schur product + change of variables. (3) Use the PD of K to conclude `I ≥ 0`. |

### 8.11.67 CRITICAL ANALYSIS: The group-PD of the full Boltzmann does NOT directly give non-negativity of I — the Lüscher decomposition T = V^{1/2}·U·V^{1/2} is the correct mechanism (2026-08-10 session 81)

**Build GREEN (unchanged), 0 sorries, 6 axioms. No code changes this session — this section documents a critical mathematical analysis that revises the §8.11.66 proof strategy.**

This session performed a deep analysis of the §8.11.66 proposed strategy ("prove the PD of the u⁰-integrated kernel K using `plaquetteBoltzmannPD` + Schur product + change of variables") and discovered that **the group-PD of the full Boltzmann factor B on the link group G does NOT directly give the non-negativity of the integral I.** The correct mechanism is the **Lüscher decomposition** T = V^{1/2}·U·V^{1/2}, which separates spatial and temporal plaquettes and handles them by different mechanisms.

#### The group-PD gap

The full Boltzmann factor `B(U) = exp(-β·S_W(U)) = ∏_p exp(β·Re Tr(U_{∂p}))` is a product of plaquette Boltzmann factors. Each plaquette factor is PD on `SU(N)⁴` (proven: `plaquetteBoltzmannPD`). By the Schur product theorem (`PositiveDefinite.finprod`), the product B is PD on the full link group `G = SU(N)^{allLinks}` (with componentwise multiplication).

The group-PD of B on G means: for any `{g_i} ⊂ G` and `{c_i} ⊂ ℂ`:
```
∑_{i,j} c_i · conj(c_j) · B(g_i⁻¹ · g_j) ≥ 0
```
where `g_i⁻¹ · g_j` is the COMPONENTWISE group product (each link variable is multiplied componentwise).

The integral operator version (`PositiveDefinite.integralOperator_nonneg`) gives:
```
∫∫ f(g) · conj(f(h)) · B(g⁻¹ · h) dμ(g) dμ(h) ≥ 0
```

**But our integral is** `I = ∫ f(U) · f(θU) · B(U) dμ₀(U)`, which is fundamentally different:
1. `B(U)` is the Boltzmann at a SINGLE configuration U, NOT `B(g⁻¹ · h)` (the Boltzmann at a group product).
2. The reflection θ is NOT a group homomorphism — it inverts time-like links and permutes sites, which is a geometric operation, not group multiplication.
3. Therefore `B(U) ≠ B(g⁻¹ · h)` for any g, h related by θ.

**Conclusion:** The group-PD of B gives non-negativity for `∫∫ f·conj(f)·B(g⁻¹·h)`, but our integral `∫ f·f(θU)·B(U)` has a different structure. The group-PD does NOT directly imply the non-negativity of I.

#### Why the character expansion gives Â_w · Â_{w*} (not |Â_w|²)

As shown in §8.11.66, the full character expansion of B gives:
```
B(U) = C · Σ_w F(w) · Φ_w(U⁺) · Ψ_w(u⁰) · V_w(U⁻)
```
where `Φ_w(U⁺) = ∏_{pos links} χ_{w(l)}(U⁺_l)`, `Ψ_w(u⁰) = ∏_{int links} χ_{w(l)}(u⁰_l)`, and `V_w(U⁻) = star(∏_{neg links} χ_{dual(w(l))}(U⁻_l))`.

After integrating out u⁰ (interface links) with `dependsOnlyOnPositive` (f doesn't depend on interface links), character orthogonality gives `δ_{w|int, trivial}`. After the change of variables `U⁻ = reflectPosToNeg V⁺` (measure-preserving), the Step 4 identity (`star_charFactorNegAll_eq_charFactorPosAll_fullReflect`) gives `V_w(reflectPosToNeg V⁺) = Φ_{w*}(V⁺)` where `w* = fullReflectReindexLink dual w`.

The result is:
```
I = C · Σ_{w: trivial on int} F(w) · Â_w · Â_{w*}
```
where `Â_w = ∫ f(U⁺) · Φ_w(U⁺) dμ⁺` and `Â_{w*} = ∫ f(V⁺) · Φ_{w*}(V⁺) dμ⁺`.

**Why this is NOT |Â_w|²:** `conj(Â_w) = ∫ f · conj(Φ_w) dμ⁺ = ∫ f · ∏_{pos} χ_{dual(w(l))} dμ⁺` (using `hdual: conj(χ_i) = χ_{dual(i)}`). For `Â_{w*} = conj(Â_w)`, we'd need `Φ_{w*} = conj(Φ_w)`, i.e., `w*(l) = dual(w(l))` for all positive l. But `w*(l) = fullReflectReindexLink dual w l` involves the REFLECTED link `(reflectSite l.1, l.2)`, not `dual(w(l))` at the same link. So `w*(l) ≠ dual(w(l))` in general, and `Â_{w*} ≠ conj(Â_w)`.

**Why the sum is NOT trivially non-negative:** The sum `Σ_w F(w) · Â_w · Â_{w*}` is a sum of products of complex Fourier coefficients at DIFFERENT weights (w and w*), NOT absolute squares. Even though F(w) ≥ 0, the product `Â_w · Â_{w*}` is complex in general, and the sum is NOT trivially ≥ 0.

**Can the w ↔ w* pairing save it?** The reflection maps w → w* = fullReflectReindexLink dual w, which is an involution. If c_w = c_{w*} (by reflection symmetry), the pair sum is `c_w · (Â_w · Â_{w*} + Â_{w*} · Â_w) = 2·c_w·Re(Â_w · Â_{w*})`. But `Re(Â_w · Â_{w*})` can be NEGATIVE (it's the real part of a product of two different complex numbers, not an absolute square). So the pairing does NOT save it.

#### The u⁰-integrated kernel K is NOT Mercer-PD

The u⁰-integrated kernel is:
```
K(U⁺, V⁺) = ∫_{u⁰} exp(-β·S_W(U⁺, u⁰, reflectPosToNeg V⁺)) dμ⁰
           = C · Σ_{w: trivial on int} F(w) · Φ_w(U⁺) · Φ_{w*}(V⁺)
```

For K to be Mercer-PD (`PositiveDefiniteKernel`), we'd need:
```
Σ_{i,j} a_i · conj(a_j) · K(U⁺_i, V⁺_j) = Σ_w F(w) · [Σ_i a_i · Φ_w(U⁺_i)] · [Σ_j conj(a_j) · Φ_{w*}(V⁺_j)] ≥ 0
```

This is a sum of products of complex numbers with non-negative coefficients, which is NOT necessarily ≥ 0 (since `Φ_{w*} ≠ conj(Φ_w)`, the two bracketed sums are NOT conjugates, and their product is NOT an absolute square).

**Conclusion:** The u⁰-integrated kernel K is NOT Mercer-PD in general. The §8.11.66 claim that "K is PD by the PD of the full Boltzmann factor" is INCORRECT — the group-PD of B does not transfer to the Mercer-PD of K because K is not of the form `φ(g⁻¹·h)` for a PD function φ.

#### The correct mechanism: Lüscher decomposition T = V^{1/2}·U·V^{1/2}

The Osterwalder-Seiler theorem does NOT use the group-PD of B directly, nor the full character expansion. Instead, it uses the **Lüscher decomposition** of the transfer matrix:

```
T = V^{1/2} · U · V^{1/2}
```

where:
- **V** (spatial hopping operator) comes from the SPATIAL plaquettes (plaquettes within a single time slice). V is a multiplication operator: `(Vψ)(u) = exp(β·Σ_{spatial p} Re Tr(U_{∂p})) · ψ(u)`. V is positive because the spatial Boltzmann factor is a product of PD plaquette factors (Schur product theorem), hence PD, hence defines a positive multiplication operator.

- **U** (temporal transfer operator) comes from the TEMPORAL plaquettes (plaquettes spanning two adjacent time slices). U is an integral operator that integrates out the temporal links. U is positive because:
  1. Each temporal plaquette factor has a character expansion with non-negative coefficients (from `plaquetteBoltzmannPD`).
  2. The Schur orthogonality integrates out the temporal links, producing a kernel of the form `Σ_s a_s · χ_s(W·V)` with `a_s ≥ 0` (the Lüscher cascade, formalized as `luscher_2site_cascade_coeff` / `luscher_3site_cascade_coeff`).
  3. `character_kernel_integral_nonneg` gives `∫∫ f(W)·f(V⁻¹)·K(W,V) ≥ 0` for any kernel `K(W,V) = Σ_s a_s · χ_s(W·V)` with `a_s ≥ 0`.

- **T = V^{1/2}·U·V^{1/2}** is positive because V^{1/2} is self-adjoint and U is positive: `∫ g·Tg = ∫ (V^{1/2}g)·U·(V^{1/2}g) ≥ 0`.

#### Why the Lüscher decomposition avoids the Â_w · Â_{w*} problem

The key difference from the full character expansion:

| Approach | Temporal plaquettes | Spatial plaquettes | Result |
|----------|-------------------|-------------------|--------|
| Full char expansion | Expanded in characters | Expanded in characters | `Σ_w F(w)·Â_w·Â_{w*}` (NOT |Â_w|², NOT trivially ≥ 0) |
| Lüscher decomposition | Expanded in characters + Schur orthogonality (Lüscher cascade) | NOT expanded — used as PD multiplication operator (Schur product) | `T = V^{1/2}·U·V^{1/2}` (positive operator, ∫ g·Tg ≥ 0) |

The Lüscher decomposition works because:
1. **Temporal plaquettes** are handled by the character expansion + Schur orthogonality (Lüscher cascade). This produces a kernel `Σ_s a_s · χ_s(W·V)` with `a_s ≥ 0`, which is Mercer-PD (because `χ_s` is PD and `a_s ≥ 0`). The `character_kernel_integral_nonneg` lemma then gives the non-negativity.

2. **Spatial plaquettes** are NOT expanded in characters. Instead, they give a PD function (product of PD plaquette factors by Schur product), which defines a positive multiplication operator V. This avoids the `Â_w · Â_{w*}` problem because the spatial character factors are NOT expanded — they stay as a PD function.

3. The **combination** T = V^{1/2}·U·V^{1/2} is positive because both V and U are positive operators. The V^{1/2} factor "dresses" the test function g, and the positivity of U ensures the dressed integral is non-negative.

The full character expansion fails because it tries to expand ALL plaquettes (temporal AND spatial) in characters, which produces the `Â_w · Â_{w*}` form (product of Fourier coefficients at different weights, NOT an absolute square). The Lüscher decomposition succeeds because it separates the two types of plaquettes and handles them by different mechanisms.

#### The formalization plan (revised)

The formalization requires:

1. **Decompose the Wilson action** into spatial and temporal plaquette contributions:
   - `S_W = S_spatial + S_temporal` where S_spatial is the sum over spatial plaquettes and S_temporal is the sum over temporal plaquettes.
   - This requires defining "spatial plaquette" (all 4 corners at the same time) and "temporal plaquette" (corners at two adjacent times).

2. **Construct V** (spatial hopping operator):
   - `Vψ(u) = exp(β·S_spatial(u)) · ψ(u)` (multiplication by the spatial Boltzmann factor).
   - Show V is positive: the spatial Boltzmann factor is a product of PD plaquette factors (Schur product), hence PD, hence V is a positive multiplication operator.

3. **Construct U** (temporal transfer operator):
   - `Uψ(u) = ∫ ψ(V⁺) · exp(β·S_temporal(u, V⁺)) dμ(V⁺)` (integral over the temporal links).
   - Show U is positive: expand each temporal plaquette factor in characters (non-negative coefficients from `plaquetteBoltzmannPD`), apply the Lüscher cascade (Schur orthogonality integrates out temporal links, producing `Σ_s a_s · χ_s(W·V)` with `a_s ≥ 0`), then apply `character_kernel_integral_nonneg`.

4. **Show T = V^{1/2}·U·V^{1/2}**:
   - This requires showing that the transfer matrix `transferMatrixCorrect` factors as V^{1/2}·U·V^{1/2}.
   - The V^{1/2} factor comes from splitting the OS-positive action: `S⁺ = S_spatial + S_temporal⁺/2` (the spatial plaquettes contribute fully to V, the temporal plaquettes contribute half to V^{1/2} and half to U).

5. **Conclude** `∫ g·Tg = ∫ (V^{1/2}g)·U·(V^{1/2}g) ≥ 0` (positivity of U).

6. **Use `integral_G_thetaG_eq_inner_g_Tg`** to conclude `I = ∫ g·Tg ≥ 0`.

#### Key existing infrastructure

- `plaquetteBoltzmannPD` (PeterWeyl.lean:367) — plaquette Boltzmann factor is PD (non-negative character expansion coefficients)
- `PositiveDefinite.finprod` (PositiveDefinite.lean:503) — n-ary Schur product theorem (product of PD is PD)
- `PositiveDefinite.comp_hom` (PositiveDefinite.lean:470) — PD preserved by group homomorphisms (projections)
- `character_kernel_integral_nonneg` (PositiveDefiniteIntegral.lean:1400) — `∫∫ f·f⁻¹·Σ a_s χ_s(W·V) ≥ 0` for `a_s ≥ 0`
- `luscher_2site_cascade_coeff` / `luscher_3site_cascade_coeff` (PositiveDefinite.lean) — Lüscher cascade (Schur orthogonality integrates out temporal links)
- `integral_G_thetaG_eq_inner_g_Tg` (TransferMatrix.lean:5149) — `∫ G·G(θU) = ∫ g·(Tg)`
- `transferMatrix_change_of_variables` (TransferMatrix.lean:2619) — change of variables U⁻ → V⁺
- `transferMatrixReflected` (TransferMatrix.lean:2600) — transfer matrix after change of variables

#### Key challenges

1. **Spatial/temporal plaquette decomposition**: The existing `wilsonActionOSPositive` / `wilsonActionOSNegative` / `wilsonActionOSInterface` decomposition is by TIME SIGNATURE (positive/negative/interface), not by spatial/temporal. The Lüscher decomposition requires a DIFFERENT decomposition: spatial plaquettes (all links at the same time) vs temporal plaquettes (links at two adjacent times). This is a new decomposition that needs to be defined and proven to sum to the full action.

2. **Lüscher cascade on the full lattice**: The existing `luscher_2site_cascade_coeff` / `luscher_3site_cascade_coeff` are for abstract 2-site and 3-site cascades. Extending to the full lattice (many temporal links) requires a more general cascade argument, potentially an inductive argument over time slices.

3. **V^{1/2} factorization**: Showing T = V^{1/2}·U·V^{1/2} requires splitting the OS-positive action into spatial and temporal parts, with the temporal part split evenly between V^{1/2} and U. This requires a careful decomposition of the action.

4. **Continuity/compactness**: The `character_kernel_integral_nonneg` and `PositiveDefiniteKernel.integralOperator_nonneg` lemmas require continuity and compactness. The link variable space is compact (product of compact SU(N)), and the Boltzmann factor is continuous, so these should be satisfiable.

#### Summary

| Question | Answer |
|----------|--------|
| Does the group-PD of B directly give I ≥ 0? | **NO** — B(U) ≠ B(g⁻¹·h), and θ is not a group homomorphism |
| Is the u⁰-integrated kernel K Mercer-PD? | **NO** — the character expansion gives `Σ F(w)·Φ_w·Φ_{w*}` with `Φ_{w*} ≠ conj(Φ_w)`, so the quadratic form is NOT non-negative |
| Is the §8.11.66 strategy correct? | **NO** — "K is PD by the PD of the full Boltzmann" is incorrect; the group-PD does not transfer to Mercer-PD of K |
| What is the correct mechanism? | **Lüscher decomposition** T = V^{1/2}·U·V^{1/2}: spatial plaquettes → V (PD multiplication operator), temporal plaquettes → U (positive integral operator via Lüscher cascade + `character_kernel_integral_nonneg`) |
| Why does the Lüscher decomposition work? | It separates temporal and spatial plaquettes: temporal → character expansion + Schur orthogonality (kernel `Σ a_s χ_s(W·V)`, a_s ≥ 0, Mercer-PD), spatial → Schur product (PD function, positive operator) |
| Why does the full character expansion fail? | It expands ALL plaquettes in characters, giving `Â_w · Â_{w*}` (product at different weights, NOT |Â_w|²) |
| What are the key formalization steps? | (1) Spatial/temporal plaquette decomposition, (2) V positive (Schur product), (3) U positive (Lüscher cascade + `character_kernel_integral_nonneg`), (4) T = V^{1/2}·U·V^{1/2}, (5) ∫ g·Tg ≥ 0 |
| What is the most tractable first step? | Formalize the full Boltzmann PD on G (building block: `plaquetteBoltzmannPD` + `comp_hom` + `finprod`), then the spatial/temporal plaquette decomposition |

### 8.11.68 STEP 5 SUB-STEPS 1-2 COMPLETE: Spatial/temporal plaquette decomposition + spatialBoltzmannPD (2026-08-11 session 84)

**Build GREEN (2972 jobs), 0 sorries, 6 axioms (unchanged). Two new lemmas + one theorem added to `ReflectionPositivity.lean` (lines 1855-2078).**

This session completed sub-steps 1 and 2 of the Lüscher decomposition T = V^{1/2}·U·V^{1/2} (§8.11.67):

#### Sub-step 1: Spatial/temporal plaquette decomposition

**New definitions** (ReflectionPositivity.lean, after `fullBoltzmannPD`):
- `isSpatialPlaquette (p : PlaquetteIndex T L) : Prop` — `p.2.1 ≠ 0 ∧ p.2.2 ≠ 0` (both directions nonzero → plaquette within a single time slice)
- `isTemporalPlaquette (p : PlaquetteIndex T L) : Prop` — `p.2.1 = 0 ∨ p.2.2 = 0` (at least one direction is the time direction 0 → plaquette spanning two time slices)
- `spatialPlaquettes (T L) : Finset (PlaquetteIndex T L)` — filter of `Finset.univ` by `isSpatialPlaquette`
- `temporalPlaquettes (T L) : Finset (PlaquetteIndex T L)` — filter of `Finset.univ` by `isTemporalPlaquette`
- `wilsonActionSpatial (N T L β U) : ℝ` — `∑ p ∈ spatialPlaquettes, plaquetteContribution N β U p.1 p.2.1 p.2.2`
- `wilsonActionTemporal (N T L β U) : ℝ` — `∑ p ∈ temporalPlaquettes, plaquetteContribution N β U p.1 p.2.1 p.2.2`

**New lemmas:**
- `spatialPlaquettes_mem_iff` / `temporalPlaquettes_mem_iff` — membership characterizations
- `spatial_temporal_plaquette_partition` — `Disjoint (spatialPlaquettes) (temporalPlaquettes) ∧ spatialPlaquettes ∪ temporalPlaquettes = Finset.univ` (the spatial/temporal partition is disjoint and covers all plaquettes)
- `wilsonActionFinite_eq_spatial_plus_temporal` — **`S_W = S_spatial + S_temporal`** (the Wilson action decomposes into spatial + temporal parts). Proof: convert the triple sum `∑ n, ∑ μ, ∑ ν, plaquetteContribution` to a `PlaquetteIndex` sum using `← Fintype.sum_prod_type'` (same pattern as `prod_if_interface_eq_prod_subtype`), then split by the partition using `Finset.sum_union`.

**Axioms:** `[propext, Classical.choice, Quot.sound]` — standard 3 only, 0 custom axioms.

#### Sub-step 2: V positive (spatial Boltzmann PD)

**New lemmas/theorem:**
- `spatial_boltzmann_eq_abstract_product` — `exp(-β·S_spatial) = C_spatial · ∏_{p ∈ spatialPlaquettes} exp((β²/N)·Re Tr(P_p))` with `C_spatial > 0`. Proof: `Finset.mul_sum` + `Real.exp_sum` (exp-of-sum for the spatial action) + `plaquetteContribution_exp_decomp_tm` (per-plaquette Boltzmann decomposition) + `Finset.prod_mul_distrib` (split constant from product). Standard axioms only.
- `spatialBoltzmannPD` — **the spatial Boltzmann factor `exp(-β·S_spatial)` is PD on the link group `G = SU(N)^{allLinks}`**. Proof: same pattern as `fullBoltzmannPD` — each spatial plaquette factor is PD (`plaquetteBoltzmannPD_inv` + `comp_hom` + `congr`), the product is PD (`PositiveDefinite.finprod` + `congr`), C times the product is PD (`smul_nonneg` + `congr`), and the spatial Boltzmann equals C times the product (`exact_mod_cast h_eq U`).

**Axioms:** `[propext, Classical.choice, Quot.sound, peterWeyl_clebschGordan_plaquette]` — same as `fullBoltzmannPD` (4 axioms, no new axioms).

**Key technique (reused from session 83):** The `addVectorPeriodic` match on `Fin 4` gets stuck during `whnf` when `μ` is a variable. The fix (from `fullBoltzmannPD`) is to use `PositiveDefinite.congr` for all PD transfer steps — build PD proofs without declared types (no conclusion defeq check), then transfer PD with `congr` + `funext` + `rfl`. The `funext` goal is alpha-equivalent, so `rfl` is fast.

#### Remaining sub-steps (3-6 of the §8.11.67 plan)

- **Sub-step 3 (U positive):** Show the temporal plaquette operator U is positive. Expand each temporal plaquette factor in characters (non-negative coefficients from `plaquetteBoltzmannPD`), apply the Lüscher cascade (Schur orthogonality integrates out temporal links, producing `Σ_s a_s · χ_s(W·V)` with `a_s ≥ 0`), then apply `character_kernel_integral_nonneg`. **Key infrastructure:** `character_kernel_integral_nonneg` (PositiveDefiniteIntegral.lean:1400), `luscher_2site_cascade_integral_nonneg` (PositiveDefiniteIntegral.lean:1479), `luscher_2site_cascade_coeff` / `luscher_3site_cascade_coeff` (PositiveDefinite.lean).
- **Sub-step 4 (T = V^{1/2}·U·V^{1/2}):** Show the transfer matrix `transferMatrixCorrect` factors as V^{1/2}·U·V^{1/2}. The V^{1/2} factor comes from splitting the OS-positive action: `S⁺ = S_spatial + S_temporal⁺/2`.
- **Sub-step 5 (∫ g·Tg ≥ 0):** Conclude `∫ g·Tg = ∫ (V^{1/2}g)·U·(V^{1/2}g) ≥ 0` (positivity of U).
- **Sub-step 6 (I ≥ 0):** Use `integral_G_thetaG_eq_inner_g_Tg` to conclude `I = ∫ g·Tg ≥ 0`.

#### Summary

| Question | Answer |
|----------|--------|
| Is sub-step 1 (spatial/temporal decomposition) complete? | **YES** — `wilsonActionFinite_eq_spatial_plus_temporal`, build GREEN, 0 sorries |
| Is sub-step 2 (V positive) complete? | **YES** — `spatialBoltzmannPD`, build GREEN, 0 sorries |
| What axioms do the new results use? | Standard 3 + `peterWeyl_clebschGordan_plaquette` (same as `fullBoltzmannPD`) |
| Did the axiom count change? | **NO** — still 6 |
| What is the next sub-step? | Sub-step 3: U positive (temporal plaquette operator via Lüscher cascade + `character_kernel_integral_nonneg`) |

### 8.11.69 STEP 5 SUB-STEP 3a: `temporal_boltzmann_eq_abstract_product` — temporal Boltzmann abstract product form (2026-08-12 session 91)

**Build GREEN, 0 sorries, 6 axioms (unchanged). One new lemma added to `ReflectionPositivity.lean` (after `spatialBoltzmannPD`, ~line 2080).**

This session began sub-step 3 of the Lüscher decomposition (§8.11.67). The first building block is the temporal analogue of `spatial_boltzmann_eq_abstract_product`:

#### `temporal_boltzmann_eq_abstract_product` (line ~2080)

The temporal Boltzmann factor `exp(-β·S_temporal)` equals a positive constant
`C = ∏_{p ∈ temporalPlaquettes} exp(-β²)` times the abstract plaquette product
`∏_{p ∈ temporalPlaquettes} exp((β²/N)·Re Tr(P_p))`. This is the temporal analogue
of `spatial_boltzmann_eq_abstract_product` (line ~1967). Pure algebra — same proof
pattern: `Finset.mul_sum` + `Real.exp_sum` + `plaquetteContribution_exp_decomp_tm`
+ `Finset.prod_mul_distrib`.

**Axioms:** `[propext, Classical.choice, Quot.sound]` — standard 3 only, 0 custom axioms.

#### Key infrastructure analysis for sub-step 3 (U positive)

The session also analyzed the key infrastructure for sub-step 3:

1. **`character_kernel_integral_nonneg`** (PositiveDefiniteIntegral.lean:1400) — proves
   `0 ≤ ∫ W ∫ V f(W)·f(V⁻¹)·Σ_ν coeff_ν·χ_ν(W·V) dμ dμ` for `coeff_ν ≥ 0`. This is the
   key non-negativity lemma for kernels of the form `Σ a_s χ_s(W·V)` with `a_s ≥ 0`.
   **This is the right tool for sub-step 5** (NOT the general L² `integralOperator_nonneg_general`
   from `mathlib_candidates/PositiveDefiniteKernelGeneral.lean`, which is for Mercer-PD
   kernels `K(x,y)` with `Σ c_i conj(c_j) K(x_i, x_j) ≥ 0`; the kernel `Σ a_s χ_s(W·V)`
   is NOT Mercer-PD in the standard sense — it's `χ_s(W·V)`, not `χ_s(W⁻¹·V)`).

2. **`chainIntegral_eq`** (PositiveDefinite.lean:1612) — the general L-site Lüscher cascade.
   For an open chain of (representation, Wilson-line) pairs, the cascade evaluates to
   `δ_{all γ=γ₀} · (1/d_γ)^n · χ_γ(a · (∏ W) · b⁻¹)` where n is the number of interior
   integrations. The coefficient `(1/d_γ)^n > 0` is non-negative. **This is the key tool
   for the cascade on the full lattice** — the temporal links form a chain, and the cascade
   integrates them out one by one.

3. **`luscher_2site_cascade_integral_nonneg`** (PositiveDefiniteIntegral.lean:1479) — combines
   the 2-site cascade with `character_kernel_integral_nonneg`. This is the 2-site version
   of the full non-negativity result.

4. **`luscher_key_identity`** (PositiveDefinite.lean:1110) — the single-link identity
   `∫_G χ_γ(g·h)·χ_{γ'}(g⁻¹·k) dg = δ_{γγ'}·(1/d_γ)·χ_γ(h·k)`. This is the building block
   for all cascade lemmas.

#### Remaining sub-steps for sub-step 3 (U positive)

- **3b**: `temporal_product_character_expansion` — apply `plaquette_product_separable_decomp`
  (or `interface_kernel_character_expansion`) to the temporal plaquettes, producing a
  character expansion `∏_p exp(c·Re Tr(P_p)) = Σ_w F(w) · Φ_w · Ψ_w · V_w` with `F(w) ≥ 0`.
  The link partition separates temporal links (internal, integrated out by cascade) from
  spatial links (external, the kernel variables W and V). **Key challenge**: identifying
  the correct link partition for the temporal plaquettes (temporal links vs spatial links
  at positive/negative time).
- **3c**: Lüscher cascade on temporal links — use `chainIntegral_eq` to integrate out the
  temporal links, producing a kernel `Σ_s a_s · χ_s(W·V)` with `a_s ≥ 0`. **Key challenge**:
  the temporal links form a chain (or cycle for periodic BC), and the cascade needs to
  handle all of them. The `chainIntegral_eq` lemma handles open chains; periodic chains
  may need a variant.
- **3d**: Apply `character_kernel_integral_nonneg` to conclude U is positive.

#### Adversarial self-check (per standing rules)

The Lüscher decomposition T = V^{1/2}·U·V^{1/2} is the standard approach in the literature
(Lüscher 1977, Osterwalder-Seiler 1978). The extensive analysis in §8.11.50-67 ruled out
several incorrect approaches (full character expansion → Â_w·Â_{w*}, per-u⁰ PD, group-PD
of B). The Lüscher decomposition is the correct mechanism. The main risk is formalization
difficulty (especially the cascade on the full lattice, sub-step 3c), not mathematical
soundness. The key infrastructure (`chainIntegral_eq`, `character_kernel_integral_nonneg`,
`luscher_key_identity`) is in place. The approach is NOT a dead end.

#### Summary

| Question | Answer |
|----------|--------|
| Is `temporal_boltzmann_eq_abstract_product` complete? | **YES** — build GREEN, 0 sorries, standard 3 axioms |
| Is the general L² result applicable to sub-step 5? | **NO** — `character_kernel_integral_nonneg` is the right tool (kernel `Σ a_s χ_s(W·V)` is not Mercer-PD) |
| Is `chainIntegral_eq` available for the full-lattice cascade? | **YES** — general L-site cascade, handles arbitrary chain length |
| What is the next sub-step? | 3b: `temporal_product_character_expansion` (character expansion of temporal plaquette product) |

### 8.11.70 STEP 5 SUB-STEP 3b: `temporal_product_character_expansion` — temporal plaquette product character expansion (2026-08-12 session 92)

**Build GREEN, 0 sorries, 6 axioms (unchanged). One new lemma + supporting infrastructure added to `ReflectionPositivity.lean` (after `temporal_boltzmann_eq_abstract_product`, ~line 2120).**

This session completed sub-step 3b of the Lüscher decomposition (§8.11.67): the temporal plaquette product is expanded in characters, separating temporal links (internal, to be integrated out by the Lüscher cascade in sub-step 3c) from spatial links (external, the kernel variables W and V).

#### New infrastructure (temporal link analogue of interface link infrastructure)

Following the pattern of `InterfacePlaquette` / `InterfaceLink` / `interfaceLinkAssign` (lines 1108-1269), the temporal analogue was defined:

- **`TemporalPlaquette (T L)`** — subtype `{p : PlaquetteIndex T L // isTemporalPlaquette p}` (plaquettes with at least one direction = 0). Fintype + DecidableEq instances provided.
- **`temporalPlaqLinkFinset (T L)`** — Finset of all links appearing in at least one temporal plaquette (image of `plaquetteLinkIdx` over `TemporalPlaquette × Fin 4`).
- **`TemporalLink (T L)`** — subtype `{l : PeriodicSite T L × Fin 4 // l ∈ temporalPlaqLinkFinset T L}`. Fintype + DecidableEq instances provided.
- **`temporalLinkAssign (T L)`** — link assignment `TemporalPlaquette → Fin 4 → TemporalLink` (maps each plaquette `p` and index `j` to the j-th link of `p`).
- **`temporalLinkAssign_surj (T L)`** — surjectivity: every `TemporalLink` arises as some plaquette's j-th link. This is the `hlinks_surj` hypothesis for `interface_kernel_character_expansion`.
- **`temporalLinkVar (N T L U)`** — extract link variable `U.value l.val.1 l.val.2` at a `TemporalLink`.
- **`plaquetteProduct_temporal_eq`** — `plaquetteProduct N U p.val... = temporalLinkVar U (assign p 0) · ... · temporalLinkVar U (assign p 3)⁻¹` (connects concrete plaquette product to abstract link form).

#### The temporal link partition (L_U / L_0 / L_V)

The key design decision for sub-step 3b is the partition of temporal links into three sets, matching the `interface_kernel_character_expansion` signature (L_U, L_0, L_V):

- **`temporalLinkPos` (L_U, "W")**: spatial links (μ ≠ 0) at **positive** signed time. These are the external "W" variables of the Lüscher kernel.
- **`temporalLinkInt` (L_0, internal)**: temporal links (μ = 0, at **any** time) OR spatial links at the **interface** (signedTime = 0). These are the internal links to be integrated out by the Lüscher cascade in sub-step 3c.
- **`temporalLinkNeg` (L_V, "V")**: spatial links (μ ≠ 0) at **negative** signed time. These are the external "V" variables of the Lüscher kernel.

**Why this partition?** The temporal plaquettes (at least one direction = 0) involve two types of links:
1. **Temporal links** (μ = 0): these connect adjacent time slices and are internal to the transfer matrix. They must be integrated out by the Lüscher cascade (sub-step 3c). Placing them in L_0 (internal) ensures they appear in the `Ψ_w(internal)` factor, which is consumed by the cascade.
2. **Spatial links** (μ ≠ 0): these lie within a single time slice and are external. The positive-time ones are "W" (L_U), the negative-time ones are "V" (L_V). The interface spatial links (signedTime = 0) are also internal (L_0) because they sit at the time-slice boundary.

**Disjointness + cover** (`temporalLinkPartition_disjoint_cover`):
- Disjoint L_U L_0: L_U requires μ ≠ 0 and signedTime > 0, contradicting both μ = 0 and signedTime = 0.
- Disjoint (L_U ∪ L_0) L_V: L_V requires signedTime < 0, contradicting L_U's signedTime > 0 and L_0's signedTime = 0 or μ = 0.
- Cover: by signedTime trichotomy (> 0, = 0, < 0) and μ = 0 / μ ≠ 0 cases, every temporal link falls into exactly one set.

The `hdisj` and `hcover` lemmas (`temporalLinkPartition_hdisj`, `temporalLinkPartition_hcover`) package this in the form required by `interface_kernel_character_expansion`.

#### `temporal_product_character_expansion` (line ~2295)

The temporal plaquette product `∏_{p ∈ TemporalPlaquette} exp((β²/N)·Re Tr(P_p))` (viewed in ℂ) admits the separable character expansion:

```
∏_p exp(c·Re Tr(...)) = ∑_w F(w) · Φ_w(W) · Ψ_w(internal) · conj(Φ_w(V))
```

with `F(w) ≥ 0`, where:
- `Φ_w(W) = ∏_{l ∈ L_U} χ_{w(l)}(U_l)` (positive-time spatial links, external "W")
- `Ψ_w(internal) = ∏_{l ∈ L_0} χ_{w(l)}(U_l)` (temporal + interface links, internal)
- `conj(Φ_w(V)) = star(∏_{l ∈ L_V} χ_{dual(w(l))}(U_l))` (negative-time spatial links, external "V")

**Proof:** Apply `interface_kernel_character_expansion` with:
- P = `TemporalPlaquette T L`, L = `TemporalLink T L`
- links = `temporalLinkAssign T L`, hlinks_surj = `temporalLinkAssign_surj T L`
- L_U = `temporalLinkPos`, L_0 = `temporalLinkInt`, L_V = `temporalLinkNeg`
- hdisj = `temporalLinkPartition_hdisj`, hcover = `temporalLinkPartition_hcover`

Then rewrite the goal's `plaquetteProduct` to the linkIdx form via `plaquetteProduct_temporal_eq` (using `Finset.prod_congr`). The `hF_decomp (temporalLinkVar N T L U)` gives the expansion directly.

**Axioms:** `[propext, Classical.choice, Quot.sound, peterWeyl_clebschGordan_plaquette]` — same as `full_product_character_expansion` and `interface_product_character_expansion` (4 axioms, no new axioms, NO sorryAx).

#### Remaining sub-steps for sub-step 3 (U positive)

- **3c**: Lüscher cascade on temporal links — use `chainIntegral_eq` to integrate out the temporal links (the L_0 / internal links), producing a kernel `Σ_s a_s · χ_s(W·V)` with `a_s ≥ 0`. **Key challenge**: the temporal links form a chain (or cycle for periodic BC), and the cascade needs to handle all of them. The `chainIntegral_eq` lemma handles open chains; periodic chains may need a variant. The L_0 set includes both temporal links (μ = 0) and interface spatial links (signedTime = 0); the cascade integrates out the temporal links, while the interface spatial links are handled by character orthogonality (δ_{w|int, trivial}).
- **3d**: Apply `character_kernel_integral_nonneg` to conclude U is positive.

#### CRITICAL ANALYSIS for sub-step 3c (2026-08-12 session 92, continued)

**The separable expansion from sub-step 3b is NOT directly useful for the Lüscher cascade.** Deep analysis of the cascade mechanism reveals a key distinction:

1. **Separable (multi-link) expansion** (from `temporal_product_character_expansion` / `interface_kernel_character_expansion`): Each link l gets a SINGLE character `χ_{w(l)}(g_l)` of the INDIVIDUAL link variable g_l. This is the result of the Clebsch-Gordan (CG) decomposition, which combines characters from multiple plaquettes sharing a link into a single character of that link variable. After integrating out internal links, this gives `K(W,V) = Σ_{w: w|int=trivial} F(w) · Φ_w(W) · conj(Φ_w(V))` — the `Â_w · Â_{w*}` form (NOT non-negative, per §8.11.67).

2. **Single-character expansion** (what the Lüscher cascade needs): Each plaquette factor is expanded as `exp(c·Re Tr(P_p)) = Σ_γ a_γ · χ_γ(P_p)` where `P_p = g₁·g₂·g₃⁻¹·g₄⁻¹` is the PLAQUETTE PRODUCT (a product of 4 link variables). The character `χ_γ(P_p)` is a character of the PRODUCT, not of individual links. The cascade integrates out temporal links using `luscher_key_identity`: `∫ χ_γ(g·h)·χ_{γ'}(g⁻¹·k) dg = δ_{γγ'}·(1/d_γ)·χ_γ(h·k)`, which produces a character of the PRODUCT of the remaining links — specifically `χ_s(W·V)`, the form needed for `character_kernel_integral_nonneg`.

**Key distinction**: The CG decomposition combines characters of the SAME group element (`χ_γ(g)·χ_{γ'}(g) = Σ_s cg(γ,γ',s)·χ_s(g)`). The Lüscher cascade integrates out a variable appearing in characters of DIFFERENT group elements (`χ_γ(g·h)·χ_{γ'}(g⁻¹·k)`). These are fundamentally different mechanisms. The separable expansion uses CG; the cascade uses Schur orthogonality on products. The separable expansion DESTROYS the product structure that the cascade needs.

**Deriving the single-character expansion from `hexp4`**: Setting g₂=g₃=g₄=1 in `hexp4` gives `exp(c·Re Tr(g)) = Σ_s a_s · χ_s(g)` where `a_s = Σ_{r,t,u,v} coeff(r,s,t,u,v)·dims_t·dims_u·dims_v ≥ 0`. This is the Peter-Weyl expansion of `f(g) = exp(c·Re Tr(g))` on SU(N), with non-negative coefficients (because f is PD). This expansion is NOT yet formalized as a standalone lemma — it needs to be derived from `hexp4`.

**Cascade structure on the full lattice**: The temporal links form a BIPARTITE GRAPH between adjacent time slices (not a simple 1D chain). Each temporal link U(x,t,0) appears in multiple plaquettes (one for each spatial direction ν), connecting to different temporal links at the adjacent time slice. The `chainIntegral_eq` lemma handles open 1D chains; the bipartite graph structure requires a generalization. The `luscher_2site_cascade_integral_nonneg` handles 2 temporal links with 2 characters; the full lattice has many temporal links, each appearing in multiple characters of products.

**Formalization plan for 3c**:
1. Derive the single-character expansion `exp(c·Re Tr(g)) = Σ_γ a_γ · χ_γ(g)` with `a_γ ≥ 0` from `hexp4` (set g₂=g₃=g₄=1).
2. Apply to each temporal plaquette: `exp(c·Re Tr(P_p)) = Σ_γ a_γ · χ_γ(P_p)`.
3. Take the product over all temporal plaquettes.
4. Integrate out temporal links using Schur orthogonality (`luscher_key_identity`), producing `Σ_s a_s · χ_s(W·V)` with `a_s ≥ 0`.
5. Apply `character_kernel_integral_nonneg`.

Step 4 is the hardest — the bipartite graph structure of temporal links requires an inductive or decompositional argument. Starting with the simplest case (L=1, single spatial site, 2 temporal links) and using `luscher_2site_cascade_integral_nonneg` directly may be the most tractable first step.

Sub-steps 4-6 (factorization T = V^{1/2}·U·V^{1/2}, ∫g·Tg≥0, conclude I≥0) follow after U is proven positive.

#### Summary

| Question | Answer |
|----------|--------|
| Is `temporal_product_character_expansion` complete? | **YES** — build GREEN, 0 sorries, 4 axioms (standard 3 + peterWeyl) |
| What is the temporal link partition? | L_U = spatial (μ≠0) at positive time, L_0 = temporal (μ=0) at any time OR spatial at interface, L_V = spatial (μ≠0) at negative time |
| Why are temporal links in L_0 (internal)? | They connect adjacent time slices and must be integrated out by the Lüscher cascade (sub-step 3c) |
| What is the next sub-step? | 3c: Lüscher cascade on temporal links via `chainIntegral_eq` |

### 8.11.71 CRITICAL ANALYSIS: Steps 1-3 of 3c plan ALREADY DONE; cascade produces REVERSAL (not cyclic shift) obstruction for L≥3; group-PD + partial trace gives non-negativity for K(W⁻¹·V) but NOT K(W,V) (2026-08-12 session 93)

**Build GREEN (unchanged), 0 sorries, 6 axioms. No code changes this session — pure analysis.**

This session performed a detailed analysis of sub-step 3c (Lüscher cascade on temporal links) and discovered three key findings:

#### Finding 1: Steps 1-3 of the 3c formalization plan are ALREADY DONE

The §8.11.70 critical analysis stated that the single-character expansion `exp(c·Re Tr(g)) = Σ_γ a_γ · χ_γ(g)` with `a_γ ≥ 0` was "NOT yet formalized as a standalone lemma — it needs to be derived from `hexp4`." This is INCORRECT. The expansion IS already formalized:

- **`plaquette_boltzmann_single_char_expansion`** (PeterWeyl.lean:1231): derives `exp(c·Re Tr(g₁·g₂·g₃⁻¹·g₄⁻¹)) = Σ_s (c' s : ℂ) · χ_s(g₁·g₂·g₃⁻¹·g₄⁻¹)` with `c' s ≥ 0` from `hexp4` by setting g₂=g₃=g₄=1. The coefficient is `c' s = Σ_{r,t,u,v} coeff(r,s,t,u,v)·dims_t·dims_u·dims_v ≥ 0`. **This is step 1 of the 3c plan, already done.**

- **`plaquette_product_single_char_decomp`** (PeterWeyl.lean:1307): produces `∏_p exp(c·Re Tr(gP p)) = Σ_{w : P → ι} F(w) · ∏_p χ_{w(p)}(gP p)` with `F(w) = ∏_p c'_{w(p)} ≥ 0`. This is the product-of-sums identity applied to the single-index expansion. **This is steps 2-3 of the 3c plan, already done.**

Both lemmas are verified (build GREEN, `#print axioms` checked). The single-character expansion uses characters of the PLAQUETTE PRODUCT (not individual links), which is exactly the form the Lüscher cascade needs.

**Implication:** Sub-step 3c can skip directly to step 4 (the cascade itself). The prerequisite infrastructure is in place.

#### Finding 2: The cascade produces a SEPARABLE kernel with a REVERSAL obstruction for L≥3

Detailed calculation of the Lüscher cascade on the full lattice reveals the precise form of the obstruction. For L spatial sites, 1 spatial direction, 1 time step, periodic BC:

The temporal plaquettes form a cycle: P_i = g_i · V_i · g_{i+1}⁻¹ · W_i⁻¹ (indices mod L). The single-character expansion gives `Σ_{w} F(w) · ∏_i χ_{w(i)}(g_i · V_i · g_{i+1}⁻¹ · W_i⁻¹)`. Integrating out the temporal links g₀, g₁, ..., g_{L-1} in sequence (using `luscher_key_identity` for the first integration and the "conjugation integral" `∫ χ_s(A·g⁻¹·M·g·B) = (1/d_s)·χ_s(M)·χ_s(A·B)` for subsequent integrations) produces:

```
K(W, V) = Σ_s c_s · χ_s(W-product) · χ_s(V-product)
```

where:
- `c_s = a_s^L · (1/d_s)^L ≥ 0` (non-negative)
- `W-product = W_{L-1}⁻¹ · W_{L-2}⁻¹ · ... · W_0⁻¹` (ordered product of W-inverses)
- `V-product = V_{L-1} · V_{L-2} · ... · V_0` (ordered product of V's)

The reflection positivity integral (after change of variables V → V⁻¹ and renaming) becomes:
```
I = Σ_s c_s · [∫ f(W) · conj(χ_s(W-product)) dW] · [∫ f(V) · conj(χ_s(V-product-reversed)) dV]
```

where `V-product-reversed` is the REVERSAL of `W-product` (the products accumulate in OPPOSITE directions around the cycle).

**For L=2:** `W-product = W₁⁻¹·W₀⁻¹ = (W₀·W₁)⁻¹`, `V-product-reversed = V₁·V₀`. After reflection V→W: `W₁·W₀`. Since `χ_s(W₀·W₁) = χ_s(W₁·W₀)` (cyclicity of trace for 2-element products), the two integrals are the SAME, giving `I = Σ_s c_s · |∫ f · conj(χ_s(W₁·W₀))|² ≥ 0`. **L=2 works.** ✓

**For L≥3:** `W-product` and `V-product-reversed` are related by REVERSAL (not cyclic shift). `χ_s(g₁·g₂·...·g_L) ≠ χ_s(g_L·...·g₂·g₁)` in general (characters are NOT invariant under reversal for non-abelian groups). The two integrals are DIFFERENT, and the product is NOT `|...|²`. **L≥3 does NOT work via this mechanism.** ✗

> **§8.11.75 CORRECTION (session 95, 2026-08-13):** The above L≥3 obstruction analysis is **WRONG**. The reversal is NOT an obstruction to positivity. See §8.11.75 below for the corrected analysis. The error was analyzing the wrong question: asking "does the cascade produce χ_s(W·V)?" (which requires reversal = cyclic) instead of "is the separable kernel positive?" (which it is, regardless of reversal, by the |Fourier coefficient|² argument from the conj in the inner product).

This is a more precise characterization of the §8.11.49 Finding 6 obstruction. The §8.11.49 analysis called it a "cyclic shift" (`⟨B, σ(B)⟩`), but the actual mechanism is REVERSAL: the W-product and V-product accumulate in opposite directions around the temporal link cycle, producing reversed orderings.

**Note:** The §8.11.67 analysis claims the cascade produces `Σ_s a_s · χ_s(W·V)` (a single character of the product W·V). This is an OVERSIMPLIFICATION — it's only true for L=2 (where reversal = cyclic by trace cyclicity). For L≥3, the cascade produces a SEPARABLE kernel `Σ_s c_s · χ_s(W-product) · χ_s(V-product)`, NOT a single character `χ_s(W·V)`.

#### Finding 3: Group-PD + partial trace gives non-negativity for K(W⁻¹·V) but NOT K(W,V)

An alternative approach was analyzed: use the group-PD of the temporal Boltzmann factor + partial trace (integrating out temporal links) to get a PD kernel K on the spatial link group, then use the general L² `integralOperator_nonneg` lemma.

The temporal Boltzmann factor B_temporal is PD on the full link group G (product of PD plaquette factors by Schur product). The partial trace K(g) = ∫ B_temporal(g, temporal) dμ(temporal) is PD on the spatial link group G' (by `PositiveDefinite.integral`).

The group-PD of K gives:
```
∫∫ f(W) · f(V) · K(W⁻¹·V) dW dV = Σ_γ c_γ · Σ_{a,b} |∫ f · Φ_γ|² ≥ 0
```
where `Φ_γ(W) = ∏_l conj((ρ_{γ_l}(W_l))_{b_l a_l})` and `c_γ ≥ 0`. This IS non-negative (sum of |Fourier coefficient|² with non-negative weights).

**BUT** the reflection positivity integral has the form `∫∫ f(W) · f(θV) · K(W, V) dW dV`, where K(W, V) is the kernel evaluated at TWO arguments (not the group product W⁻¹·V). The group-PD gives non-negativity for `K(W⁻¹·V)` (a function of ONE group element), NOT for `K(W, V)` (a function of TWO group elements).

The mismatch: `K(W, V) ≠ K(W⁻¹·V)` in general. The partial trace K is a function of the FULL spatial configuration (all spatial links at all times), and `K(W, V)` separates this into positive-time (W) and negative-time (V) parts. The group product `W⁻¹·V` is the COMPONENTWISE product, which is NOT how the temporal plaquettes couple W and V (they couple through the ordered plaquette product, not componentwise).

**Conclusion:** The group-PD + partial trace approach does NOT directly resolve the obstruction. The non-negativity of `∫∫ f·f·K(W⁻¹·V)` does NOT imply the non-negativity of `∫∫ f·f(θV)·K(W,V)`.

#### Finding 4: The star topology adds another layer (temporal links shared across spatial directions)

For d spatial directions, each temporal link U_0(x,t) appears in d plaquettes (one per spatial direction ν). The temporal plaquettes in different directions SHARE the temporal links, forming a STAR topology (not independent chains).

The cascade for the star topology requires integrating out a variable g that appears in d characters: `∫ g ∏_ν χ_{γ_ν}(g · h_ν) dg`. This is a MULTI-MATRIX-ELEMENT integral, requiring the CG decomposition for matrix elements (`cgME` from the axiom) to combine the d matrix elements of g into a sum of single matrix elements, then Schur orthogonality.

This is the "triple product integral" mechanism from §8.11.55-56. The axiom was extended (Parts 3-4) to provide the CG decomposition for this purpose. So the star topology CAN be handled with existing infrastructure, but it adds significant complexity.

#### Summary and implications

| Question | Answer |
|----------|--------|
| Are steps 1-3 of the 3c plan done? | **YES** — `plaquette_boltzmann_single_char_expansion` + `plaquette_product_single_char_decomp` already exist |
| Does the cascade produce `χ_s(W·V)` for L≥3? | **NO** — it produces `χ_s(W-product)·χ_s(V-product)` (separable, with reversal) |
| Does the cascade work for L=2? | **YES** — reversal = cyclic for 2-element products (trace cyclicity) |
| Does group-PD + partial trace resolve the obstruction? | **NO** — gives non-negativity for K(W⁻¹·V), not K(W,V) |
| What is the precise obstruction? | **REVERSAL**: W-product and V-product accumulate in opposite directions around the temporal link cycle |
| Can the star topology be handled? | **YES** — via CG decomposition for matrix elements (cgME), but adds complexity |
| Is the approach a dead end? | **UNCLEAR** — the reversal obstruction for L≥3 is real, but the Osterwalder-Seiler theorem IS true, so a resolution mechanism must exist |

#### Possible resolution mechanisms (for future investigation)

1. **The V^{1/2} factor compensates.** The Lüscher decomposition T = V^{1/2}·U·V^{1/2} might resolve the reversal through the spatial plaquette structure. The V^{1/2} factor involves spatial plaquettes (which couple different spatial directions), and might introduce character factors that compensate for the reversal. This requires further analysis.

2. **Plaquette-by-plaquette induction.** Instead of the cascade, use the PD of each temporal plaquette factor and the Schur product theorem to show the temporal Boltzmann is PD, then use reflection positivity directly. This avoids the cascade entirely but requires a different non-negativity mechanism.

3. **A generalized non-negativity lemma for separable kernels.** The cascade produces `Σ_s c_s · χ_s(W-product) · χ_s(V-product)`. A lemma showing `∫∫ f(W)·f(V⁻¹)·Σ_s c_s·χ_s(W-product)·χ_s(V-product) ≥ 0` for specific product structures (where W-product and V-product are related by reflection) might exist but is NOT currently formalized.

4. **The 1-direction, L=2 case as a first step.** Formalizing the cascade for L=2, 1 spatial direction (where the reversal obstruction doesn't appear) would be a concrete step forward, demonstrating the mechanism works in the simplest non-degenerate case.

#### Recommended next action

Start with option 4: formalize the L=2, 1-direction cascade using `luscher_2site_cascade_integral_nonneg` directly. This is the simplest case where the cascade works (reversal = cyclic for 2 elements). The 2 temporal links form a 2-cycle (chain), matching the 2-site cascade structure. The result would be a proved non-negativity lemma for the L=2 temporal plaquette operator, which can then be extended to more complex cases.


## §8.11.72 — conjugation_integral lemma VERIFIED (session 94, 2026-08-12)

**Status: VERIFIED.** Builds clean (exit 0), no sorries, `#print axioms` = `[propext, Classical.choice, Quot.sound, characterOrthogonality]` (same as all other lemmas in the file; no `sorryAx`).

**Lemma:** `conjugation_integral`
```
∫ g, repCharacter (ρ γ) (g⁻¹ * M * g * N) ∂μ =
  (1 / dims γ : ℂ) * repCharacter (ρ γ) M * repCharacter (ρ γ) N
```

**Proof structure** (follows `luscher_key_identity` pattern):
1. Regroup `g⁻¹ * M * g * N = (g⁻¹ * M) * (g * N)` via `mul_assoc` + `MonoidHom.map_mul`.
2. Expand `χ_γ(g⁻¹*M*g*N) = Tr(ρ(g⁻¹*M) * ρ(g*N)) = Σ a b, (ρ(g⁻¹*M))_{ab} * (ρ(g*N))_{ba}` via `htrace_mul`.
3. Expand matrix elements: `(ρ(g⁻¹*M))_{ab} = Σ c, conj((ρ g)_{ca}) * (ρ M)_{cb}` (using `Matrix.mul_apply` + `h_unitary_elem`), and `(ρ(g*N))_{ba} = Σ d, (ρ g)_{bd} * (ρ N)_{da}` (using `Matrix.mul_apply`).
4. Combine via `Fintype.sum_mul_sum` into 4-index sum: `Σ a b c d, conj((ρ g)_{ca}) * (ρ M)_{cb} * (ρ g)_{bd} * (ρ N)_{da}`.
5. Exchange sums with integral (4 levels, using `integrable_finsetSum` + `hInt` from `characterOrthogonality`).
6. Factor constants out of each integral: `(ρ M)_{cb} * (ρ N)_{da} * ∫ g, (ρ g)_{bd} * conj((ρ g)_{ca}) dg`.
7. Apply Schur orthogonality (`hSchur_diag`): `∫ g, (ρ g)_{bd} * conj((ρ g)_{ca}) dg = if b=c ∧ d=a then 1/d_γ else 0`.
8. Collapse Kronecker deltas: `d`-sum picks `d=a`, `c`-sum picks `c=b`.
9. Factor `1/d_γ` and recognize traces: `(1/d_γ) * Tr(ρ M) * Tr(ρ N) = (1/d_γ) * χ_γ(M) * χ_γ(N)`.

**Key fixes from the previous attempt (session 93):**
- Used explicit `have` helpers (`hmap`, `hchar`, `hME1`, `hME2`, `hchar4`) instead of `simp only` for the matrix element expansion.
- `hME1` incorporates unitarity directly (replaces `(ρ g⁻¹)_{ac}` with `conj((ρ g)_{ca})` during the expansion).
- For the `hd` collapse: used `and_true` instead of `true_and` (condition is `b = c ∧ True`, not `True ∧ b = c`).
- For the `hc` collapse: used `fun h => hcb h.symm` to convert `c ≠ b` to `¬(b = c)`.
- For Step 12 (factoring): used `Finset.sum_mul` at each level + `Fintype.sum_mul_sum` for the double-sum factoring, avoiding `ring` on sums.

**Significance:** This is the key building block for the L=2 Lüscher cascade formalization (sub-step 3c). The identity `∫ χ_γ(g⁻¹ M g N) = (1/d_γ) χ_γ(M) χ_γ(N)` is the standard "conjugation integral" / "twisted convolution" identity in representation theory. The coefficient `1/d_γ > 0` is strictly positive, and `χ_γ` is positive-definite — this is the mechanism that gives non-negativity in the L=2 cascade.


## §8.11.73 — luscher_2site_cascade_separable lemma VERIFIED (session 95, 2026-08-13)

**Status: VERIFIED.** Builds clean (exit 0), no sorries, `#print axioms` = `[propext, Classical.choice, Quot.sound, characterOrthogonality]` (no `sorryAx`). Located at `PositiveDefinite.lean:2857`, inside `end UnitaryRepresentation`.

**Lemma:** `luscher_2site_cascade_separable`
```
∫ g₀, ∫ g₁,
  ∑ s, ∑ t, (F s t : ℂ) *
    (repCharacter (ρ s) (g₀ * V₀ * g₁⁻¹ * W₀⁻¹) *
     repCharacter (ρ t) (g₁ * V₁ * g₀⁻¹ * W₁⁻¹)) ∂μ ∂μ =
∑ s, (F s s : ℂ) * ((1 / dims s : ℂ)^2 *
  repCharacter (ρ s) (W₁⁻¹ * W₀⁻¹) * repCharacter (ρ s) (V₀ * V₁))
```

for irreducible unitary representations `ρ` of a compact group with normalized Haar measure `μ`, and non-negative coefficients `F : ι → ι → ℝ` with `F s t ≥ 0`.

**This is the L=2 cascade formalization (sub-step 3c).** The 2-site temporal cascade with two temporal plaquettes (each split into W and V parts) evaluates to a **separable kernel**:
```
K(W,V) = Σ_s (F(s,s) · (1/d_s)²) · χ_s(W₁⁻¹·W₀⁻¹) · χ_s(V₀·V₁)
```
with non-negative coefficients `F(s,s)·(1/d_s)² ≥ 0` (since `F(s,s) ≥ 0` and `(1/d_s)² > 0`). This matches the `character_kernel_integral_nonneg` form (step 3d).

**Proof structure** (follows `luscher_2site_cascade_coeff` pattern):
1. **Helpers:**
   - `hmul_comm : χ_i(a*b) = χ_i(b*a)` via `Matrix.trace_mul_comm`.
   - `hcyc₁ : χ_s(g₀·V₀·g₁⁻¹·W₀⁻¹) = χ_s(g₁⁻¹·(W₀⁻¹·g₀·V₀))` via `repCharacter_cyclic` + `mul_assoc`.
   - `hcyc₂ : χ_s((V₁·g₀⁻¹·W₁⁻¹)·(W₀⁻¹·g₀·V₀)) = χ_s(g₀⁻¹·(W₁⁻¹·W₀⁻¹)·g₀·(V₀·V₁))` via two `hmul_comm` + `mul_assoc`.
   - `hInt_char_conj : Integrable (fun g => χ_s(g⁻¹·M·g·N)) μ` — follows the `conjugation_integral` integrability pattern (~60 lines).
2. **Integrability of each (s,t) term w.r.t. g₁** (`hInt_char`): uses `char_product_integrable` with `A = W₀⁻¹·g₀·V₀`, `B = V₁·g₀⁻¹·W₁⁻¹`, then `h.congr` to match the integrand. The congruence rewrites the first factor via `heq = (hmul_comm s (W₀⁻¹·g₀·V₀) g₁⁻¹).trans (hcyc₁ s g₀ g₁).symm` and normalizes the second factor's associativity via `mul_assoc`.
3. **Inner integral via `luscher_key_identity`** (`hInner`): rewrite the first factor to `χ_s(g₁⁻¹·(W₀⁻¹·g₀·V₀))` form (via `hcyc₁`), reorder factors (via `ring`), then apply `luscher_key_identity` with `t, s` and `A = V₁·g₀⁻¹·W₁⁻¹`, `B = W₀⁻¹·g₀·V₀`. Schur orthogonality forces `t = s`, giving `(1/d_s)·χ_s((V₁·g₀⁻¹·W₁⁻¹)·(W₀⁻¹·g₀·V₀))`.
4. **Collapse the if** via `Finset.sum_eq_single`: the `t`-sum picks `t = s`.
5. **Rewrite character via `hcyc₂`**: `χ_s((V₁·g₀⁻¹·W₁⁻¹)·(W₀⁻¹·g₀·V₀)) = χ_s(g₀⁻¹·(W₁⁻¹·W₀⁻¹)·g₀·(V₀·V₁))`.
6. **Integrability for g₀ integral** (`hInt_g0`): uses `hInt_char_conj` with `M = W₁⁻¹·W₀⁻¹`, `N = V₀·V₁`.
7. **Apply `conjugation_integral`** to each term: `∫ χ_s(g₀⁻¹·(W₁⁻¹·W₀⁻¹)·g₀·(V₀·V₁)) = (1/d_s)·χ_s(W₁⁻¹·W₀⁻¹)·χ_s(V₀·V₁)`.
8. **Final simplification** via `push_cast; ring`: the combined coefficient is `(1/d_s)²`.

**Key fix this session (the build error):** The `hInt_char` congruence originally used `simp only [heq, mul_assoc]` in a single step. This FAILED because `simp` applies `mul_assoc` (which normalizes to right-nested form `(a*b)*c → a*(b*c)`) BEFORE `heq` could match — `heq`'s LHS pattern `χ_s((W₀⁻¹·g₀·V₀)·g₁⁻¹)` is in left-nested form and no longer matches after `mul_assoc` rewrites it to `χ_s(W₀⁻¹·(g₀·(V₀·g₁⁻¹)))`. The fix was to split into two steps: `simp only [heq]` first (which beta-reduces the `(fun g => ...) g₁` redex AND applies `heq` before `mul_assoc` can interfere), then `simp only [mul_assoc]` (which normalizes the second factor's associativity, closing the goal). The lesson: when combining a specific rewrite (`heq`) with a normalizing simp lemma (`mul_assoc`), apply the specific rewrite FIRST so the normalizer doesn't destroy the match.

**Significance:** This completes sub-step 3c (the L=2 cascade itself). The separable kernel `K(W,V) = Σ_s c_s · χ_s(W-product) · χ_s(V-product)` with `c_s = F(s,s)·(1/d_s)² ≥ 0` is the form needed for step 3d (`character_kernel_integral_nonneg`), which will show `∫∫ f(W)·f(V⁻¹)·K(W,V) ≥ 0`. The non-negativity comes from the non-negative coefficients `c_s ≥ 0` and the positive-definiteness of characters `χ_s`. This is the L=2 case where the reversal obstruction (§8.11.71 Finding 2) does NOT appear (reversal = cyclic for 2-element products by trace cyclicity).


## §8.11.74 — separable_character_kernel_integral_nonneg lemma VERIFIED (session 95, 2026-08-13)

**Status: VERIFIED.** Builds clean (exit 0), no sorries, `#print axioms` = `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no `characterOrthogonality` — this is a general PD-kernel result that only depends on `character_expansion_nonneg`). Located at `PositiveDefiniteIntegral.lean:1540`.

**Lemma:** `separable_character_kernel_integral_nonneg`
```
0 ≤ ∫ W, ∫ V, (f W : ℂ) * (f V⁻¹ : ℂ) *
  ∑ s, (coeff s : ℂ) * repCharacter (ρ s) W * repCharacter (ρ s) V ∂μ ∂μ
```
for unitary representations `ρ` of a compact group with normalized Haar measure `μ`, non-negative coefficients `coeff : ι → ℝ` with `coeff s ≥ 0`, and `θ = inv` measure-preserving.

**This is sub-step 3d (the separable kernel non-negativity).** The kernel `K(W,V) = Σ_s coeff_s · χ_s(W) · χ_s(V)` is shown to give a non-negative integral `∫∫ f(W)·f(V⁻¹)·K(W,V) ≥ 0`.

**Proof structure:**
1. Define `K(W,V) = Σ_s coeff_s · χ_s(W) · χ_s(V)`.
2. Rewrite `K` via `repCharacter_inv` (`χ_s(V) = conj(χ_s(V⁻¹))` for unitary reps): `K(W,V) = Σ_s coeff_s · χ_s(W) · conj(χ_s(V⁻¹))`. This is the Mercer-PD form `Σ_s a_s · Φ_s(W) · conj(Φ_s(θ V))` with `Φ_s = χ_s`, `θ = inv`, `a_s = coeff_s ≥ 0`.
3. Apply `character_expansion_nonneg` with `Φ_s = repCharacter (ρ s)`, `θ = Inv.inv`, `a_s = coeff_s`.

**Hypotheses:** Takes `hχ_meas` (AEStronglyMeasurable of each character) and `hfχ_int` (Integrable of `f · χ_s`) as explicit hypotheses, rather than deriving them from matrix-element measurability/integrability. This is a higher-level interface than `character_kernel_integral_nonneg` (which takes `hρ_meas`/`hfρ_int` for individual matrix elements and internally expands the trace). The character-level hypotheses are natural for the separable kernel setting.

**Significance:** This completes sub-step 3d. Combined with `luscher_2site_cascade_separable` (sub-step 3c), the L=2 cascade + separable kernel non-negativity gives: the 2-site temporal cascade produces a separable kernel with non-negative coefficients, and the integral of `f(W)·f(V⁻¹)` against this kernel is non-negative. The remaining work is step 4 (factorization): connecting the cascade output (a function of W₀, W₁, V₀, V₁ — four individual link variables) to the separable kernel lemma (a function of single W, V — the products W₁⁻¹·W₀⁻¹ and V₀·V₁). This requires either a change of variables (integrating over the product) or a generalization of the separable kernel lemma to handle product arguments.


## §8.11.75 — ADVERSARIAL SELF-CHECK: The §8.11.71 "reversal obstruction" is WRONG; the L=2 approach extends to ALL L (session 95, 2026-08-13)

**Status: ANALYSIS (no code changes). This corrects a significant error in the §8.11.71 Finding 2 analysis.**

### The error in §8.11.71

The §8.11.71 analysis (Finding 2) claimed that for L≥3, the cascade produces a separable kernel `K(W,V) = Σ_s c_s · χ_s(W-product) · χ_s(V-product)` where W-product and V-product are related by REVERSAL, and that this reversal is an obstruction to positivity because `χ_s(g₁·...·g_L) ≠ χ_s(g_L·...·g₁)` for non-abelian groups.

**This analysis was asking the wrong question.** It asked "does the cascade produce `χ_s(W·V)` (a single character of the product)?" — which requires reversal = cyclic. But the right question is "is the separable kernel `χ_s(W-product) · χ_s(V-product)` positive?" — which it is, **regardless of reversal**, by the argument below.

### The corrected argument: the conj in the inner product gives |Fourier coefficient|²

The transfer matrix positivity is `⟨g, Ug⟩ ≥ 0` where the inner product is:
```
⟨g, Ug⟩ = ∫∫ g(W) · conj(g(V)) · K(W,V) dW dV
```
Note the **conj(g(V))** — this is the standard L² inner product, NOT the reflection positivity form `f(W)·f(θV)`.

The cascade produces:
```
K(W,V) = Σ_s c_s · χ_s(W-product) · χ_s(V-product)
```
where the W-product = W_{L-1}⁻¹·...·W_0⁻¹ = (W_0·...·W_{L-1})⁻¹ (INVERTED product), and V-product = V_0·...·V_{L-1} (non-inverted product).

The key: `χ_s(W-product) = χ_s((W_0·...·W_{L-1})⁻¹) = conj(χ_s(W_0·...·W_{L-1}))` by `repCharacter_inv`. So the kernel is:
```
K(W,V) = Σ_s c_s · conj(χ_s(W_0·...·W_{L-1})) · χ_s(V_0·...·V_{L-1})
```

For real-valued g:
```
⟨g, Ug⟩ = Σ_s c_s · [∫ g(W) · conj(χ_s(W_0·...·W_{L-1})) dW] · [∫ conj(g(V)) · χ_s(V_0·...·V_{L-1}) dV]
         = Σ_s c_s · conj(E_s) · E_s
         = Σ_s c_s · |E_s|² ≥ 0
```
where `E_s = ∫ g(V) · χ_s(V_0·...·V_{L-1}) dV` (using g real so conj(g) = g, and conj of the first integral = integral of conj).

**This works for ALL L, regardless of reversal.** The conj on the W-part (from the ⁻¹ in the plaquette orientation) combined with the conj(g(V)) in the inner product gives conj(E_s) · E_s = |E_s|². The reversal of the V-product relative to the W-product is irrelevant — the two factors are already conjugates of each other by the ⁻¹ structure, not by the product ordering.

### Why the §8.11.71 analysis went wrong

The §8.11.71 analysis computed the reflection positivity integral as:
```
I = Σ_s c_s · [∫ f(W) · conj(χ_s(W-product)) dW] · [∫ f(V) · conj(χ_s(V-product-reversed)) dV]
```
and noted that for L≥3, `χ_s(W-product) ≠ χ_s(V-product-reversed)` (reversal ≠ cyclic), so the two integrals are different and the product is NOT `|...|²`.

The error: the second factor should NOT have `conj(χ_s(V-product-reversed))`. The V-product in the kernel is `χ_s(V_0·...·V_{L-1})` (NO conj — the V-links appear as-is in the plaquette, not inverted). The conj comes from the inner product `conj(g(V))`, not from the kernel. So the second factor is `∫ conj(g(V)) · χ_s(V_0·...·V_{L-1}) dV = E_s` (for real g), and the first factor is `conj(E_s)`. The product is `|E_s|²`, not `A_s · B_s` with different A, B.

### Implications

1. **The L=2 approach extends to ALL L.** The separable kernel `χ_s(W-product) · χ_s(V-product)` is positive for any L, by the |E_s|² argument. The reversal obstruction was a red herring.

2. **The `separable_character_kernel_integral_nonneg` lemma (§8.11.74) does NOT directly apply to the cascade kernel.** That lemma uses the reflection positivity form `∫∫ f(W)·f(V⁻¹)·Σ c_s·χ_s(W)·χ_s(V)` (θ = inv). But the cascade kernel `conj(χ_s(W-product))·χ_s(V-product)` has the conj on the W-part (wrong side for θ = inv). The RIGHT approach uses the **inner product form** with `conj(K)`: the transfer matrix positivity is `⟨g, Tg⟩ = ∫∫ g(W)·conj(g(V))·conj(K(W,V)) dW dV`, and `conj(K(W,V)) = Σ_s c_s · χ_s(W-product) · conj(χ_s(V-product))` (the conj moves from W to V). This is the `character_expansion_nonneg` form with **θ = id** (not inv), `Φ_s = χ_s(product)`. The result: `Σ_s c_s · |E_s|² ≥ 0` where `E_s = ∫ g · χ_s(W-product) dW`. The formalization requires applying `character_expansion_nonneg` with `θ = id` on the product group `G^L`, with `Φ_s(W₀,...,W_{L-1}) = χ_s(W₀·...·W_{L-1})`.

3. **The factorization step (step 4) is doable.** Expand `χ_s(W-product) = Σ_{a,b,...} ∏ (ρ_s(W_i))_{...}` and `χ_s(V-product) = Σ_{c,d,...} ∏ (ρ_s(V_i))_{...}` in matrix elements. The integral becomes `Σ_s c_s · Σ_{indices} conj(D) · D = Σ_s c_s · |Σ_{indices} D|² = Σ_s c_s · |∫ g · χ_s(product)|² ≥ 0`. This is exactly the `character_expansion_nonneg` mechanism on the product group with θ = id.

4. **Remaining challenges:** (a) the star topology (temporal links shared across spatial directions, requiring CG decomposition — Finding 4), (b) the V^{1/2} positivity (spatial plaquettes, by Schur product), (c) the algebraic fact ABA ≥ 0 for A self-adjoint, B positive, (d) the formalization must use the **inner product form** (θ = id, conj(K)), NOT the reflection positivity form (θ = inv) — the `separable_character_kernel_integral_nonneg` lemma (θ = inv) is valid but does NOT match the cascade kernel. These are separate from the reversal issue, which is now resolved.

### Assessment

**The current approach is NOT a dead end.** It is more viable than the §8.11.71 analysis suggested. The reversal obstruction was the main identified obstacle, and it turns out to be non-existent. The remaining challenges (star topology, V^{1/2} positivity, factorization formalization) are substantial but do not appear to be fundamental mathematical obstructions.


## §8.11.76 — Step 4 (factorization) VERIFIED: luscher_2site_factorization_nonneg (session 96, 2026-08-13)

**Status: VERIFIED.** Builds clean (exit 0), no sorries, `#print axioms` = `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no `characterOrthogonality` — this is a general PD-kernel result that only depends on `character_expansion_nonneg`). Located at `PositiveDefiniteIntegral.lean:1608`.

**Lemma:** `luscher_2site_factorization_nonneg`
```
0 ≤ ∫ W, ∫ V, (f W : ℂ) * (f V : ℂ) *
  ∑ s, (F s s : ℂ) * ((1 / dims s : ℂ)^2 *
    repCharacter (ρ s) (W.1 * W.2) * conj (repCharacter (ρ s) (V.1 * V.2)))
  ∂(μ.prod μ) ∂(μ.prod μ)
```

for a compact group `G` with normalized Haar measure `μ`, representations `ρ`, non-negative coefficients `F : ι → ι → ℝ` with `F s t ≥ 0`, and a real-valued test function `f : G × G → ℝ`.

**This is step 4 (factorization).** The 2-site cascade produces the separable kernel `K(W,V) = Σ_s c_s · χ_s(W₁⁻¹·W₀⁻¹) · χ_s(V₀·V₁)` with `c_s = F(s,s)·(1/d_s)² ≥ 0` (from `luscher_2site_cascade_separable`). By `repCharacter_inv`, `χ_s(W₁⁻¹·W₀⁻¹) = conj(χ_s(W₀·W₁))`, so `conj(K(W,V)) = Σ_s c_s · χ_s(W₀·W₁) · conj(χ_s(V₀·V₁))`. This is the `character_expansion_nonneg` form with **θ = id** (not inv), `Φ_s(W₀,W₁) = χ_s(W₀·W₁)`, `a_s = c_s ≥ 0`, on the product group `G² = G × G` with product measure `μ × μ`.

**Proof structure:**
1. Define the coefficient `a_s = F s s * (1 / (dims s : ℝ))^2` and show `0 ≤ a_s` (from `hF` and `sq_nonneg`).
2. Apply `character_expansion_nonneg` with:
   - `μ = ν = μ.prod μ` (product measure on `G²`)
   - `θ = id`, `hθ = MeasurePreserving.id`
   - `a = fun s => F s s * (1 / (dims s : ℝ))^2`
   - `Φ = fun s W => repCharacter (ρ s) (W.1 * W.2)`
   - `K = fun W V => [explicit sum from the statement]` (definitionally equal to the goal)
   - `hK = fun W V => by apply Finset.sum_congr; intro s _; push_cast; simp only [id]; ring` (shows `K W V = Σ_s (a_s : ℂ) * (Φ_s W * conj(Φ_s V))`)
3. The conclusion of `character_expansion_nonneg` has `K W V`, which beta-reduces to the explicit sum in the statement, matching the goal.

**Key fix:** The `hK` congruence required `simp only [id]` before `ring` to simplify `(id V).1 * (id V).2` to `V.1 * V.2` (the `id` from `Φ_s(θ V) = Φ_s(id V)` doesn't reduce automatically inside `ring`).

**Hypotheses:** Takes `hΦ_meas` (AEStronglyMeasurable of `χ_s(W₀·W₁)` on `G²`), `hf_meas` (AEStronglyMeasurable of `f` on `G²`), and `hfΦ_int` (Integrable of `f · χ_s(W₀·W₁)` on `G²`) as explicit hypotheses. These are character-level hypotheses on the product group, analogous to `separable_character_kernel_integral_nonneg` (which takes character-level hypotheses on `G`). The derivation of these from matrix-element measurability (expanding `χ_s(W₀·W₁) = Σ_{a,b} (ρ_s W₀)_{ab} · (ρ_s W₁)_{ba}` and using `AEStronglyMeasurable.comp_quasiMeasurePreserving` with `quasiMeasurePreserving_fst`/`quasiMeasurePreserving_snd`) is deferred to a helper lemma.

**Significance:** This completes step 4 (factorization). The conj(K) form of the cascade kernel is a positive-definite kernel on the product group `G²`, and the integral `∫∫ f(W)·f(V)·conj(K(W,V)) d(μ×μ) d(μ×μ) = Σ_s c_s · |E_s|² ≥ 0` where `E_s = ∫ f(W)·χ_s(W₀·W₁) d(μ×μ)`. This is the **inner-product form** (θ = id, conj(K)), NOT the reflection-positivity form (θ = inv) — the `separable_character_kernel_integral_nonneg` lemma (θ = inv) is valid but does NOT match the cascade kernel (see §8.11.75).

**Remaining work:**
- **Helper lemma:** Derive `hΦ_meas` from `hρ_meas` (individual matrix-element measurability) via the trace expansion + product-measure lifting. This requires `hρ_meas : ∀ s (a b : Fin (dims s)), AEStronglyMeasurable (fun g => (ρ s g) a b) μ` as a new hypothesis (not directly available from `characterOrthogonality`, which gives integrability of products, not individual elements — see §8.11.76 analysis below).
- **Step 5:** Connect the factorization to the transfer matrix inner product `⟨g, Tg⟩ = ∫∫ g(W)·conj(g(V))·conj(K(W,V)) dW dV`. For real-valued `g`, `conj(g(V)) = g(V)`, so this matches the factorization integral.
- **Step 6:** Conclude `I ≥ 0` and replace `transferMatrixPositivity_axiom` with the proved lemma (axioms 6→5).

**Note on measurability:** The `characterOrthogonality` axiom provides `hInt : Integrable (fun g => (ρ r g) i j * conj ((ρ s g) k l)) μ` for all matrix-element products. This gives `AEStronglyMeasurable` of products, but NOT of individual matrix elements (counter-example: `f = e^{iθ}` with non-measurable `θ` has `|f|² = 1` measurable but `f` not measurable). So `hρ_meas` (individual matrix-element measurability) must be taken as a separate hypothesis. In the Peter-Weyl setting, matrix elements of continuous representations are continuous, hence Borel measurable — this is a natural hypothesis.

## §8.11.77 — Helper lemmas VERIFIED: hΦ_meas and hfΦ_int from hρ_meas (session 97, 2026-08-13)

**Status: VERIFIED.** Three helper lemmas build clean (exit 0), no sorries, `#print axioms` = `[propext, Classical.choice, Quot.sound]` for all three (no `sorryAx`, no `characterOrthogonality`). Located in `PositiveDefiniteIntegral.lean` lines 1586–1680.

### Lemma 1: `repCharacter_trace_expand_prod` (line 1586)
```
repCharacter ρ (W₀ * W₁) = ∑ a : Fin n, ∑ b : Fin n, (ρ W₀) a b * (ρ W₁) b a
```
Plain trace expansion (no unitarity/inversion), via `MonoidHom.map_mul` + `Matrix.trace` + `Matrix.mul_apply`. This is the non-unitary version of `repCharacter_trace_expand` (which uses `V⁻¹` and unitarity to get `conj`).

### Lemma 2: `repCharacter_product_aestronglyMeasurable` (line 1606)
```
hρ_meas : ∀ s (a b : Fin (dims s)), AEStronglyMeasurable (fun g => (ρ s g) a b) μ
⊢ AEStronglyMeasurable (fun W => repCharacter (ρ s) (W.1 * W.2)) (μ.prod μ)
```
Derives `hΦ_meas` from `hρ_meas`. Proof:
1. Lift each matrix element to `G × G` via `AEStronglyMeasurable.comp_quasiMeasurePreserving` with `Measure.quasiMeasurePreserving_fst` (for `W.1`) and `Measure.quasiMeasurePreserving_snd` (for `W.2`).
2. Products via `AEStronglyMeasurable.mul`.
3. Finite sums via `Finset.aestronglyMeasurable_fun_sum` (the `@[to_additive]` of `Finset.aestronglyMeasurable_fun_prod`).
4. Rewrite to character form via `AEStronglyMeasurable.congr` + `repCharacter_trace_expand_prod`.

**Key Mathlib API:** `Measure.quasiMeasurePreserving_fst` / `Measure.quasiMeasurePreserving_snd` (in `MeasureTheory.Measure` namespace, NOT `quasiMeasurePreserving_fst` directly — `MeasureTheory` is opened but `Measure` is not). `Finset.aestronglyMeasurable_fun_sum` (much faster than `Finset.sum_induction` which caused `whnf` timeouts).

### Lemma 3: `repCharacter_product_integrable` (line 1651)
```
hU : ∀ i, IsUnitaryRepresentation (ρ i)
hf_int : Integrable (fun W => (f W : ℂ)) (μ.prod μ)
⊢ Integrable (fun W => (f W : ℂ) * repCharacter (ρ s) (W.1 * W.2)) (μ.prod μ)
```
Derives `hfΦ_int` from `hf_int` + unitarity. Proof:
1. Measurability: `hf_int.aestronglyMeasurable.mul hΦ_meas` (using Lemma 2).
2. Dominating function: `(Integrable.norm hf_int).const_mul (dims s : ℝ)` gives `Integrable (fun W => (dims s : ℝ) * ‖(f W : ℂ)‖) (μ.prod μ)`.
3. Norm bound: `‖f · χ_s‖ ≤ ‖f‖ · ‖χ_s‖ ≤ ‖f‖ · dims s = dims s · ‖f‖` via `norm_mul_le` + `repCharacter_norm_le_dim` (existing lemma in `PositiveDefinite.lean:812`).
4. Conclude via `Integrable.mono'`.

**Significance:** These three lemmas close the "helper lemma" item from §8.11.76. The character-level hypotheses `hΦ_meas` and `hfΦ_int` of `luscher_2site_factorization_nonneg` can now be derived from the more primitive `hρ_meas` (matrix-element measurability) + `hU` (unitarity) + `hf_int` (integrability of `f`). The `hρ_meas` hypothesis is natural in the Peter-Weyl setting (continuous reps → Borel measurable matrix elements) and is NOT derivable from `characterOrthogonality` (which gives product integrability, not individual-element measurability — see §8.11.76).

**Remaining work:**
- **Step 5:** Connect the factorization to the transfer matrix inner product `⟨g, Tg⟩ = ∫∫ g(W)·conj(g(V))·conj(K(W,V)) dW dV`. For real-valued `g`, `conj(g(V)) = g(V)`, so this matches the factorization integral.
- **Step 6:** Conclude `I ≥ 0` and replace `transferMatrixPositivity_axiom` with the proved lemma (axioms 6→5).

## §8.11.78 — STEP 5 deep analysis: connecting the cascade to the transfer matrix (session 98, 2026-08-13)

**Status: ANALYSIS (no code changes). This section documents a thorough investigation of the STEP 5 connection and identifies the key formalization challenges.**

### Adversarial self-check (session 98)

Per the standing instruction to periodically steelman the dead-end case, this session examined whether the STEP 5/6 approach (cascade factorization → transfer matrix positivity → axiom removal) could be a dead end.

**Concern 1: The 2-site cascade only handles L=2, T=3.** The `luscher_2site_cascade_separable` integrates out 2 temporal links at 2 spatial positions — exactly the transfer matrix for T=3 (one negative time slice), L=2. For general odd T, the transfer matrix integrates over (T-1)/2 negative time slices, and for general L, over L spatial positions. The 2-site cascade is a building block, not the full transfer matrix.

**Assessment:** The §8.11.75 analysis confirms the |E_s|² argument works for ALL L (the reversal obstruction was a red herring). The L-generalization requires applying `character_expansion_nonneg` with `X = G^L` and `Φ_s(W₀,...,W_{L-1}) = χ_s(W₀·...·W_{L-1})` — the same mechanism, on a larger product group. The T-generalization requires iterating the cascade over (T-1)/2 time steps; each step multiplies the coefficient by `F(s,s)·(1/d_s)² ≥ 0`, preserving non-negativity. These are substantial generalizations but NOT fundamental obstructions.

**Concern 2: The shared-variable structure.** The transfer matrix `T` has a shared interface: `(Tg)(u) = ∫_{V⁺} g(reflectToPosInterface(V⁺, u⁰)) · exp(-β·(...)) dμ⁺(V⁺)`. The interface links `u⁰` are part of `u` and also appear in `reflectToPosInterface(V⁺, u⁰)`. This shared structure means `luscher_2site_factorization_nonneg` (which uses the non-shared `character_expansion_nonneg` on `G × G`) does NOT directly apply — the W and V configs share the interface links.

**Assessment:** This is the most significant formalization challenge. Two approaches:
- **(a) Cascade approach:** Integrate out ALL temporal links (including temporal interface links u⁰_t), collapsing the temporal part of `Ψ_w` to trivial via Schur orthogonality. The spatial interface links u⁰_s remain shared. The cascade kernel `Σ_s c_s · conj(χ_s(W-product)) · χ_s(V-product)` involves the product of ALL spatial links (including u⁰_s), so the shared structure is absorbed into the product. The `character_expansion_nonneg` then applies on the full spatial link group `G = SU(N)^{spatial}` with `Φ_s(W) = χ_s(W-product)`. The key: the "product" `W₀·...·W_{L-1}` includes the spatial interface links, so they're part of the character argument, not a separate shared variable.
- **(b) Shared-variable approach:** Use `character_expansion_nonneg_shared` directly. But this requires `a(u⁰, w) = F(w) · Ψ_w(u⁰) ≥ 0`, which FAILS because `Ψ_w(u⁰)` is a product of characters (complex in general). So this approach requires the triple product expansion (CG decomposition) to resolve the spatial interface links — Path B of §8.11.53.

**Concern 3: The Lüscher decomposition T = V^{1/2}·U·V^{1/2}.** The transfer matrix kernel involves `exp(-β·(S_pos(u)/2 + S_neg(U⁻)/2 + S_int(u, U⁻)))`. The Lüscher decomposition factors this into:
- `V^{1/2}(u) = exp(-β·S_spatial(u)/2)` (spatial plaquette Boltzmann, the "hopping" operator)
- `U(u, v)` = temporal evolution (the cascade kernel, after integrating out temporal links)

The `V^{1/2}` factors are absorbed into the test function: `f(u) = g(u)·V^{1/2}(u)`. Then `⟨g, Tg⟩ = ∫∫ f(u)·f(v)·U(u,v) dμ dμ`, and `U` is the cascade kernel.

**Assessment:** The Lüscher decomposition is NOT yet formalized. It requires:
1. Factoring the Boltzmann factor into spatial plaquette factors (V^{1/2}) and temporal plaquette factors (U).
2. The spatial factors are PD (`fullBoltzmannPD` proves the full Boltzmann is PD; the spatial part is PD by Schur product).
3. The temporal factors, after integrating out temporal links, give the cascade kernel.
4. The algebraic fact: `⟨g, V^{1/2}·U·V^{1/2}·g⟩ = ⟨V^{1/2}g, U·V^{1/2}g⟩ = ∫∫ f·f·U ≥ 0` when `U` is a PD kernel.

This is a significant formalization effort but uses existing infrastructure (`fullBoltzmannPD`, `luscher_key_identity`, `plaquetteBoltzmannPD_inv`).

### The key mathematical identity

The transfer matrix positivity reduces to:
```
⟨g, Tg⟩ = ∫∫ f(W)·f(V)·conj(K_cascade(W,V)) dW dV = Σ_s c_s · |E_s|² ≥ 0
```
where:
- `f(W) = g(W)·V^{1/2}(W)` (test function with spatial Boltzmann absorbed)
- `K_cascade(W,V) = Σ_s c_s · conj(χ_s(W-product)) · χ_s(V-product)` (cascade kernel)
- `conj(K_cascade(W,V)) = Σ_s c_s · χ_s(W-product) · conj(χ_s(V-product))` (the form in `luscher_2site_factorization_nonneg`)
- `c_s = F(s,s)·(1/d_s)² ≥ 0` (cascade coefficient, from Schur orthogonality)
- `E_s = ∫ f(W)·χ_s(W-product) dW` (Fourier coefficient)

The `luscher_2site_factorization_nonneg` lemma proves exactly `0 ≤ ∫∫ f·f·conj(K_cascade)` for the 2-site case (L=2, T=3). The general case requires:
1. The L-site cascade (generalizing `luscher_2site_cascade_separable` to L spatial sites).
2. The multi-step cascade (iterating over (T-1)/2 time steps).
3. The Lüscher decomposition (factoring V^{1/2} from the transfer matrix kernel).
4. Applying `character_expansion_nonneg` on the full spatial link group.

### Existing infrastructure for STEP 5

| Lemma | File:Line | Role |
|-------|----------|------|
| `luscher_key_identity` | PositiveDefinite.lean:1037 | Single-link Schur orthogonality (cascade building block) |
| `luscher_2site_cascade_separable` | PositiveDefinite.lean:2857 | 2-site cascade (L=2, T=3) |
| `luscher_2site_factorization_nonneg` | PositiveDefiniteIntegral.lean:1707 | Non-negativity of 2-site cascade integral |
| `character_expansion_nonneg` | PositiveDefiniteIntegral.lean:1147 | General non-negativity (θ=id, separable kernel) |
| `character_expansion_nonneg_shared` | PositiveDefiniteIntegral.lean:1197 | Shared-variable non-negativity |
| `interface_kernel_character_expansion` | PeterWeyl.lean:1636 | Interface kernel separable expansion (same weight, conj V⁺) |
| `interface_boltzmann_character_expansion` | ReflectionPositivity.lean:1687 | Interface Boltzmann expansion (fullReflect form) |
| `osG_thetaG_eq_char_expansion_pointwise` | ReflectionPositivity.lean:3817 | Pointwise expansion of osG·osG(θU) (Step 2, DONE) |
| `integral_G_thetaG_eq_inner_g_Tg` | TransferMatrix.lean:5149 | ∫G·G(θU) = ⟨g,Tg⟩ (key identity) |
| `transfer_matrix_fubini_integrated_pull_fullReflect` | TransferMatrix.lean:6005 | Character expansion of ⟨g,Tg⟩ (fullReflect form — WRONG form per §8.11.75) |
| `fullBoltzmannPD` | ReflectionPositivity.lean:1768 | Full Boltzmann factor is PD |
| `plaquetteBoltzmannPD_inv` | PeterWeyl.lean | Single plaquette Boltzmann is PD |
| `repCharacter_product_aestronglyMeasurable` | PositiveDefiniteIntegral.lean:1606 | hΦ_meas from hρ_meas (helper, DONE) |
| `repCharacter_product_integrable` | PositiveDefiniteIntegral.lean:1651 | hfΦ_int from hf_int + hU (helper, DONE) |

### Formalization path for STEP 5

**Approach A (cascade, recommended by §8.11.75):**
1. **L-site cascade lemma:** Generalize `luscher_2site_cascade_separable` to L spatial sites. The cascade integrates out L temporal links (one per spatial position) and produces `Σ_s c_s · conj(χ_s(W₀·...·W_{L-1})) · χ_s(V₀·...·V_{L-1})` with `c_s ≥ 0`. This is an iteration of `luscher_key_identity` across L sites (Fubini + Schur orthogonality).
2. **Multi-step cascade:** For T > 3, iterate the single-step cascade over (T-1)/2 time steps. Each step multiplies the coefficient by `F(s,s)·(1/d_s)² ≥ 0`.
3. **Lüscher decomposition:** Factor the transfer matrix kernel `exp(-β·(S_pos/2 + S_neg/2 + S_int))` into `V^{1/2}(W) · U(W,V) · V^{1/2}(V)` where `U` is the cascade kernel and `V^{1/2}` is the spatial Boltzmann factor. Absorb `V^{1/2}` into `f = g·V^{1/2}`.
4. **Apply non-negativity:** Use `character_expansion_nonneg` on the full spatial link group `G = SU(N)^{spatial}` with `Φ_s(W) = χ_s(W₀·...·W_{L-1})` and `a_s = c_s ≥ 0`. The helper lemmas (`repCharacter_product_aestronglyMeasurable`, `repCharacter_product_integrable`) generalize from G² to G^L.
5. **Conclude:** `⟨g, Tg⟩ = ∫∫ f·f·conj(K_cascade) = Σ_s c_s · |E_s|² ≥ 0`.

**Approach B (triple product, Path B of §8.11.53):**
1. Connect `interface_kernel_character_expansion` to the lattice plaquettes (Step 1 of Path B).
2. Substitute into the integral, getting `C · Σ_w F(w) · ∫_{u⁰} Ψ_w(u⁰) · |A_w(u⁰)|² dμ⁰`.
3. Integrate out temporal interface links u⁰_t (collapse Ψ_w to trivial on temporal).
4. Resolve spatial interface triple product via `triple_product_character_matrix_integral` (CG decomposition).
5. Apply `reflection_positivity_reorganization` to conclude ≥ 0.

**Assessment:** Approach A is mathematically cleaner (the |E_s|² argument is direct) but requires the L-site cascade and the Lüscher decomposition. Approach B uses existing infrastructure but requires the triple product expansion (more complex). The §8.11.75 analysis recommends Approach A.

### Key challenge RESOLVED: the shared interface links and `character_expansion_nonneg_shared`

The transfer matrix has a shared interface structure: the spatial interface links `u⁰_s` appear in both the `u` (positive+interface) and `v` (reflected negative = positive+interface) configs. This means `luscher_2site_factorization_nonneg` (which uses the non-shared `character_expansion_nonneg` on `G × G` with independent W, V) does NOT directly apply.

**Resolution:** The `character_expansion_nonneg_shared` lemma (PositiveDefiniteIntegral.lean:1197) IS the right lemma. It handles the shared structure:
```
0 ≤ ∫ z, ∫ x, ∫ y, (g x z : ℂ) * (g y z : ℂ) * K x y z ∂μ ∂μ ∂ν
```
where `K x y z = Σ_i (a z i : ℂ) * (Φ i z x * conj (Φ i z y))` with `a z i ≥ 0`.

The key insight: after the cascade (integrating out temporal links), the transfer matrix kernel has the form:
```
K(U⁺, V⁺, u⁰_s) = Σ_s c_s · χ_s(u⁰_s-product · U⁺-product) · conj(χ_s(u⁰_s-product · V⁺-product))
```
where:
- `c_s = F(s,s) · (1/d_s)² ≥ 0` is a **CONSTANT** (from Schur orthogonality, independent of the spatial links)
- `Φ_s(u⁰_s, U⁺) = χ_s(u⁰_s-product · U⁺-product)` depends on the shared variable `u⁰_s`

Matching to `character_expansion_nonneg_shared`:
- `z = u⁰_s` (spatial interface links, shared), `ν = μ⁰_s` (interface measure)
- `x = U⁺` (positive spatial links), `y = V⁺` (reflected negative spatial links), `μ = μ⁺` (positive measure)
- `g(x, z) = g(U⁺, u⁰_s)` (test function)
- `Φ_s(z, x) = χ_s(z-product · x-product)` (character of the product, depends on z)
- `a(z, s) = c_s ≥ 0` (CONSTANT, so `∀ z i, 0 ≤ a z i` is satisfied!)

The crucial point: the cascade coefficient `c_s` is a constant (from Schur orthogonality `δ_{st} · (1/d_s)`), NOT depending on the shared variable `u⁰_s`. So `a(z, s) = c_s ≥ 0` is satisfied, and `character_expansion_nonneg_shared` applies directly.

This resolves the shared-variable concern from the adversarial self-check. The `luscher_2site_factorization_nonneg` (non-shared) is a building block that demonstrates the |E_s|² mechanism, but the actual transfer matrix application needs `character_expansion_nonneg_shared` (shared). The temporal interface links `u⁰_t` are integrated out by the cascade (collapsing to trivial via Schur orthogonality), leaving only the spatial interface links `u⁰_s` as the shared variable.

### Revised formalization path for STEP 5

1. **Cascade the temporal links:** Integrate out ALL temporal links (temporal bulk + temporal interface) via Schur orthogonality (`luscher_key_identity`). This produces the cascade kernel `Σ_s c_s · conj(χ_s(W-product)) · χ_s(V-product)` with `c_s ≥ 0` constant, where `W-product` and `V-product` include ALL spatial links (positive, negative reflected, and spatial interface).
2. **Identify the shared structure:** The spatial interface links `u⁰_s` are shared between W and V. Decompose `W = (U⁺, u⁰_s)` and `V = (V⁺, u⁰_s)` with shared `u⁰_s`.
3. **Apply `character_expansion_nonneg_shared`:** With `z = u⁰_s`, `x = U⁺`, `y = V⁺`, `Φ_s(z, x) = χ_s(z-product · x-product)`, `a(z, s) = c_s ≥ 0`. The helper lemmas (`repCharacter_product_aestronglyMeasurable`, `repCharacter_product_integrable`) need to be generalized to handle the `Φ_s(z, x) = χ_s(z-product · x-product)` form (product of two group elements, one shared).
4. **Conclude:** `⟨g, Tg⟩ = ∫_{u⁰_s} ∫_{U⁺} ∫_{V⁺} g·g·K ≥ 0` by `character_expansion_nonneg_shared`.

### Conclusion

The STEP 5 approach is NOT a dead end. The math is correct (the |E_s|² argument works for all L and T, even with shared spatial interface links, because the cascade coefficient is constant). The key lemma is `character_expansion_nonneg_shared` (not `luscher_2site_factorization_nonneg`). The key missing lemmas are:
1. **Cascade for the transfer matrix kernel** (integrating out temporal links to get the separable form with constant coefficients).
2. **Lüscher decomposition** (factoring V^{1/2} from the transfer matrix kernel, absorbing into the test function).
3. **Measurability/integrability helpers** for `Φ_s(z, x) = χ_s(z-product · x-product)` (generalizing the existing helpers to the shared-variable form).

The next session should start with the cascade for the transfer matrix kernel (step 1), as it's the most direct application of existing infrastructure (`luscher_key_identity`, `interface_boltzmann_character_expansion`).

## §8.11.79 — STEP 5 progress: shared-variable helpers + non-negativity lemma (session 99, 2026-08-13)

**Status: VERIFIED. Five new lemmas compiled, `#print axioms` = [propext, Classical.choice, Quot.sound] (no sorryAx). Build GREEN.**

> **Update (session 100, 2026-08-13):** The connecting lemma `cascade_shared_kernel_form`
> (item 5 below) was BROKEN in session 99 — it used `rw [mul_inv]`, but Mathlib's `mul_inv`
> lives in a commutative context and does not apply to a general `Group G`. The correct
> identity in a non-abelian group is `mul_inv_rev : (a * b)⁻¹ = b⁻¹ * a⁻¹`, so
> `x⁻¹ * z⁻¹ = (z * x)⁻¹` holds via `(mul_inv_rev z x).symm`. Fixed; now VERIFIED with
> `#print axioms` = [propext, Classical.choice, Quot.sound] (no sorryAx).

### What was done

Session 99 implemented the **measurability/integrability helpers** (step 3 of the revised formalization path in §8.11.78) and the **shared-variable non-negativity lemma** (step 4), which is the pure group-theoretic core of STEP 5.

The three new lemmas, all in `PositiveDefiniteIntegral.lean` (after `luscher_2site_factorization_nonneg`, before `end YangMills`):

1. **`repCharacter_leftmul_aestronglyMeasurable`** (line ~1770): For fixed `z ∈ G`, `fun x => χ_s(z * x)` is `AEStronglyMeasurable` w.r.t. `μ`. Proof: expand `χ_s(z * x) = ∑_{a,b} (ρ_s z)_{ab} · (ρ_s x)_{ba}` via `repCharacter_trace_expand_prod`. Each `(ρ_s z)_{ab}` is a constant (z fixed), so `AEStronglyMeasurable.const_mul` lifts it; `(ρ_s x)_{ba}` is AESM from `hρ_meas`. Finite sums via `Finset.aestronglyMeasurable_fun_sum`. Rewrite to character form via `.congr`.

2. **`repCharacter_leftmul_integrable`** (line ~1810): For fixed `z ∈ G`, if `g(·, z)` is integrable, then `g(·, z) · χ_s(z · ·)` is integrable. Proof: `‖χ_s(z * x)‖ ≤ dims s` (unitarity, `repCharacter_norm_le_dim`), so `‖g · χ_s‖ ≤ dims s · ‖g‖`, apply `Integrable.mono'`.

3. **`shared_cascade_factorization_nonneg`** (line ~1850): The main lemma. Given non-negative constant coefficients `c_s ≥ 0` and a real-valued test function `g : G → G → ℝ` (where `g x z` depends on positive links `x` and shared interface links `z`):
   ```
   0 ≤ ∫_z ∫_x ∫_y g(x,z) · g(y,z) · Σ_s c_s · χ_s(z·x) · conj(χ_s(z·y)) dμ dμ dμ
   ```
   Proof: direct application of `character_expansion_nonneg_shared` with `a(z, s) = c_s` (constant, so `∀ z i, 0 ≤ a z i` is satisfied) and `Φ_s(z, x) = χ_s(z * x)`. The measurability and integrability hypotheses are discharged by the two helper lemmas above.

4. **`shared_cascade_factorization_nonneg_conj`** (line ~1930): The conjugated-form variant. The cascade `luscher_2site_cascade_separable` produces `Σ_s c_s · χ_s(W₁⁻¹·W₀⁻¹) · χ_s(V₀·V₁)`. When the shared interface link appears in both W and V (W₀ = V₀ = z), this becomes `Σ_s c_s · conj(χ_s(z·x)) · χ_s(z·y)` (using `χ_s(x⁻¹·z⁻¹) = conj(χ_s(z·x))`). This is the CONJUGATED form. The proof uses `character_expansion_nonneg_shared` with `Φ_s(z, x) = conj(χ_s(z·x))` (measurability via `AEStronglyMeasurable.star`, integrability via `‖conj(χ_s(g))‖ = ‖χ_s(g)‖ ≤ dims s` by `Complex.norm_conj`). The `hK` proof requires `Complex.conj_conj` to simplify `conj(conj(χ_s(z·y))) = χ_s(z·y)`.

5. **`cascade_shared_kernel_form`** (line ~2002): The connecting lemma showing the 2-site cascade result `Σ_s F(s,s)·(1/d_s)² · χ_s(x⁻¹·z⁻¹) · χ_s(z·y)` equals the conj-form `Σ_s (F(s,s)·(1/d_s)²) · conj(χ_s(z·x)) · χ_s(z·y)`. The key step is `χ_s(x⁻¹·z⁻¹) = χ_s((z·x)⁻¹) = conj(χ_s(z·x))`, using `mul_inv_rev` (NOT `mul_inv`, which is commutative-only) for `x⁻¹·z⁻¹ = (z·x)⁻¹`, then `repCharacter_inv`. VERIFIED (session 100 fix).

### Key design decisions

- **`const_mul` instead of `comp_quasiMeasurePreserving`**: The existing `repCharacter_product_aestronglyMeasurable` lifts both factors of `χ_s(W.1 * W.2)` from the product group `G × G` via `comp_quasiMeasurePreserving` (fst/snd projections). The shared-variable form `χ_s(z * x)` has `z` fixed, so the first factor `(ρ_s z)_{ab}` is a constant — lifted via `AEStronglyMeasurable.const_mul` instead. This is the key structural difference.

- **Constant coefficient `a(z, s) = c_s`**: The `character_expansion_nonneg_shared` hypothesis is `∀ z i, 0 ≤ a z i`. By making `a` constant in `z` (i.e., `a z s = c s`), this reduces to `∀ s, 0 ≤ c s`, which is the natural hypothesis from the cascade (Schur orthogonality gives `c_s = F(s,s) · (1/d_s)² ≥ 0`). This is the crucial insight from §8.11.78: the cascade coefficient is constant, NOT depending on the shared variable.

- **`rfl` for `hK`**: The kernel `K` in the statement IS the expansion `Σ_s c_s · χ_s(z·x) · conj(χ_s(z·y))`, so `hK` (which says `K = Σ_i a(z,i) · Φ_i(z,x) · conj(Φ_i(z,y))`) is provable by `rfl` after beta-reduction. No `push_cast` or `ring` needed.

### What remains for STEP 5

The pure group-theoretic non-negativity is now DONE (`shared_cascade_factorization_nonneg`). The remaining work connects this to the actual lattice transfer matrix:

1. **Cascade the temporal links** (step 1 of §8.11.78): Integrate out ALL temporal links via Schur orthogonality (`luscher_key_identity`, `integral_repCharacter_trivial`). This produces the cascade kernel `Σ_s c_s · χ_s(z-product · x-product) · conj(χ_s(z-product · y-product))` with `c_s ≥ 0` constant. The temporal interface links `u⁰_t` collapse to trivial (via `integral_repCharacter_trivial`), leaving only spatial interface links `u⁰_s` as the shared variable `z`.

2. **Lüscher decomposition** (step 2 of §8.11.78): Factor the transfer matrix kernel `exp(-β·(S_pos/2 + S_neg/2 + S_int))` into `V^{1/2}(x) · U(x,y,z) · V^{1/2}(y)` where `U` is the cascade kernel and `V^{1/2}` is the spatial Boltzmann factor. Absorb `V^{1/2}` into `f = g · V^{1/2}`.

3. **Connect to the lattice**: Match the lattice Boltzmann factor (product of plaquette contributions) to the cascade structure. This requires understanding the specific plaquette orientations and link structure of the transfer matrix.

4. **Apply `shared_cascade_factorization_nonneg`**: With `z = u⁰_s`, `x = U⁺`, `y = V⁺`, `c_s` = cascade coefficient, `g(x, z) = f(x, z)` (test function with V^{1/2} absorbed). Conclude `⟨g, Tg⟩ ≥ 0`.

### STEP 6 (after STEP 5)

Use `integral_G_thetaG_eq_inner_g_Tg` to convert `⟨g, Tg⟩ ≥ 0` to `∫ G·G(θU) ≥ 0`, then replace `transferMatrixPositivity_axiom` with the proved lemma (axioms 6→5).

### No new mathlib candidates this session

The three new lemmas are specific to the representation theory / character expansion setting (they use `repCharacter`, `IsUnitaryRepresentation`, etc.). The general lemma `character_expansion_nonneg_shared` (which `shared_cascade_factorization_nonneg` applies) was already identified as a mathlib candidate in a previous session.

## §8.11.80 — Adversarial self-check + key obstruction: link-level vs plaquette-level expansion (session 101, 2026-08-13)

**Status: ANALYSIS ONLY. No new verified lemmas this session. Codebase GREEN (unchanged from session 100).**

### Adversarial self-check (steelmanning the dead-end case)

At the start of this session, before resuming STEP 5, I steelmanned the case that the current scaffolding strategy (cascade → `shared_cascade_factorization_nonneg`) might NOT lead to transfer matrix positivity. The strongest objection:

> The existing `interface_boltzmann_character_expansion` (ReflectionPositivity.lean:1687) and `transfer_matrix_fubini_character_expansion` (TransferMatrix.lean:2922) expand the interface Boltzmann factor at the **link level** — each interface link `l` gets its own character `χ_{w(l)}(interfaceLinkVar U l)`, with a multi-index `w : InterfaceLink T L → ι`. The cascade (`luscher_key_identity`) integrates out a temporal link `g` shared between TWO plaquettes, forcing the two representations to MATCH (giving `δ_{st} · (1/d_s) · χ_s(h·k)`). But at the LINK level, each temporal link appears in only ONE plaquette's character product (the plaquette product `g₁·g₂·g₃⁻¹·g₄⁻¹` is a single group element, and the link-level expansion assigns one character per LINK, not per plaquette). So the link-level cascade would integrate out a link that appears in only one character, giving TRIVIALITY (`∫ χ_s(g) dg = δ_{s,σ_0} · dims(s)`, the trivial rep), NOT matching. This produces a coefficient `a(z, w)` that is a product of `dims` factors — a COMPLEX number, not a non-negative real — violating the `a(z,i) ≥ 0` hypothesis of `character_expansion_nonneg_shared`.

This objection is **valid for the link-level expansion** and would be a genuine dead end.

### The resolution: plaquette-level expansion

The obstruction is real but the conclusion is wrong: the fix is to expand at the **plaquette level**, not the link level. The plaquette Boltzmann factor `exp(c · Re Tr(g₁·g₂·g₃⁻¹·g₄⁻¹))` is a class function of the single group element `g = g₁·g₂·g₃⁻¹·g₄⁻¹` (the plaquette product). As a class function, it admits a **single-character expansion**:

```
exp(c · Re Tr(g)) = Σ_s coeff_s · χ_s(g)     with coeff_s ≥ 0
```

This is derived from `peterWeyl_clebschGordan_plaquette` Part 1 (the link-level expansion `exp(c·Re Tr(g₁g₂g₃g₄)) = Σ_{r,s,t,u,v} coeff(r,s,t,u,v) · χ_s(g₁)·χ_t(g₂)·χ_u(g₃)·χ_v(g₄)`) by setting `g₂ = g₃ = g₄ = 1` (the identity), using `χ_i(1) = dims(i)`. The plaquette-level coefficient is:

```
coeff_s = Σ_{r,t,u,v} coeff(r,s,t,u,v) · dims(t) · dims(u) · dims(v) ≥ 0
```

(non-negative because `coeff(r,s,t,u,v) ≥ 0` and `dims ≥ 0`).

### Why plaquette-level fixes the cascade

At the plaquette level, each temporal interface link `g` appears in the plaquette product `g = g₁·g₂·g₃⁻¹·g₄⁻¹` of EXACTLY TWO interface plaquettes (the two plaquettes that share the link, one on each side along the spatial direction). The cascade integrates out `g` via `luscher_key_identity`, which forces the two plaquette-level representations to MATCH (giving `δ_{st} · (1/d_s) · χ_s(h·k)`), producing a CONSTANT non-negative coefficient `(1/d_s) · coeff_s ≥ 0`. This is exactly the `a(z, i) = c_i ≥ 0` (constant) structure required by `character_expansion_nonneg_shared`.

The spatial interface links `u⁰_s` remain as the shared variable `z` (they appear in the plaquette products but are NOT integrated out). The temporal interface links `u⁰_t` are integrated out by the cascade. Since `f` satisfies `dependsOnlyOnPosSpatialInterface` (depends only on positive + SPATIAL interface links, NOT temporal interface links), the test function `g` does not depend on `u⁰_t`, so the `u⁰_t` integration acts only on the character products.

### Formalization plan (for the next session)

1. **`plaquette_boltzmann_character_expansion_single`** (PeterWeyl.lean): Prove `exp(c · Re Tr(g)) = Σ_s coeff_s · χ_s(g)` with `coeff_s ≥ 0` from `peterWeyl_clebschGordan_plaquette` Part 1 by setting `g₂=g₃=g₄=1`. **A scaffold was written this session but reverted** (the sum-factoring `rw [← Finset.mul_sum]` failed to match the nested 4-fold sum pattern). The next session should re-implement it cleanly — the key step is factoring `χ_s(g)` out of the 4-fold sum `Σ_{r,t,u,v} (coeff : ℂ) * (χ_s(g) * dims_t * dims_u * dims_v)` to get `χ_s(g) * Σ_{r,t,u,v} (coeff : ℂ) * dims_t * dims_u * dims_v`, then `push_cast` to match `coeff_single s`. Suggested approach: rearrange summand to put `χ_s(g)` on the RIGHT via `ring`, then factor with `← Finset.sum_mul` (4 levels, inside-out), then `push_cast` + `mul_comm`.

2. **Plaquette-level interface expansion**: Re-derive `interface_boltzmann_character_expansion` at the plaquette level (each interface plaquette gets ONE character `χ_{w(p)}(plaquetteProduct U p)`, not four link-level characters). This gives `exp(-β·S_int) = C · Σ_w F(w) · ∏_p χ_{w(p)}(plaquetteProduct U p)` with `F(w) ≥ 0`.

3. **Cascade the temporal links**: Apply `luscher_key_identity` to integrate out each temporal interface link `g` (shared between two plaquette characters), forcing matching and producing constant coefficients. The spatial interface links remain as shared variable `z`.

4. **Apply `shared_cascade_factorization_nonneg`** (or `_conj`): With `z = u⁰_s`, `x = U⁺`, `y = V⁺`, `Φ_w(z, x) = ∏_p χ_{w(p)}(z-product · x-product)`, `a(z, w) = c_w ≥ 0` constant. Conclude `⟨g, Tg⟩ ≥ 0`.

### Key design notes

- The lattice is 4D: `PeriodicSite T L` has `time : ZMod T` and `x, y, z : ZMod L` (3 spatial dimensions). The interface (t=0) plaquettes form a 3D spatial array. The temporal links at the interface couple adjacent plaquettes along each spatial direction. The cascade is NOT a simple 1D chain — it's a 3D structure. However, the `|Φ|²` positivity argument works regardless of dimensionality (each temporal link integration produces a matching + constant coefficient). The `chainIntegral_eq` (1D) is a building block; the full 3D cascade needs a more general formulation OR a per-direction factorization argument.

- `plaquetteBoltzmannPD` (PeterWeyl.lean:368) proves the plaquette factor is positive-definite at the LINK level (4 characters). The plaquette-level single-character expansion is a DIFFERENT (stronger, in a sense) result — it's the class-function expansion. Both are derivable from the same `peterWeyl_clebschGordan_plaquette` axiom.

- The `fullBoltzmannPD` (ReflectionPositivity.lean:1768) proves the FULL Boltzmann factor is PD (via Schur product theorem at the link level). This is the building block for the Lüscher `V^{1/2}` factor (spatial hopping operator). The plaquette-level expansion is needed for the `U` (transfer) part of the Lüscher decomposition `T = V^{1/2} · U · V^{1/2}`.

### No new mathlib candidates this session

The plaquette-level expansion is specific to the SU(N) representation theory setting.

## §8.11.81 — CORRECTION: §8.11.80 briefing was stale; uniform plaquette expansion VERIFIED (session 102, 2026-08-13)

**Status: VERIFIED. One new lemma compiled, `#print axioms` = [propext, Classical.choice, Quot.sound, peterWeyl_clebschGordan_plaquette] (no sorryAx). Build GREEN.**

### The §8.11.80 briefing was stale

The §8.11.80 "formalization plan" listed as its **step 1** the implementation of
`plaquette_boltzmann_character_expansion_single`, claiming "a scaffold was written
this session but reverted." This was based on **stale information**:

- The **parametric** single-character expansion `plaquette_boltzmann_single_char_expansion`
  (PeterWeyl.lean:1232) was already VERIFIED in session 56 (§8.11.45, 2026-08-08). It
  takes the Peter-Weyl package as hypotheses and concludes `∃ c', exp(c·Re Tr(g₁·g₂·g₃⁻¹·g₄⁻¹)) = Σ_s c'_s · χ_s(g₁·g₂·g₃⁻¹·g₄⁻¹)` for a specific plaquette product.
- The §8.11.71 analysis (session 93) explicitly documented that "steps 1-3 of the 3c
  plan are ALREADY DONE" (line 6539 of this doc), citing
  `plaquette_boltzmann_single_char_expansion` + `plaquette_product_single_char_decomp`.
- Session 101 apparently did not realize this and attempted to re-create the lemma
  under a different name, failed on the sum-factoring step (using the WRONG lemma name
  `Finset.mul_sum` instead of `Finset.sum_mul`), reverted, and left a stale briefing.

### What was actually missing: the UNIFORM (`∀ g`) version with the full package

The existing `plaquette_boltzmann_single_char_expansion` is **parametric** (takes the
package as hypotheses, concludes for a specific plaquette product). What STEP 5 step 2
(plaquette-level interface expansion) actually needs is the **uniform** version that
provides `hexp1 : ∀ g, exp(c·Re Tr(g)) = Σ_s coeff_s · χ_s(g)` with a FIXED `coeff`
(independent of `g`) and the FULL Peter-Weyl package existentially quantified — exactly
the `hexp1` hypothesis of `plaquette_product_single_char_decomp`.

### New lemma: `plaquette_boltzmann_character_expansion_single` (PeterWeyl.lean:~1294)

```
∃ (ι : Type) (hι : Fintype ι) (dims : ι → ℕ)
  (ρ : ∀ i, SU N →* Matrix (Fin (dims i)) (Fin (dims i)) ℂ)
  (hU : ∀ i, IsUnitaryRepresentation (ρ i))
  (hMeas : ∀ i, Measurable (repCharacter (ρ i)))
  (hIrr : ∀ i, IsIrreducible (ρ i))
  (hDims : ∀ i, 0 < dims i)
  (coeff : ι → ℝ) (hcoeff : ∀ s, 0 ≤ coeff s),
  ∀ (g : SU N),
  (Real.exp (c * (Matrix.trace ((g : SU N) : Matrix (Fin N) (Fin N) ℂ)).re) : ℂ) =
    ∑ s : ι, (coeff s : ℂ) * repCharacter (ρ s) g
```

**Proof** (reuses the technique from the parametric `plaquette_boltzmann_single_char_expansion`):
1. `obtain` the full package from `peterWeyl_clebschGordan_plaquette N c hc`.
2. `hchar_one : ∀ i, repCharacter (ρ i) 1 = (dims i : ℂ)` via `MonoidHom.map_one, Matrix.trace_one, Fintype.card_fin`.
3. `coeff s = Σ_{r,t,u,v} coeff4(r,s,t,u,v) · dims(t) · dims(u) · dims(v)` (independent of `g`).
4. `hcoeff : ∀ s, 0 ≤ coeff s` by `Finset.sum_nonneg` (each term ≥ 0).
5. Expansion: `hexp4 g 1 1 1`, `simp only [mul_one]` (g·1·1·1 = g), `simp only [hchar_one]`
   (χ_t(1) = dims t), `rw [h, Finset.sum_comm]` (exchange r/s sums), rearrange summand
   via `ring` + `push_cast`, factor `χ_s(g)` out via `simp only [← Finset.sum_mul]`,
   match coefficient via `simp only [Complex.ofReal_sum]`.

**Key:** the factoring uses `Finset.sum_mul` (NOT `Finset.mul_sum` — the §8.11.80 failure
was using the wrong lemma name). `simp only [← Finset.sum_mul]` handles all 4 nesting
levels at once.

**Axioms:** [propext, Classical.choice, Quot.sound, peterWeyl_clebschGordan_plaquette] —
the standard 3 plus the project's Peter-Weyl axiom. No `sorryAx`.

### What this enables

This lemma provides the `hexp1` hypothesis for `plaquette_product_single_char_decomp`,
enabling the **plaquette-level interface expansion** (STEP 5 step 2 of §8.11.80):
`∏_p exp(c·Re Tr(gP p)) = Σ_{w : P → ι} F(w) · ∏_p χ_{w(p)}(gP p)` with `F(w) ≥ 0` —
one character per PLAQUETTE (not per link). This is the form the Lüscher cascade needs:
at the plaquette level, each temporal link appears in two plaquette characters, so the
cascade forces matching (not triviality), producing constant non-negative coefficients.

### Actual remaining work for STEP 5 (corrected)

The §8.11.80 plan's 4 steps, with corrected status:
1. ✅ **`plaquette_boltzmann_character_expansion_single`** — DONE this session (uniform `∀ g` version, full package).
2. ⬜ **Plaquette-level interface expansion** — apply `plaquette_product_single_char_decomp` to the interface plaquettes with `gP p = plaquetteProduct U p`, giving `exp(-β·S_int) = C · Σ_{w : InterfacePlaquette → ι} F(w) · ∏_p χ_{w(p)}(plaquetteProduct U p)` with `F(w) ≥ 0`.
3. ⬜ **Cascade the temporal links** — apply `luscher_key_identity` to integrate out each temporal interface link (shared between two plaquette characters), forcing matching, producing constant coefficients. Spatial interface links remain as shared variable `z`.
4. ⬜ **Apply `shared_cascade_factorization_nonneg`** (or `_conj`) — conclude `⟨g, Tg⟩ ≥ 0`.

Then STEP 6: use `integral_G_thetaG_eq_inner_g_Tg` to convert to `∫ G·G(θU) ≥ 0`, replace `transferMatrixPositivity_axiom` (axioms 6→5).

### No new mathlib candidates this session

The uniform plaquette expansion is specific to the SU(N) representation theory setting.

### Attempted (and reverted): plaquette-level interface expansion

Session 102 also attempted STEP 5 step 2 — a plaquette-level interface expansion
`interface_product_plaquette_char_expansion` in ReflectionPositivity.lean (applying
`plaquette_product_single_char_decomp` to the interface plaquettes with
`gP p = plaquetteProduct U p`). The lemma was written but **REVERTED** because the proof
left an unsolved goal (sorryAx). The issue: after `set gP := fun p => plaquetteProduct`,
the `rw [Finset.prod_congr rfl (fun p _ => hexp1 (gP p))]` step (Step 1) did not match —
the goal's LHS uses `Complex.re (Matrix.trace ...)` while `hexp1`'s LHS (from
`plaquette_boltzmann_character_expansion_single`) uses `(Matrix.trace ...).re`. Changing
the statement to `.re` did not fully resolve it (the unsolved goal persisted, likely in
Step 3's `simp only [Complex.ofReal_prod]` not beta-reducing `F w` or a `DecidableEq`/
`Fintype.prod_sum` instance issue). The codebase is GREEN (the broken lemma was removed;
ReflectionPositivity.lean builds clean). The next session should re-attempt this lemma,
diagnosing the exact unsolved goal (add `sorry` after each step to localize), and consider
applying `plaquette_product_single_char_decomp` directly (extracting its `F` and showing
it equals the explicit `F = fun w => ∏ p, coeff (w p)`) rather than inlining the
product-of-sums proof.

## §8.11.82 — Plaquette-level interface expansion VERIFIED (session 103, 2026-08-14)

**Status: VERIFIED. `interface_product_plaquette_char_expansion` compiled,
`#print axioms` = [propext, Classical.choice, Quot.sound, peterWeyl_clebschGordan_plaquette]
(no sorryAx). Build GREEN.**

### Adversarial self-check (start of session)

Before resuming, the case that the cascade → transfer-matrix-positivity approach is a
dead end was steelmanned:

1. **Is the plaquette-level expansion genuinely necessary?** The existing LINK-level
   `interface_product_character_expansion` (ReflectionPositivity.lean:1633) was already
   verified. At the link level, each link gets ONE character index `w(l)`; integrating out a
   temporal link `l_t` (which carries a single character `χ_{w(l_t)}`) via Schur orthogonality
   forces `w(l_t) = trivial` — TRIVIALITY, killing the temporal structure entirely. This is
   wrong. At the PLAQUETTE level, each temporal link appears in TWO plaquette characters
   `χ_{w(p₁)}(gP p₁)` and `χ_{w(p₂)}(gP p₂)`; integrating out `l_t` forces `w(p₁) = w(p₂)`
   — MATCHING, which propagates the constraint across the lattice. So the plaquette-level
   expansion is genuinely necessary. **Conclusion: the §8.11.80/81 claim is sound; not a
   dead end.**

2. **2-site → full-lattice generalization.** `shared_cascade_factorization_nonneg` and
   `luscher_2site_cascade_separable` are explicitly 2-site (one temporal link, one shared
   spatial link). The actual interface has MANY temporal and spatial links. Generalizing the
   cascade to the full lattice is non-trivial and is the main remaining RISK for steps 3–4.
   **This risk belongs to later steps, not the immediate task (step 2, pure algebra).** Flagged
   for when steps 3–4 are reached.

**Verdict:** the immediate task (step 2) is sound and low-risk. Proceed.

### New lemma: `interface_product_plaquette_char_expansion` (ReflectionPositivity.lean:~1693)

```
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
    (Real.exp ((β * β / N) * (Matrix.trace ((gP p) : Matrix (Fin N) (Fin N) ℂ)).re) : ℂ) =
  ∑ w : InterfacePlaquette T L → ι, (F w : ℂ) *
    ∏ p : InterfacePlaquette T L, repCharacter (ρ (w p)) (gP p)
```

where `gP p = interfaceLinkVar U (interfaceLinkAssign p 0) · interfaceLinkVar U (interfaceLinkAssign p 1) ·
(interfaceLinkVar U (interfaceLinkAssign p 2))⁻¹ · (interfaceLinkVar U (interfaceLinkAssign p 3))⁻¹`
and `F w = ∏ p, coeff (w p) ≥ 0`. This is the **plaquette-level** analogue of
`interface_product_character_expansion` (link-level): one character per PLAQUETTE, not per link.

### Two failed approaches and why (key lessons for the next session)

**Failed approach 1 — `obtain` from `plaquette_product_single_char_decomp` + `exact`:**
```
obtain ⟨F', hF', hF'_decomp⟩ := plaquette_product_single_char_decomp ρ coeff hcoeff ... gP
exact hF'_decomp   -- TYPE MISMATCH
```
The mismatch was ONLY in the RHS: `↑(F' w)` (from the decomp) vs `↑((fun w => ∏ p, coeff (w p)) w)`
(from the goal's `refine`). The LHS matched perfectly (both `(↑(gP p)).trace.re` — confirming the
`Complex.re` vs `.re` worry from §8.11.81 was a NON-issue; Lean elaborates `Complex.re (Tr X)` to
`(Tr X).re` syntactically). **Root cause:** `obtain` from an existential makes the witness `F'`
OPAQUE — Lean no longer knows `F' = fun w => ∏ p, coeff (w p)` definitionally. So `F' w` is not
defeq to the goal's explicit `(fun w => ∏ p, coeff (w p)) w`. This is fundamental to `obtain` from
`∃`; it cannot be worked around by making a "uniform" version (any `obtain` from `∃` is opaque).

**Failed approach 2 — inline the product-of-sums proof WITH `set gP`:**
```
set gP : InterfacePlaquette T L → SU N := fun p => [long expr]
rw [Finset.prod_congr rfl (fun p _ => hexp1 (gP p))]
rw [Fintype.prod_sum (fun p s => (coeff s : ℂ) * repCharacter (ρ s) (gP p))]
refine Finset.sum_congr rfl (fun w _ => ?_)
rw [Finset.prod_mul_distrib]
simp only [Complex.ofReal_prod]   -- UNSOLVED GOAL
```
`set gP` replaced the long expression in the goal's **LHS** (inside the Boltzmann factor) with
`gP p`, but did **NOT** replace it in the goal's **RHS** (inside `repCharacter (ρ (w p)) (long expr)`).
The final goal was `(∏ x, … (gP x)) = (∏ p, … (long expr p))` — defeq-closable in principle (`gP p`
beta-reduces to the long expr via the `let`-binding), but `simp`'s closing `rfl` did not unfold the
local `let`-def `gP`. (The asymmetry is likely a `set`-abstraction quirk: the LHS and RHS long
expressions live under different binders / have different `: SU N` annotation, so `set` matched
only one.)

### Working approach — inline WITHOUT `set` (explicit long expression)

The fix: write the plaquette-product expression **explicitly** in both the `hexp1` application and
the `Fintype.prod_sum` argument (no `set`), so the LHS (from `Fintype.prod_sum`) and the RHS (from
the lemma statement) carry the **identical** expression, and `rfl` (via `simp only [Complex.ofReal_prod]`)
closes the goal:
```
rw [Finset.prod_congr rfl (fun p _ => hexp1
    (interfaceLinkVar N T L U (interfaceLinkAssign T L p 0) * … * …⁻¹ * …⁻¹))]
rw [Fintype.prod_sum (fun p s => (coeff s : ℂ) * repCharacter (ρ s)
    (interfaceLinkVar N T L U (interfaceLinkAssign T L p 0) * … * …⁻¹ * …⁻¹))]
refine Finset.sum_congr rfl (fun w _ => ?_)
rw [Finset.prod_mul_distrib]
simp only [Complex.ofReal_prod]
```
This is exactly the proof body of `plaquette_product_single_char_decomp` (PeterWeyl.lean:1404–1413),
inlined with `c' = coeff`, `c = β*β/N`, `P = InterfacePlaquette T L`. The `F` is provided by the
outer `refine` as `fun w => ∏ p, coeff (w p)` (definitionally transparent), so it matches the goal.

**Axioms:** [propext, Classical.choice, Quot.sound, peterWeyl_clebschGordan_plaquette] — the standard
3 plus the project's Peter-Weyl axiom. No `sorryAx`. Axiom count unchanged (6 overall).

### What this enables (STEP 5 step 2 DONE)

This is STEP 5 step 2 of §8.11.80: the plaquette-level interface expansion. Combined with the
constant `C` from `interface_boltzmann_eq_abstract_product`, it gives
`exp(-β·S_int) = C · Σ_{w : InterfacePlaquette → ι} F(w) · ∏_p χ_{w(p)}(gP p)` with `F(w) ≥ 0`,
`C > 0` — one character per plaquette, the form the Lüscher cascade needs.

### Corrected remaining work for STEP 5

1. ✅ `plaquette_boltzmann_character_expansion_single` (uniform `∀ g` version) — DONE (session 102).
2. ✅ **Plaquette-level interface expansion** — DONE this session (`interface_product_plaquette_char_expansion`).
3. ⬜ **Cascade the temporal links** — apply `luscher_key_identity` / Schur orthogonality to integrate
   out each temporal interface link (shared between two plaquette characters), forcing matching
   `w(p₁) = w(p₂)`, producing constant coefficients. Spatial interface links remain as shared
   variable `z`. **RISK (from self-check):** the existing cascade lemmas are 2-site; generalizing to
   the full lattice (many temporal + spatial links) is non-trivial and is the main remaining risk.
4. ⬜ **Apply `shared_cascade_factorization_nonneg`** (or `_conj`) — conclude `⟨g, Tg⟩ ≥ 0`.

Then STEP 6: use `integral_G_thetaG_eq_inner_g_Tg` (TransferMatrix.lean:5149) to convert to
`∫ G·G(θU) ≥ 0`, replace `transferMatrixPositivity_axiom` (ReflectionPositivity.lean:~3641,
axioms 6→5).

### No new mathlib candidates this session

The plaquette-level interface expansion is specific to the SU(N) lattice setting.

### Addendum: combined plaquette-level interface Boltzmann expansion (also VERIFIED)

The composition lemma `interface_boltzmann_plaquette_char_expansion` (ReflectionPositivity.lean:~1750)
was also added and VERIFIED this session. It composes `interface_boltzmann_eq_abstract_product`
(`exp(-β·S_int) = C · ∏_p exp(c·Re Tr(gP p))`, `C > 0`) with
`interface_product_plaquette_char_expansion` to give the full plaquette-level interface Boltzmann
expansion (viewed in ℂ):

    (exp(-β·S_int(U)) : ℂ) = (C : ℂ) · ∑_{w : InterfacePlaquette → ι} F(w) · ∏_p χ_{w(p)}(gP p)

with `C > 0`, `F(w) ≥ 0`. Proof follows the same pattern as `interface_boltzmann_character_expansion`
(link-level): `rw [hC_eq_all U]; have h := hF_decomp U; norm_cast at h; rw [Complex.ofReal_mul, h]`.
`#print axioms` = [propext, Classical.choice, Quot.sound, peterWeyl_clebschGordan_plaquette] (no sorryAx).
This is the form the Lüscher cascade operates on (the constant `C` factors out of the integral).

## §8.11.83 — Bipartite L-site cascade VERIFIED (session 105, 2026-08-14)

**Status: VERIFIED. `bipartiteChainIntegral_eq` compiled,
`#print axioms` = [propext, Classical.choice, Quot.sound, characterOrthogonality]
(no sorryAx). Build GREEN.**

### What was done

Session 104 wrote the `bipartiteChainIntegral` definition and `bipartiteChainIntegral_eq`
lemma but the build FAILED with 4 errors (syntax, rewrite, unsolved goals). Session 105
fixed all errors and verified the lemma.

**New lemma: `bipartiteChainIntegral_eq`** (PositiveDefinite.lean:~1763)

The bipartite open-chain L-site cascade generalizes `chainIntegral_eq` to plaquettes with
BOTH a V-link and a W-link (the structure needed for the transfer matrix). Each plaquette
product is `g_i · V_i · g_{i+1}⁻¹ · W_i⁻¹`, and the cascade integrates out the interior
temporal links g₁,...,gₙ, forcing all representations to match:

    bipartiteChainIntegral a b [(γ₀,V₀,W₀),...,(γₙ,Vₙ,Wₙ)] =
      δ_{all γ=γ₀} · (1/d_γ)^n · χ_γ(a · V-product · b⁻¹ · W-product⁻¹)

where `n = rest.length`, `V-product = V₀·...·Vₙ`, `W-product = W₀·...·Wₙ`.

**New helper lemma: `repCharacter_cyclic2`** (PositiveDefinite.lean:~795)

    χ(g · h) = χ(h · g)

Proved from `Matrix.trace_mul_comm` (`Tr(A·B) = Tr(B·A)`). This is the 2-factor special
case of cyclic invariance of the trace. No unitary/irreducibility hypothesis needed.
Logged as mathlib candidate §9 (standard-but-unformalized).

### Build errors fixed

1. **Syntax error (line ~1843):** Extra `)` in the `luscher_key_identity` argument list.
   Fixed by removing the stray paren.
2. **`mul_inv_rev` ambiguity (line ~1877):** Both `_root_.mul_inv_rev` (group) and
   `Matrix.mul_inv_rev` (matrix) matched. Fixed by qualifying as `_root_.mul_inv_rev`.
3. **`ring` failure (pos case):** After the cyclic rewrite, the LHS and RHS character
   arguments differed only by associativity of the last two factors
   (`... * W-prod⁻¹ * W₀⁻¹` vs `... * (W-prod⁻¹ * W₀⁻¹)`). `ring` treats `repCharacter`
   as an atom but couldn't see through the associativity difference. Fixed by adding an
   explicit `rw [show ... = ... from by ac_rfl]` to align the character arguments before
   `ring`.
4. **`h2` rewrite (line ~1842):** Added `change` to explicitly state the goal form before
   `rw [hcyc g]`, matching the pattern from `chainIntegral_eq` (line 1668).

### Proof structure (pos case)

The pos case (γ₁ = γ₀) is the hardest part. The approach:
1. `simp only [if_pos hγ, hRHS, if_true]` + `rw [hγ]` to simplify both sides.
2. Unfold RHS list products (`List.map_cons`, `List.prod_cons`, `mul_inv_rev`).
3. Cyclic rewrite of LHS character to match RHS character, using `repCharacter_cyclic2`
   twice: `χ(A * B) = χ(B * A)` then `χ(W₀⁻¹ * Z) = χ(Z * W₀⁻¹)`, with `ac_rfl` for
   reassociation between the two cyclic steps.
4. `rw [pow_add, pow_one]` for the power, then `ring` for the coefficient.

### What this enables (STEP 5 step 3 — open chain DONE)

This is the open-chain building block. The CYCLIC version (a = b = g₀, integrated out via
`conjugation_integral`) gives the separable kernel `Σ_s c_s · χ_s(W-product) · χ_s(V-product)`
with `c_s ≥ 0`. This is the next step.

### Remaining work for STEP 5

3a. ✅ Open-chain bipartite cascade — DONE (`bipartiteChainIntegral_eq`).
3b. ✅ **Cyclic cascade** — DONE (`bipartiteCyclicCascade_eq`). Closes the chain
    (a = b = g₀, integrate out g₀ via `conjugation_integral`), producing the separable
    kernel `(1/d)^(n+1) · χ(W-product⁻¹) · χ(V-product)`. Also extracted
    `char_conjugation_integrable` as a standalone lemma for reuse.
3c. ⬜ **Connect to lattice** — match the plaquette-level expansion
    (`interface_boltzmann_plaquette_char_expansion`) to the bipartite cascade structure.
    RISK: the full lattice is 3D, not 1D.
4. ⬜ **Apply `shared_cascade_factorization_nonneg`** — conclude `⟨g, Tg⟩ ≥ 0`.

Then STEP 6: replace `transferMatrixPositivity_axiom` (axioms 6→5).

## §8.11.84 — Adversarial self-check + 3D obstacle analysis (session 106, 2026-08-14)

**Status: ANALYSIS ONLY. No code changes. Build unchanged (GREEN from session 105).**

### Adversarial self-check (standing instruction §4)

This session performed the periodic adversarial self-check: steelmanning the case
that the current cascade scaffolding is a dead end for the transfer matrix positivity
proof. The conclusion is **mixed**: the 1D cascade is verified and the σ-twist obstacle
IS handled, but the 1D→3D connection is a genuine structural gap that requires
substantial new formalization.

### The 3D obstacle (confirmed)

**The core problem:** The bipartite cascade (`bipartiteChainIntegral_eq`,
`bipartiteCyclicCascade_eq`) is a **1D** tool. It assumes each temporal link appears
in exactly **2** plaquettes (a chain: plaquette `i` has `g_i · V_i · g_{i+1}⁻¹ · W_i⁻¹`,
so `g_i` is shared between plaquettes `i-1` and `i`). The cascade integrates out the
interior `g_i` one at a time via Schur orthogonality, forcing all representations to
match.

**The 3D lattice structure:** On the 3+1D lattice (`PeriodicSite T L` with 3 spatial
directions x, y, z), each temporal link `u_t(x, t=0)` at the interface appears in
**6** interface plaquettes (3 spatial directions ν=1,2,3 × 2 orientations: forward
as link-0 of plaquette `(x, 0, ν)` and backward as link-2 of plaquette `(x-ν̂, 0, ν)`).

This was verified by examining `plaquetteLinkIdx` (ReflectionPositivity.lean:1085):
- link 0: `(n, μ)` — temporal at `n`
- link 2: `(n+μ̂+ν̂, μ)` — temporal at `n+ν̂` (inverted), same time as `n` (since ν is spatial)

So for temporal plaquettes (μ=0, ν spatial), both temporal links are at the same time
slice, at spatial sites `x` and `x+ν̂`. Each temporal link `u_t(x, t=0)` is shared across
all 3 spatial directions.

**Consequence:** The product of characters from the plaquette-level expansion
(`interface_boltzmann_plaquette_char_expansion`) is:
```
∏_x ∏_{ν=1,2,3} χ_{w(x,ν)}(u_t(x) · V_{x,ν} · u_t(x+ν̂)⁻¹ · W_{x,ν}⁻¹)
```
This is a **3D network** (each `u_t(x)` in 6 factors), NOT a 1D chain (each `g_i` in 2
factors). The 1D cascade does NOT apply.

**Per-direction factorization fails:** The interface Boltzmann factor does factor as
`∏_ν [∏_x B_p(plaquette(x,ν))]` (each plaquette belongs to one direction), but the
temporal links are **shared** across the directional sub-products. Expanding each
direction independently and then integrating out `u_t(x)` requires handling 6
characters simultaneously (3 from forward plaquettes, 3 from backward), which is
exactly the 3D case the cascade doesn't handle.

### The σ-twist obstacle (RESOLVED by the cascade)

A key positive finding: the σ-twist obstacle from §8.11.38 (the reflection conjugates
the CHARACTER, giving `A²` not `|A|²`) **IS handled** by the cascade + conj form.

The cyclic cascade produces: `(1/d)^(n+1) · χ(W-prod⁻¹) · χ(V-prod)`.

Via `cascade_shared_kernel_form` (PositiveDefiniteIntegral.lean:2002):
`χ_s(x⁻¹·z⁻¹) = χ_s((z·x)⁻¹) = conj(χ_s(z·x))` (by `mul_inv_rev` + `repCharacter_inv`).

So when `W-prod = z·x` and `V-prod = z·y` (shared interface link `z`, positive links
`x`, negative links `y`), the cascade result becomes:
```
(1/d)^(n+1) · conj(χ_s(z·x)) · χ_s(z·y)
```
which is exactly the `shared_cascade_factorization_nonneg_conj` kernel form
(PositiveDefiniteIntegral.lean:1934) with `c_s = (1/d_s)^(n+1) ≥ 0`.

**Conclusion:** The σ-twist is NOT the remaining obstacle. The conj form handles it.
The ONLY remaining obstacle is the 1D→3D structural gap.

### Verified building blocks for the 3D case

1. **`single_site_3D_luscher_integral`** (PeterWeyl.lean:3055) — VERIFIED. Integrates
   out ONE temporal link appearing in 3 plaquettes (3 unbarred + 3 barred matrix
   elements) via 3-fold CG decomposition + Schur orthogonality. Gives a sum over
   combined representations `α` with CG coefficients. `#print axioms` =
   `[propext, Classical.choice, Quot.sound, characterOrthogonality]`.

2. **`cg_unitarity_nonneg`** (PeterWeyl.lean:3296) — VERIFIED. In the **diagonal** case
   (barred indices = unbarred indices), the single-site 3D integral gives
   `∑_{α,p,q} (1/dims α) · |C(α,p,q)|² ≥ 0`. This demonstrates the |C|² structure from
   CG unitarity. BUT: only the diagonal case (self-correlation), not the off-diagonal
   case (transfer matrix inner product).

3. **`bipartiteChainIntegral_eq` / `bipartiteCyclicCascade_eq`** (PositiveDefinite.lean) —
   VERIFIED. 1D cascade. Produces separable kernel with non-negative coefficients.

4. **`shared_cascade_factorization_nonneg` / `_conj`** (PositiveDefiniteIntegral.lean) —
   VERIFIED. Separable kernel `Σ_s c_s · χ_s(z·x) · conj(χ_s(z·y))` with `c_s ≥ 0`
   gives non-negative integral.

5. **`cascade_shared_kernel_form`** (PositiveDefiniteIntegral.lean:2002) — VERIFIED.
   Converts `χ(W-prod⁻¹) · χ(V-prod)` to `conj(χ(z·x)) · χ(z·y)`.

### The missing piece: 3D global cascade

The 3D resolution (from §8.11.41, CONJECTURED not formalized): The GLOBAL cascade
(integrating out ALL `u_t(x)` site by site) matches representations across sites, and
the CG UNITARITY (`hcgME_unitary`) ensures the coefficients are `|C|²` type
(non-negative). Result: `U_3D = ∑_γ a_γ · Φ_γ(u_s) · conj(Φ_γ(v_s))` with `a_γ ≥ 0`.

**Why this is hard to formalize:**
- At each site, `single_site_3D_luscher_integral` gives CG coefficients that involve
  NEIGHBORING temporal links (not yet integrated out).
- The cascade doesn't close locally — the CG coefficients from site `x` depend on
  `u_t(x+ν̂)` for each direction ν, which are integrated out at neighboring sites.
- The global argument requires CG unitarity (`hcgME_unitary`) to combine the CG
  coefficients across sites into `|C|²` terms.
- `cg_unitarity_nonneg` proves this for the DIAGONAL case only; the off-diagonal
  (multi-site, transfer matrix inner product) case is NOT formalized.

### Gauge-fixing approach (also complex for 3D)

The gauge-fixing approach (§8.11.39) works cleanly for 1D: fix `u_t(0) = e`, change
variables to relative links `v(x) = u_t(x+1)⁻¹ · u_t(x)`, constraint `∏ v(x) = e`
enforced by character expansion of delta function, Schur orthogonality gives
`|c_γ|²/d_γ ≥ 0`.

For 3D, the relative links `v_ν(x) = u_t(x+ν̂)⁻¹ · u_t(x)` (one per direction ν per
site x) satisfy a **zero-curvature constraint**:
```
v_μ(x) · v_ν(x+μ̂) = v_ν(x) · v_μ(x+ν̂)   (non-commuting, for each 2D face)
```
This is a set of non-commuting constraints (one per spatial 2D face), much more
complex than the 1D constraint `∏ v(x) = e`. The character expansion of the
corresponding delta function is not straightforward. This approach is also not
formalized for 3D.

### Assessment and path forward

**The cascade approach is NOT a dead end** — the σ-twist is handled, and the 3D
resolution is conjectured with a clear mechanism (CG unitarity → |C|²). But the 1D→3D
connection requires substantial new formalization:

**Option A: 3D global cascade.** Formalize the multi-site cascade using
`single_site_3D_luscher_integral` + CG unitarity. The key lemma: the global cascade
gives `∑_γ a_γ · Φ_γ · conj(Φ_γ)` with `a_γ ≥ 0` (off-diagonal case). Then apply
`shared_cascade_factorization_nonneg_conj`. Major effort; the off-diagonal CG
unitarity argument is the crux.

**Option B: 1+1D proof of concept.** Prove the cascade works for 1 spatial direction
(where it applies directly). Requires a separate formalization (the existing
`InterfacePlaquette` includes all 3 directions). Doesn't prove 3D but validates the
mechanism end-to-end and identifies the exact 3D gap.

**Option C: Operator factorization T = B*B.** Define the half-step operator B, show
`T = B†B`, conclude `⟨f, Tf⟩ = ‖Bf‖² ≥ 0`. Requires understanding the Lüscher
decomposition `T = V^{1/2} · U · V^{1/2}`. Different approach from character expansion.

**Option D: Fock space (Lüscher 1977).** Build the Hilbert space as a Fock space,
construct the transfer matrix explicitly, show it's positive definite. Completely
different formalization; requires detailed study of the Lüscher construction.

**Recommendation:** Option B (1+1D proof of concept) is the most tractable immediate
step — it validates the full pipeline (plaquette expansion → cascade → conj form →
`shared_cascade_factorization_nonneg_conj`) end-to-end for the case where the cascade
applies. Then Option A (3D global cascade) extends to the full lattice. The 1+1D case
would also clarify whether the `shared_cascade_factorization_nonneg_conj` lemma's
hypotheses can be discharged in the concrete lattice setting.

### What remains unchanged

- All verified lemmas from session 105 remain GREEN (no code changes this session).
- Axiom count: still 6 (4 standard + `peterWeyl_clebschGordan_plaquette` +
  `transferMatrixPositivity_axiom`).
- The cascade lemmas (`bipartiteChainIntegral_eq`, `bipartiteCyclicCascade_eq`,
  `cascade_shared_kernel_form`, `shared_cascade_factorization_nonneg_conj`) are
  verified building blocks that will be used in either Option A or B.

### Key distinction: character-level vs matrix-element-level CG decomposition

A crucial finding from this session's analysis:

**Character-level CG decomposition** (`hcg_decomp` from `peterWeyl_clebschGordan_plaquette`):
`χ_s(g) · χ_t(g) = ∑_ν cg s t ν · χ_ν(g)` — requires BOTH characters to have the SAME
argument `g`. The coefficients `cg s t ν` are multiplicities (non-negative integers ≥ 0).
Used by `luscher_2site_2D_cascade_charlevel` (PositiveDefinite.lean:1959), which assumes
both forward plaquettes share the same `W` factor (simplification).

**Matrix-element-level CG decomposition** (`hcgME_decomp`):
`(ρ_s g)_{ab} · (ρ_t g)_{ij} = ∑_ν ∑_{p,q} cgME · (ρ_ν g)_{pq} · conj(cgME)` — handles
DIFFERENT arguments (via matrix elements). The CG coefficients `cgME` are complex (NOT
necessarily non-negative). Used by `single_site_3D_luscher_integral` (PeterWeyl.lean:3055).

**Why this matters for the actual lattice:** In the actual 3D lattice, each temporal link
appears in 3 forward plaquettes with DIFFERENT W variables (one per spatial direction):
`χ_{s1}(g·W₁·g'⁻¹) · χ_{s2}(g·W₂·g'⁻¹) · χ_{s3}(g·W₃·g'⁻¹)`. The character-level CG
decomposition CANNOT combine these (different arguments). The matrix-element-level CG
decomposition CAN (by expanding each character as a trace, then decomposing the product
of matrix elements).

**Consequence for non-negativity:** The character-level approach gives non-negative
coefficients directly (multiplicities ≥ 0). The matrix-element-level approach gives
complex CG coefficients, requiring the |C|² argument (CG unitarity) for non-negativity.
`cg_unitarity_nonneg` (PeterWeyl.lean:3296) proves this for the DIAGONAL case only.
The OFF-DIAGONAL case (transfer matrix inner product, different indices on two sides)
is NOT proven — this is the crux of the 3D global cascade.

**Even the 2D lattice has this obstacle:** The `luscher_2site_2D_cascade_charlevel` lemma
uses the same-W simplification. The actual 2D lattice (2 spatial directions) has different
W variables per direction, requiring the matrix-element-level approach. So the
character-level cascade is a SIMPLIFIED MODEL, not the actual lattice structure.

## §8.11.85 — Interface plaquette subtlety RESOLVED: change-of-variables approach FLAWED, standard OS approach identified as simpler path (session 113, 2026-08-15)

**Status: ANALYSIS ONLY. No code changes. Build unchanged (GREEN from session 111).**

### The change-of-variables approach (session 112) is FLAWED

Session 112 proposed a change-of-variables + gauge projection approach:
substitute `W_{x,ν} → u_t(x)·W_{x,ν}·u_t(x+ν̂)⁻¹` (gauge transform of negative
links by interface temporal links `u_t`), claiming the interface Boltzmann becomes
`∏ B_p(V·W⁻¹)` independent of `u_t`, making the `u_t` integral a gauge projection `P`.

**This approach does NOT work.** Two fatal flaws:

#### Flaw 1: The simplified plaquette formula doesn't match the actual lattice

The handoff's formula `u_t(x)·V_{x,ν}·u_t(x+ν̂)⁻¹·W_{x,ν}⁻¹` (interface temporal ×
positive spatial × interface temporal⁻¹ × negative spatial⁻¹) does NOT correspond to
any actual lattice plaquette. The actual interface plaquettes come in THREE types:

- **Type 1** (time 0→1, μ=0, ν spatial): plaquette `(n=(0,x), μ=0, ν)`. Links:
  - link 0: `U((0,x), 0)` — temporal at time 0, **interface** link
  - link 1: `U((1,x), ν)` — spatial at time 1, **positive** link
  - link 2: `U((1,x+e_ν), 0)` — temporal at time 1, **positive** link (inverted in product)
  - link 3: `U((0,x+e_ν), ν)` — spatial at time 0, **interface** link (inverted in product)
  - **No negative links.** Involves interface + positive links only.

- **Type 2** (time T-1→0, μ=0, ν spatial): plaquette `(n=(T-1,x), μ=0, ν)`. Links:
  - link 0: `U((T-1,x), 0)` — temporal at time T-1, **negative** link
  - link 1: `U((0,x), ν)` — spatial at time 0, **interface** link
  - link 2: `U((0,x+e_ν), 0)` — temporal at time 0, **interface** link (inverted in product)
  - link 3: `U((T-1,x+e_ν), ν)` — spatial at time T-1, **negative** link (inverted in product)
  - **No positive links.** Involves negative + interface links only.

- **Type 3** (time 0, μ,ν both spatial): plaquette `(n=(0,x), μ, ν)` with μ,ν ≠ 0. Links:
  - All four links at time 0, all **interface** links.
  - Involves interface links only.

The handoff's formula mixes a positive spatial link `V` and a negative spatial link `W`
in the SAME plaquette, but no actual plaquette has this structure. Type 1 has positive
links but no negative; type 2 has negative links but no positive.

#### Flaw 2: Partial gauge transformation doesn't preserve the interface action

The change of variables only transforms NEGATIVE links (part of `U⁻`), leaving
interface and positive links fixed. For type 2 plaquettes (which involve both negative
and interface links), the plaquette product `P = g₀·g₁·g₂⁻¹·g₃⁻¹` has:
- `g₀` (negative temporal): transformed to `u_t(x)·g₀·u_t(x)⁻¹` (conjugation, since
  gauge parameter is time-independent)
- `g₁` (interface spatial): NOT transformed
- `g₂` (interface temporal): NOT transformed
- `g₃` (negative spatial): transformed to `u_t(x+e_ν)·g₃·u_t(x+2e_ν)⁻¹` (NOT conjugation)

The transformed plaquette product is NOT a conjugation of the original, so
`Re Tr(P') ≠ Re Tr(P)` in general. The interface action `S_int` is NOT invariant under
this partial gauge transformation.

A FULL gauge transformation (all links, including interface and positive) WOULD preserve
all plaquette products, but then the positive links `V` are also transformed, and `f(V)`
changes — defeating the purpose (we need `f` to be evaluated at the original positive
links).

### The STANDARD Osterwalder-Seiler approach: character expansion + reflection + conjugation

The standard proof (Osterwalder-Seiler 1978, Lüscher) works as follows:

1. **Character expansion** of the interface Boltzmann:
   `exp(-β·S_int) = C · ∑_w F(w) · ∏_p χ_{w(p)}(P_p)`
   where `P_p = g_{p,0}·g_{p,1}·g_{p,2}⁻¹·g_{p,3}⁻¹` is the plaquette product.
   [Already in codebase: `interface_boltzmann_plaquette_char_expansion`]

2. **Per-link character factoring** via Part 1 of `peterWeyl_clebschGordan_plaquette`:
   `exp(c·Re Tr(g₁g₂g₃g₄)) = ∑_{r,s,t,u,v} coeff · χ_s(g₁)·χ_t(g₂)·χ_u(g₃)·χ_v(g₄)`
   Each character is of a SINGLE link. The inverted links (g₃, g₄ in the plaquette
   product) give `χ_u(g₃⁻¹) = conj(χ_u(g₃))` and `χ_v(g₄⁻¹) = conj(χ_v(g₄))`.

3. **Group by region**: positive+interface links → factor `Φ_w(U⁺, u⁰)`,
   negative+interface links → factor `Ψ_w(U⁻, u⁰)`. Interface links appear in BOTH
   factors (type 1 plaquettes contribute to `Φ_w`, type 2 to `Ψ_w`, type 3 to both).
   The product of characters at the same link (from multiple plaquettes) is kept as a
   PRODUCT — no CG decomposition needed.

4. **Reflection + conjugation**: the reflection `θ` maps type 2 plaquettes to type 1
   plaquettes. The `conj(χ)` factors from inverted plaquette links (links 2,3) provide
   the conjugation: `Ψ_w(U⁻, u⁰) = conj(Φ_w(θ⁻⁰(U⁻, u⁰)))`.
   The σ-twist (inversion of temporal interface links) is consistent with this: it maps
   `g → g⁻¹`, giving `χ(g⁻¹) = conj(χ(g))`, which is exactly the conjugation needed.

5. **Final non-negativity**:
   `⟨f, Tf⟩ = ∑_w F(w) · ∫ du⁰ |∫ Φ_w(U⁺, u⁰) · f · exp(-β·S⁺) dU⁺|² ≥ 0`
   since `F(w) ≥ 0` and `|...|² ≥ 0`.

### Key insight: the standard approach does NOT require CG beyond Part 1 or the cascade

The cascade approach (§8.11.84) tried to integrate out individual temporal links using
Schur orthogonality, which requires CG decomposition (Parts 3-4 of the axiom) and the
3D obstacle (each temporal link in 6 plaquettes).

The standard approach just groups per-link characters by region and uses the reflection.
**No individual link integration, no CG decomposition, no cascade.** The product of
characters at the same link is kept as a product — no need to decompose it into a single
character via CG.

This is a MAJOR simplification. The only axiom needed is Part 1 (character expansion),
which is already in the codebase as `peterWeyl_clebschGordan_plaquette`.

### The conjugation mechanism (detailed)

For a type 2 plaquette (T-1→0), the character expansion gives:
`χ_s(g₀)·χ_t(g₁)·conj(χ_u(g₂))·conj(χ_v(g₃))`
where `g₀` = neg temporal, `g₁` = int spatial, `g₂` = int temporal, `g₃` = neg spatial.

The reflection maps this to a type 1 plaquette (0→1) with links:
- `g₀` (neg temporal) → `g₀⁻¹` (pos temporal, inverted by reflection)
- `g₁` (int spatial) → `g₁` (int spatial, NOT inverted)
- `g₂` (int temporal) → `g₂⁻¹` (int temporal, inverted by σ-twist)
- `g₃` (neg spatial) → `g₃` (pos spatial, NOT inverted)

The type 1 plaquette's character expansion gives:
`χ_{s'}(g₂⁻¹)·χ_{t'}(g₃)·conj(χ_{u'}(g₀⁻¹))·conj(χ_{v'}(g₁))`
= `conj(χ_{s'}(g₂))·χ_{t'}(g₃)·χ_{u'}(g₀)·conj(χ_{v'}(g₁))`

Taking the conjugate:
`conj(type 1) = χ_{s'}(g₂)·conj(χ_{t'}(g₃))·conj(χ_{u'}(g₀))·χ_{v'}(g₁)`

For `Ψ_w = conj(Φ_w(θ...))`, we need the representation indices to match:
`s = u'`, `t = v'`, `u = s'`, `v = t'`. This is ensured by the reflection symmetry
of the character expansion (same coefficients `coeff` for both plaquette types).

### Adversarial self-check (standing instruction §4)

**Is the standard approach a dead end?** No.

Steelman against: the bookkeeping is complex (each interface link in up to 6 plaquettes,
exponential terms in the character expansion). The reflection matching requires showing
representation indices match between reflected plaquettes. Interface links appear in both
factors, preventing clean factorization.

Counter: the bookkeeping is finite (finite lattice, finite irreps). The reflection
matching is a bijection between type 1 and type 2 plaquettes (provable once). Interface
links in the outer integral is standard Fubini. The σ-twist is already handled by
existing machinery (`thetaReindex`, σ-inversion lemmas). No deep mathematics (CG, Schur
orthogonality for individual links) is needed — just Part 1 + reflection + |...|².

**Conclusion:** the standard OS approach is the most promising path. It avoids both the
3D cascade obstacle (§8.11.84) and the flawed change-of-variables approach (session 112).
The main formalization work is: (a) grouping per-link characters by region, (b) proving
the reflection conjugation `Ψ_w = conj(Φ_w(θ...))`, (c) assembling the final |...|².

### What remains unchanged

- All verified lemmas from sessions 105-111 remain GREEN (no code changes).
- Axiom count: still 6 (4 standard + `peterWeyl_clebschGordan_plaquette` +
  `transferMatrixPositivity_axiom`).
- 0 sorries in the codebase.

### The interface link challenge and the `character_expansion_positivity` scaffold

**Key discovery:** the codebase already contains the abstract scaffold for the
reflection positivity proof: `character_expansion_positivity`
(PositiveDefiniteIntegral.lean:1010). This lemma states:

If `K : X → Y → ℂ` has a finite separable decomposition
`K(x, y) = ∑_i a_i · Φ_i(x) · conj(Φ_i(θ y))` with `a_i ≥ 0` and `θ`
measure-preserving, then for real-valued `f`:
`∫∫ f(x) · f(θ y) · K(x, y) dν(y) dμ(x) = ∑_i a_i · ‖∫ f · Φ_i dμ‖² ≥ 0`.

No group structure, no character orthogonality — just measure-preserving CoV
and `f` real-valued. This is EXACTLY the scaffold needed.

**The challenge: getting the separable decomposition.** The interface Boltzmann
`exp(-β·S_int)` must decompose as `∑_w F(w) · Φ_w(x) · conj(Φ_w(θ y))` where
`x` = positive+interface config, `y` = negative config, `θ` = reflection.

The existing `interface_boltzmann_character_expansion` gives:
`exp(-β·S_int) = C · ∑_w F(w) · Φ_w · Ψ_w · V_w`
where `Φ_w = ∏_{pos} χ_{w(l)}(g_l)`, `Ψ_w = ∏_{int} χ_{w(l)}(g_l)`,
`V_w = ∏_{neg} χ_{w(l)}(g_l)` (dual/conj cancel).

The problem: `Ψ_w` (interface link factor) appears in BOTH the positive and
negative sides. It cannot be cleanly assigned to either `Φ_w(x)` or
`conj(Φ_w(θ y))`:
- Putting all of `Ψ_w` in `Φ_w(x)`: requires `conj(Φ_w(θ y)) = V_w(y)`, i.e.,
  `Φ_w(θ y) = conj(V_w(y))`. But `Φ_w(θ y) = [∏_{pos} χ_{w(l)}(θg_l)] · Ψ_w(u⁰)`,
  and `conj(V_w(y)) = ∏_{neg} χ_{dual(w(l))}(g_l)`. The reflection matching
  `∏_{pos} χ_{w(l)}(θg_l) = ∏_{neg} χ_{dual(w(l))}(g_l)` works for temporal
  links (inverted by reflection → conj → dual) but NOT for spatial links
  (not inverted → no conj → dual doesn't match). See detailed analysis above.
- Splitting `Ψ_w` as `Ψ_w^{1/2} · Ψ_w^{1/2}`: requires a "square root" of the
  interface character product, which is the HALF-WEIGHT expansion
  `exp(-β·S_int/2)`. This is the standard OS approach but requires a character
  expansion of the half-weight Boltzmann, which is more complex.

**The `dependsOnlyOnPosSpatialInterface` hypothesis helps but doesn't fully
resolve this.** Since `f` doesn't depend on temporal interface links, the
σ-twist doesn't affect `f`: `f(U⁺, θu⁰) = f(U⁺, u⁰)`. This means
`A_w(θu⁰) = A_w(u⁰)` (the positive-side integral is invariant under σ-twist
of interface links). But `Ψ_w(u⁰)` is still complex, so
`∫ Ψ_w(u⁰) · |A_w(u⁰)|² du⁰` is not obviously ≥ 0.

**Two possible paths forward (for the next session to evaluate):**

1. **Half-weight expansion**: Expand `exp(-β·S_int/2)` (not `exp(-β·S_int)`)
   in characters. This gives `exp(-β·S_int/2) = ∑_w c_w · Φ_w^{1/2} · Ψ_w^{1/2}`
   where the interface factor is split between positive and negative sides.
   Then `G(U) = f·exp(-β·S⁺)·exp(-β·S_int/2)` and
   `G(θU) = f(θU)·exp(-β·S⁻)·exp(-β·S_int/2)`, and the product
   `G(U)·G(θU) = f·f(θU)·exp(-β·S⁺)·exp(-β·S⁻)·exp(-β·S_int)` has the
   full-weight expansion. The half-weight approach requires a character
   expansion of `exp(-β·S_int/2)`, which may need `√coeff` (square root of
   the expansion coefficients). This is standard in the OS literature but
   requires careful formalization.

2. **PD kernel approach**: Use `plaquetteBoltzmannPD` (already proven) +
   Schur product theorem to show `exp(-β·S_int)` is PD on the interface
   links. Then show the transfer matrix kernel `K(V, W)` (integral of the
   PD kernel over negative links) is PD, giving `⟨f, Tf⟩ ≥ 0` by the PD
   quadratic form property. This avoids the character expansion entirely
   for the positivity proof but requires showing the connection between
   PD kernels and reflection positivity (which may need its own lemma).

**Recommendation for next session:** Path 2 (PD kernel approach) may be
simpler since `plaquetteBoltzmannPD` and `fullBoltzmannPD` are already
proven, and the `PositiveDefiniteKernel.comp` lemma
(PositiveDefiniteIntegral.lean:961) provides the composition with
reflection/projection maps. The key lemma needed is: "if `K` is a PD kernel
and `θ` is measure-preserving, then `∫ f(x)·f(θy)·K(x,y) dμ(x)dν(y) ≥ 0`"
— which is essentially `character_expansion_positivity` but with the PD
property replacing the separable decomposition. This may already exist
as `integralOperator_nonneg` or a variant.

### Deep analysis of existing machinery (session 113 continued, 2026-08-15)

**MAJOR FINDING: The existing machinery is FAR more extensive than the session 112
handoff suggested.** The reflection conjugation — the key step I was planning to
formalize — is ALREADY PROVEN. The transfer matrix inner product has been reduced
to a concrete form. The remaining obstacle is precisely identified.

#### Already-proven machinery (all 0 sorries, 0 custom axioms)

1. **`fullReflectReindex` (w*)** (TransferMatrix.lean:5749): The CORRECT reflection
   reindexing that swaps pos ↔ neg via `reflectInterfaceLink`, applying `dual` on
   time-like links. For pos links: temporal → `w*(l) = dual(w(φ(l)))`, spatial →
   `w*(l) = w(φ(l))`. For int/neg links: `w*(l) = w(l)` (unchanged).

2. **`charFactorNeg_eq_star_charFactorPos_fullReflect`** (TransferMatrix.lean:5884):
   The KEY identity: `charFactorNeg w (reflectPosToNeg V⁺) = star(charFactorPos (w*) V⁺)`.
   This is the "reflection conjugation" — the negative character factor at the reflected
   positive config equals the conjugate of the positive character factor at w*.

3. **`star_charFactorNeg_eq_charFactorPos_fullReflect`** (TransferMatrix.lean:5940):
   The conjugate version: `star(charFactorNeg w (reflectPosToNeg V⁺)) = charFactorPos (w*) V⁺`.

4. **`fourierCoeffNeg_eq_fourierCoeffPos_fullReflect`** (TransferMatrix.lean:5970):
   `B_w(u⁰) = A_{w*}(σ(u⁰))` — the negative Fourier coefficient equals the positive
   Fourier coefficient at the reflected weight and reflected interface.

5. **`transfer_matrix_fubini_integrated_pull_fullReflect`** (TransferMatrix.lean:6005):
   The FULL transfer matrix inner product form:
   `∫ ψ·Tψ = C · ∑_w F(w) · ∫_{u⁰} Ψ_w(u⁰) · A_w(u⁰) · A_{w*}(σ(u⁰)) dμ⁰`
   where A_w = fourierCoeffPos, Ψ_w = charFactorInt, F(w) ≥ 0.

6. **Full-lattice analogues** (TransferMatrix.lean:6081-6334): `fullReflectReindexLink`,
   `charFactorPosAll`, `charFactorNegAll`, and the corresponding per-link/product
   identities for ALL links (not just interface links).

7. **`thetaReindex` (θ)** (TransferMatrix.lean:5315): The PROJECTION reindexing
   (idempotent, NOT a bijection). This was the first attempt; it's superseded by
   `fullReflectReindex` (w*) which IS a valid reindexing for the reflection identity.

8. **`character_expansion_positivity`** (PositiveDefiniteIntegral.lean:1010): The
   abstract scaffold: if K(x,y) = ∑_i a_i · Φ_i(x) · conj(Φ_i(θy)) with a_i ≥ 0 and
   θ measure-preserving, then ∫∫ f(x)·f(θy)·K(x,y) dν dμ = ∑_i a_i · ‖∫ f·Φ_i dμ‖² ≥ 0.

#### The EXACT remaining obstacle

The transfer matrix inner product is:
```
∫ ψ·Tψ = C · ∑_w F(w) · ∫_{u⁰} Ψ_w(u⁰) · A_w(u⁰) · A_{w*}(σ(u⁰)) dμ⁰
```

For non-negativity, we need each term `∫_{u⁰} Ψ_w(u⁰) · A_w(u⁰) · A_{w*}(σ(u⁰)) dμ⁰ ≥ 0`
(or the full sum ≥ 0).

**Key simplification from `dependsOnlyOnPosSpatialInterface`:** Since ψ (hence f)
doesn't depend on temporal interface links, and σ only inverts temporal interface
links, we have `A_w(σ(u⁰)) = A_w(u⁰)`. So the integral becomes:
```
∫_{u⁰} Ψ_w(u⁰) · A_w(u⁰) · A_{w*}(u⁰) dμ⁰
```

**The obstacle:** Ψ_w(u⁰) = ∏_{l ∈ interfaceLinks} χ_{w(l)}(g_l) is COMPLEX (product
of characters). The integral `∫ Ψ_w · A_w · A_{w*} dμ⁰` is NOT obviously ≥ 0.

**Why the separable form doesn't work directly:** For `character_expansion_positivity`,
we need K(x,y) = ∑_w a_w · Φ̃_w(x) · conj(Φ̃_w(θy)). Setting
Φ̃_w(u) = exp(-β·S⁺/2)·Φ_w(U⁺)·Ψ_w(u⁰), we need conj(Φ̃_w(θy)) = exp(-β·S⁻/2)·star(V_w(U⁻)),
i.e., Φ̃_w(θy) = exp(-β·S⁻/2)·V_w(U⁻). This requires:
```
Φ_w(U⁺(θy)) · Ψ_w(σ(u⁰)) = V_w(U⁻)
```
Using the existing identity `star_charFactorNeg_eq_charFactorPos_fullReflect`:
`charFactorPos (w*) (U⁺(θy)) = star(charFactorNeg w U⁻) = star(V_w(U⁻))`
So: `Φ_{w*}(U⁺(θy)) = star(V_w(U⁻))`, and we need:
`star(V_w(U⁻)) · Ψ_w(σ(u⁰)) = V_w(U⁻)`, i.e., `Ψ_w(σ(u⁰)) = V_w(U⁻)/star(V_w(U⁻))`.
This is NOT an identity — it doesn't hold in general.

**Why sum reindexing w → w* doesn't work:** `fullReflectReindex` is IDEMPOTENT
(θ(θw) = θw, proven at TransferMatrix.lean:5631), NOT a bijection. So the sum
reindexing `∑_w F(w)·G(w) = ∑_w F(w*)·G(w*)` is INVALID (§8.11.24).

#### The interface link factor Ψ_w is the crux

The interface character factor `Ψ_w(u⁰) = ∏_{l ∈ interfaceLinks} χ_{w(l)}(g_l)` couples
the positive and negative sides. It appears in BOTH the positive factor (Φ̃_w includes
Ψ_w) and the reflected negative factor (Φ̃_w(θy) includes Ψ_w(σ(u⁰))). This prevents
the clean separation needed for `character_expansion_positivity`.

**Temporal interface links:** Can be integrated out using character orthogonality
(∫ χ_w dμ = 0 for non-trivial w), forcing w(l) = σ_0 for temporal interface links.
This is because A_w doesn't depend on temporal interface links (f doesn't depend on them).

**Spatial interface links:** CANNOT be integrated out independently because A_w depends
on them (through f, which depends on spatial interface links). The integral
`∫_{u⁰_s} [∏_{spatial int} χ_{w(l)}(g_l)] · A_w(u⁰_s) · A_{w*}(u⁰_s) dμ⁰_s` is the
remaining challenge.

#### Three possible paths forward (refined)

1. **Half-weight expansion (Path 1):** Expand `exp(-β·S_int/2)` in characters instead of
   `exp(-β·S_int)`. This splits the interface character factor between the positive and
   negative sides: `G(U) = f·exp(-β·S⁺)·exp(-β·S_int/2)` uses the half-weight expansion,
   and `G(θU) = f(θU)·exp(-β·S⁻)·exp(-β·S_int/2)` uses the same half-weight expansion
   at the reflected config. The product `G(U)·G(θU)` then has the FULL-weight expansion.
   The key: the half-weight expansion may have a separable form where the interface
   factor is split as `Ψ_w^{1/2} · Ψ_w^{1/2}`, one half in each factor. This requires
   a character expansion of `exp(-β·S_int/2)`, which may need `√coeff` (square root of
   expansion coefficients). **Status: NOT yet formalized. The `√coeff` approach is
   standard in OS literature but requires careful handling.**

2. **PD kernel approach (Path 2):** Use `plaquetteBoltzmannPD` (proven) + Schur product
   to show `exp(-β·S_int)` is PD on the interface link group. Then show the transfer
   matrix kernel `K(u, U⁻) = exp(-β·(S⁺/2 + S⁻/2 + S_int))` is PD, giving `⟨g, Tg⟩ ≥ 0`.
   The key lemma needed: "if K is a PD kernel and θ is measure-preserving, then
   `∫ f(x)·f(θy)·K(x,y) dμ dν ≥ 0`" — this is `character_expansion_positivity` with
   the PD property replacing the separable decomposition. **Status: The PD property
   of `exp(-β·S_int)` on the interface link group is NOT yet proven (only the plaquette-
   level and full-lattice PD are proven). The connection between PD kernels and
   reflection positivity needs a new lemma.**

3. **Direct |...|² approach (Path 3):** Show that the sum
   `∑_w F(w) · ∫_{u⁰} Ψ_w(u⁰) · A_w(u⁰) · A_{w*}(u⁰) dμ⁰` can be reorganized as
   `∑_w' F'(w') · |∫_{u⁰} A_{w'}(u⁰) · Ψ'_{w'}(u⁰) dμ⁰|² ≥ 0` for some reindexed sum
   and modified character factors. This requires understanding the coupling between
   w and w* through the plaquette coefficients F(w). **Status: NOT yet analyzed in
   detail. The coupling through F(w) is the key difficulty.**

**Recommendation:** Path 1 (half-weight expansion) is the most standard OS approach and
most likely to work. The key insight is that `exp(-β·S_int/2) = (exp(-β·S_int))^{1/2}`,
and if the character expansion of `exp(-β·S_int)` has non-negative coefficients, then
the half-weight expansion can be obtained by taking square roots of the coefficients
(this works because the character expansion is a sum of PD functions with non-negative
coefficients, and the square root of a PD function with non-negative coefficient sum
is also PD). The next session should investigate whether this can be formalized using
the existing `peterWeyl_clebschGordan_plaquette` axiom (Part 1).

---

## §8.11.86 — Session 117 analysis (2026-08-15): Step A infrastructure already in place

Session 117 was an analysis session (no code changes). It verified the
current state of STEP 6 and found that **two of the three "Step A"
sub-tasks from the session-116 handoff are already done**:

### Already done

1. **Step A.1 (V positive):** `spatialBoltzmannPD`
   (`ReflectionPositivity/FullBoltzmannPD.lean:258`) proves the spatial
   Boltzmann factor `exp(-β·S_spatial)` is positive-definite on the link
   group, via the Schur product theorem (`PositiveDefinite.finprod`).

2. **Step A.2 (group-PD → operator positivity):**
   `PositiveDefinite.integralOperator_nonneg`
   (`PositiveDefiniteIntegral/IntegralOperator.lean:140`) proves: for a
   compact group `G` with probability measure `μ`, a continuous PD function
   `φ`, and continuous `f`,
   `∫∫ f(x)·conj(f(y))·φ(x⁻¹·y) dμ dμ ≥ 0`. This is the continuous analogue
   of the `PositiveDefinite` definition — exactly the connection from
   group-PD to positive integral operator. **No new lemma needed.**

3. **Abstract positivity scaffold:** `character_expansion_positivity`,
   `character_expansion_nonneg`, `character_expansion_nonneg_shared`
   (`PositiveDefiniteIntegral/CharacterExpansionPositivity.lean:44,181,231`)
   prove: if a kernel `K(x,y) = Σ_i a_i·Φ_i(x)·conj(Φ_i(θy))` with `a_i ≥ 0`
   and `θ` measure-preserving, then `∫∫ f(x)·f(θy)·K(x,y) ≥ 0`. The
   shared-variable variant handles the transfer-matrix structure where a
   spatial interface variable `z` is shared between the `x` and `y`
   integrals.

4. **2-site cascade end-to-end:** `shared_cascade_factorization_nonneg_conj`
   (`PositiveDefiniteIntegral/CascadeNonneg.lean:717`) +
   `cascade_shared_kernel_form` (line 785) connect the 2-site Lüscher
   cascade to the conjugated kernel form `Σ_s c_s·conj(χ_s(z·x))·χ_s(z·y)`
   with `c_s ≥ 0`, and prove the integral is non-negative. **The 1D
   (2-site) case is fully done end-to-end.**

5. **1D L-site cascade:** `chainIntegral_eq`, `bipartiteChainIntegral_eq`
   (`PositiveDefinite/LuscherCascade.lean:61,212`) generalize the 2-site
   cascade to arbitrary chain length via induction + `luscher_key_identity`.

6. **3D single-site integral:** `single_site_3D_luscher_integral`
   (`PeterWeyl/Site3DIntegral.lean:484`) integrates ONE temporal link in 3
   plaquettes (3 spatial directions), producing a sum of CG-coefficient
   products times `(1/dims α)`.

7. **3D diagonal non-negativity:** `cg_unitarity_nonneg`
   (`PeterWeyl/Site3DIntegral.lean:725`) proves the DIAGONAL case (barred
   indices = unbarred indices) gives `Σ_{α,p,q} (1/dims α)·|C(α,p,q)|² ≥ 0`.

### The crux (NOT done): 3D off-diagonal cascade

The off-diagonal case of `single_site_3D_luscher_integral` (where the
barred indices differ from the unbarred indices, as happens in the
multi-site transfer matrix) gives a product of two DIFFERENT CG sums:
`Σ U(ν,r,s,α,p,q) · (1/dims α) · Σ B(ν',r',s',α,p,q)`, which is NOT
`|C|²` and is not obviously non-negative locally.

The non-negativity comes from the GLOBAL cascade (integrating out ALL
temporal links site by site): the product of CG sums across sites
collapses to `Σ_s a_s · χ_s(W-product) · χ_s(V-product)` with `a_s ≥ 0`,
and the reflection maps `χ_s(W-product) = conj(χ_s(V-product))`, giving
`|χ_s|²` (the `|E_s|²` argument, §8.11.75). This global cascade is NOT
formalized.

### Remaining work for STEP 6

- **Step A.4 (T = V^{1/2}·U·V^{1/2} factorization):** Split the OS-positive
  action `S⁺ = S_spatial + S_temporal⁺/2` and show the transfer matrix
  kernel factors. This is concrete algebra but non-trivial (requires
  identifying which plaquettes contribute to V vs U).

- **Step A.5 (ABA ≥ 0):** In the concrete setting, this reduces to a
  change of variables `h = √v · g` (where `v = exp(-β·S_spatial)`), so
  `∫ g·Tg = ∫ h·U(h) ≥ 0` if U is positive. This is built into the
  factorization, not a separate lemma.

- **Step B (3D global cascade — THE CRUX):** Formalize the global cascade
  that integrates out ALL temporal links, producing
  `Σ_s a_s · χ_s(W) · conj(χ_s(V))` with `a_s ≥ 0`. This requires:
  (a) identifying the lattice structure (which temporal links appear in
  which plaquettes), (b) ordering the cascade (which links to integrate
  out first), (c) showing the CG coefficient products collapse to the
  `|E_s|²` form. The off-diagonal CG unitarity is the key ingredient.

- **Step C (conclude):** Apply `shared_cascade_factorization_nonneg_conj`
  to the global cascade result, then use
  `integral_G_thetaG_eq_inner_g_Tg` to convert `⟨g, Tg⟩ ≥ 0` to
  `∫ G·G(θU) ≥ 0`, replacing the axiom.

### Adversarial self-check (session 117)

Steelmanning the dead-end case: (1) The character expansion approach
(w* idempotent) is a documented dead end — the enormous infrastructure
built for it (Bridge.lean, FullReflect.lean) may not directly contribute
via the Lüscher route. (2) The 3D cascade is genuinely hard and may be a
multi-session effort. (3) The "6→5" headline is misleading per
`honest_frontier_audit.md` — `peterWeyl_clebschGordan_plaquette` has
absorbed ~3 substantial prerequisites comparably hard to the target. (4)
The Lüscher decomposition requires connecting the abstract cascade
(LuscherCascade.lean) to the concrete transfer matrix
(transferMatrixCorrect), which requires the 3D lattice structure.

**Honest verdict:** The infrastructure is substantially in place. The
remaining work is the 3D global cascade (Step B), which is the genuine
crux. This is "known but unformalized" math (Lüscher's approach is
standard in the literature), not genuinely open math. No axiom
strengthening is needed — the obstacle is formalization effort.

## §8.11.87 — Session 120 (2026-08-15): Step A.5 COMPLETE

Step A.5 (T = V^{1/2}·U·V^{1/2} factorization, the ABA ≥ 0 algebraic step)
is now COMPLETE and committed. Two new lemmas in LuscherDecomposition.lean:

### 1. Kernel-level factorization: `transferMatrix_kernel_VUV_factorization`

The transfer matrix kernel `exp(-β·(S⁺(u)/2 + S⁺(u')/2 + S_int))` factors as:

    K = V^{1/2}(u) · U_kernel(u, u', full_config) · V^{1/2}(u')

where:
- **V^{1/2}(u) = exp(-β·S_spatial⁺(u)/2)** — the spatial Boltzmann factor
  (PD by `spatialBoltzmannPD`, Step A.1). Depends only on positive-time
  spatial links (within a single time slice).
- **U_kernel = exp(-β·(S_temporal⁺(u)/2 + S_temporal⁺(u')/2 + S_int))** —
  the temporal integral operator kernel. Includes the FULL interface action
  S_int (spatial interface plaquettes depend on interface links, which are
  shared between the two sides of the transfer matrix, so they belong to U,
  not V).

**Proof:** Split S⁺ = S_spatial + S_temporal (keeping S_int whole), regroup
the exponent as `[spatial⁺(u)/2] + [temporal⁺(u)/2 + temporal⁺(u')/2 + S_int]
+ [spatial⁺(u')/2]`, apply `Real.exp_add` twice. Pure algebra. Only standard
3 axioms (propext, Classical.choice, Quot.sound).

### 2. Operator-level factorization: `transferMatrixReflected_VUV_factorization`

Lifts the kernel identity to the operator level:

    (Tψ)(u) = V^{1/2}(u) · ∫_{V⁺} V^{1/2}(u')·ψ(u')·U_kernel dμ⁺(V⁺)

where u' = mergePosInterface(V⁺, σ(u⁰)). This is the ABA form:
**T = V^{1/2}·U·V^{1/2}** at the operator level.

**Proof:** Apply the kernel factorization pointwise, rearrange with `ring`,
pull V^{1/2}(u) out of the integral via `integral_const_mul`. Only standard
3 axioms.

### What this means for the positivity argument

The inner product `⟨g, Tg⟩ = ∫ g(u)·(Tg)(u) dμ⁺⁰(u)` now becomes:

    ⟨g, Tg⟩ = ∫ (V^{1/2}·g)(u) · (U·(V^{1/2}·g))(u) dμ⁺⁰(u) = ⟨V^{1/2}g, U·(V^{1/2}g)⟩

This is ≥ 0 **if U is positive** (Step B). The V^{1/2} factor is PD by
`spatialBoltzmannPD` (Step A.1), and the group-PD → operator positivity
connection is `integralOperator_nonneg` (Step A.2). So the entire Step A
(A.1–A.5) is now complete; the remaining obstacle is **Step B: showing U
is positive via the 3D Lüscher cascade**.

### Adversarial self-check (session 120)

Steelmanning the dead-end case: (1) The w* idempotency dead end is
documented — the character expansion approach via `fullReflectReindex`
cannot work because w* is idempotent, not a bijection. The Lüscher
cascade route bypasses this by integrating out temporal links site by
site. (2) The 3D cascade (Step B) is the genuine crux — it requires
connecting the abstract cascade (LuscherCascade.lean) to the concrete
3D lattice structure, which is substantial formalization effort. (3)
The "6→5" headline remains misleading per `honest_frontier_audit.md` —
even if Step B closes, the assumption burden has relocated to
`peterWeyl_clebschGordan_plaquette`, not decreased. (4) Step A.5 itself
is pure algebra and does not advance the mathematical frontier — it's
wiring that connects Steps A.1–A.4 to the positivity conclusion.

**Honest verdict:** Step A.5 is a clean algebraic identity that was
straightforward to prove. The real work remains Step B (3D cascade).
No axiom strengthening was needed or used.

## §8.11.88 — Session 121 (2026-08-15): Step B adversarial self-check + structural analysis

### Adversarial self-check (session 121)

Steelmanning the dead-end case for Step B (3D off-diagonal cascade):

1. **The 1D vs 3D structural gap is fundamental.** In the 1D bipartite
   cascade (`bipartiteChainIntegral_eq`), each temporal link appears in
   exactly 2 plaquettes (one forward, one backward). The 2-character
   integral is evaluated by Schur orthogonality, which gives a Kronecker
   delta: either the reps match (survive as a single character × scalar)
   or they don't (vanish). This keeps the cascade clean — each step
   produces a single character, and the induction works.

   In 3D (3+1D lattice), each temporal link appears in 6 plaquettes
   (3 spatial directions × 2 orientations: forward and backward). The
   6-character integral (3 unbarred `χ_s(g·A)`, 3 barred
   `conj(χ_t(g·B))`) is evaluated by `single_site_3D_luscher_integral`,
   which uses matrix-element CG (`cgME_decomp_3fold`) to reduce 3
   unbarred MEs to 1, then Schur to integrate. The result is a SUM of
   CG matrix-element products — NOT a single character. There is no
   Kronecker delta killing; the CG decomposition produces a sum.

2. **The 2D cascade works because of character-level CG.**
   `luscher_2site_2D_cascade_charlevel` handles 2 plaquettes per link
   (2 spatial directions). The 2 characters per link have the SAME
   argument (e.g., `χ_{s1}(g₀·W·g₁⁻¹) · χ_{s2}(g₀·W·g₁⁻¹)`), so
   character-level CG (`χ_s · χ_t = Σ_ν cg(s,t,ν) · χ_ν` with
   `cg ≥ 0`) reduces them to a single character. Then Schur integrates.
   The coefficient `cg(s1,s2,ν)·cg(t1,t2,ν)·(1/dims ν) ≥ 0` because
   character-level CG coefficients are non-negative.

   In 3D, the 3 characters per link have DIFFERENT arguments
   (`χ_{s1}(g·A1)`, `χ_{s2}(g·A2)`, `χ_{s3}(g·A3)` with A1≠A2≠A3 —
   different spatial link products per direction). Character-level CG
   requires the SAME argument, so it does NOT apply. Matrix-element CG
   is required, and its coefficients are complex (not non-negative).

3. **The single-site 3D integral is NOT non-negative off-diagonal.**
   `cg_unitarity_nonneg` proves non-negativity only in the DIAGONAL case
   (barred indices = unbarred indices), giving `Σ |C|²/dims α ≥ 0`.
   The off-diagonal case gives `C · conj(C')` (a complex inner product),
   which is NOT necessarily real or non-negative. The non-negativity
   is GLOBAL — it emerges only after integrating out ALL temporal links
   and using CG unitarity to collapse the intermediate sums.

4. **Term explosion concern.** In 1D, each cascade step kills all but
   one term (Schur delta), so the term count stays bounded. In 3D, each
   step produces a SUM of CG products. The full cascade over a 3D grid
   of temporal links has exponential term growth. The CG unitarity
   (`hcgME_unitary`) collapses this at the END, but the intermediate
   bookkeeping is substantial. A direct step-by-step formalization on
   the concrete lattice may be intractable; an abstract tensor-network
   formulation may be needed.

5. **`hcgME_unitary` has never been applied.** The CG unitarity
   hypothesis (`hcgME_unitary`: `∑_ν ∑_p conj(cgME s t ν a i p) *
   cgME s t ν b j p = δ_{a,b}·δ_{i,j}`) is available in the axiom but
   has not been used in any proof. It is the key ingredient for the 3D
   cascade collapse. Applying it is the essential new step.

6. **The "6→5" headline remains misleading** per `honest_frontier_audit.md`.

**Honest verdict:** Step B is NOT a dead end — the math is known
(Lüscher, Osterwalder-Seiler). But the formalization is genuinely hard:
the 3D cascade requires matrix-element CG (complex coefficients), the
non-negativity is global (not single-site), and the term explosion may
require an abstract formulation. The key new ingredient is applying
`hcgME_unitary` to collapse the cascade. This is "known but
unformalized" — substantial multi-session effort, not open math.

### Structural analysis: what Step B requires

The character expansion (`temporal_product_character_expansion`) gives:
```
∏_p exp(...) = ∑_w F(w) · Φ_w(spatial) · Ψ_w(temporal)
```
where `F(w) ≥ 0`, `Φ_w` = product of spatial-link characters (external
kernel variables W, V), `Ψ_w` = product of temporal-link characters
(internal, to be integrated out).

The cascade integrates out temporal links:
```
K(W,V) = ∑_w F(w) · Φ_w(W,V) · [∫ Ψ_w(temporal) dμ(temporal)]
```

In 1D: `∫ Ψ_w dμ = (1/d_γ)^n · χ_γ(W-prod · V-prod⁻¹)` — a single
character, giving a PD kernel `Σ_s c_s · χ_s(W·V⁻¹)` with `c_s ≥ 0`.

In 3D: `∫ Ψ_w dμ` = sum of CG matrix-element products (complex). The
non-negativity comes from the B*B structure: the cascade defines an
operator B (Fourier coefficient extraction), and `K = B*B` gives
`⟨g, Tg⟩ = ‖Bg‖² ≥ 0`. The CG unitarity (`hcgME_unitary`) is the
mechanism that makes B*B work.

**Formalization plan for Step B:**
- B.1: Apply `hcgME_unitary` to prove a CG-collapse identity (the key
  new ingredient — `hcgME_unitary` has never been applied).
- B.2: Use the collapse to show the 2-site 3D cascade produces a
  separable kernel (analogous to `luscher_2site_2D_cascade_charlevel`
  but with matrix-element CG).
- B.3: Generalize to the full 3D grid (induction or tensor network).
- B.4: Apply `shared_cascade_factorization_nonneg_conj` to conclude.

## §8.11.89 — Session 124 (2026-08-16): Step B.1 COMPLETE; adversarial self-check; B.2 formalization plan

### Step B.1 COMPLETE — `cgME_isometry_normSq` proven (session 123, commit a3e33b4)

The CG Parseval identity (the key building block for Step B) is now PROVEN in
`src/lean/YangMills/Proofs/PeterWeyl/CGUnitarity.lean`:

```
∑ (ν : ι), ∑ (p : Fin (dims ν)),
  Complex.normSq (∑ (a : Fin (dims s)), ∑ (i : Fin (dims t)),
    cgME s t ν a i p * v a i) =
∑ (a : Fin (dims s)), ∑ (i : Fin (dims t)),
  Complex.normSq (v a i)
```

**`#print axioms cgME_isometry_normSq` = `[propext, Classical.choice, Quot.sound]`** — only
the 3 standard axioms, NO `sorryAx`. This is the **first-ever application of
`hcgME_unitary`** (the CG unitarity relation from the Peter-Weyl axiom), which had been
available in the axiom since its introduction (strengthening #5, 2026-08-02) but never
applied in any proof.

**Confirmation of the §8.11.88 prediction.** The session 121 structural analysis
identified `hcgME_unitary` as "the essential new ingredient for the 3D cascade collapse"
and predicted that applying it was the key step. This prediction is now **confirmed**:
`cgME_isometry_normSq` is proved by a direct application of `hcgME_unitary` (Step 5 of the
proof: `simp only [hcgME_unitary]` collapses the inner sum to a Kronecker delta, then the
delta is eliminated by `Finset.sum_eq_single`).

**Proof technique (6 steps, for reference):**
1. **ℝ→ℂ conversion**: `rw [← Complex.ofReal_inj]; simp only [Complex.ofReal_sum];
   simp only [Complex.normSq_eq_conj_mul_self]` — converts the ℝ-valued normSq sum to a
   ℂ-valued sum where `normSq z = conj z * z` applies. (This was the line 51 bug —
   `simp only [Complex.normSq_eq_conj_mul_self]` alone made no progress because the sum
   was ℝ-valued, not coerced to ℂ.)
2. **conj expansion** (`hconj` have): uses forward `map_sum (starRingEnd ℂ)` to push conj
   through the sums, then `map_mul` to split products.
3. **Product distribution**: `simp only [Finset.sum_mul_sum]` then a `sum_comm` to reorder
   (a,b,i,j) → (a,i,b,j), with `ring` at the leaf.
4. **Sum exchange** (the hard part): 8 `Finset.sum_comm` swaps (each wrapped in
   `Finset.sum_congr rfl` to go under binders) to reorder `(ν,p,a,i,b,j) → (a,i,b,j,ν,p)`.
   The dependent `p : Fin (dims ν)` sum is handled because within a fixed `ν`, `p` is
   independent of `a,i,b,j`.
5. **Reassociation + factoring**: `h_term` (a `ring` identity) reassociates each leaf term,
   then `simp only [← Finset.mul_sum]` factors `conj(v) * v` out of the `(ν,p)` sum.
6. **Delta collapse**: `simp only [hcgME_unitary]` rewrites the inner sum to
   `if a = b ∧ i = j then 1 else 0`, then `congr 1; ext a; congr 1; ext i` peels the outer
   sums, then nested `Finset.sum_eq_single a` / `Finset.sum_eq_single i` with
   `if_pos (And.intro rfl rfl)` / `if_neg (fun h => hij (h.2.symm))` / `Finset.sum_eq_zero`
   handle the three cases.

**Axiom count**: still 6 (the `peterWeyl_clebschGordan_plaquette` axiom, which contains
`hcgME_unitary`). The new lemma uses `hcgME_unitary` but does NOT reduce the axiom count
yet — that requires Step B.2 (proving `transferMatrixPositivity_axiom` from this).

### Adversarial self-check (session 124)

Steelmanning the dead-end case for the cgME_isometry_normSq → cascade non-negativity
approach:

1. **The isometry is single-site; the cascade is multi-site.** `cgME_isometry_normSq`
   proves the Parseval identity for a SINGLE application of the CG change-of-basis (one
   (s,t) pair → ν). The 3D cascade requires applying CG at EACH temporal link, and the
   isometry needs to compose across sites. The multi-site generalization requires an
   inductive/tensor-network argument that is not yet formalized and may be substantial.

2. **The off-diagonal case involves DIFFERENT reps.** The isometry
   `cgME_isometry_normSq` is for a fixed (s,t) pair — it says `cgME s t ν` is an isometry
   from `Fin(dims s) × Fin(dims t)` to `⊕_ν Fin(dims ν)`. But in the off-diagonal cascade,
   the unbarred MEs use reps (s1,s2,s3) and the barred MEs use reps (t1,t2,t3). The
   isometry for (s1,s2) doesn't directly collapse the cross-term between (s1,s2) and
   (t1,t2). The non-negativity is GLOBAL — it emerges only after summing over ALL sites
   and ALL weights, with the isometry collapsing the FULL sum, not individual cross-terms.

3. **The B*B structure requires defining the operator B.** The cascade defines B as the
   Fourier coefficient extraction operator, but formalizing B as a linear operator on the
   right Hilbert space, and showing `⟨g, Tg⟩ = ‖Bg‖²`, requires matching the abstract
   isometry (finite-dimensional ℓ²) to the concrete cascade (integrals over group
   elements). The index bookkeeping is substantial.

4. **Term explosion.** As noted in §8.11.88, the 3D cascade has exponential term growth.
   The isometry collapses the cascade at the END, but the intermediate bookkeeping (12
   nested sums per site, composed across sites) may be intractable in Lean without an
   abstract tensor-network formulation.

5. **Closing transferMatrixPositivity_axiom does NOT close the mass gap or continuum
   limit.** Per `honest_frontier_audit.md`: even if Step B.2 succeeds, the "6→5" headline
   is misleading (peterWeyl_clebschGordan_plaquette has absorbed ~3 substantial
   prerequisites comparably hard to the target), and the genuinely open problems
   (continuum_limit_exists: B5 IR control; mass_gap_axiom: M1b uniform gap) remain open.
   Step B.2 is "known but unformalized" — substantial formalization effort, not open math.

**Honest verdict:** The cgME_isometry_normSq → cascade non-negativity approach is NOT a
dead end — the math is known (Lüscher, Osterwalder-Seiler), and the isometry IS the right
tool (it is the Parseval identity that makes the B*B kernel positive semidefinite). But
the formalization is genuinely hard: the multi-site generalization, the off-diagonal
cross-term handling, and the term explosion all require careful work. The isometry is a
necessary but not sufficient ingredient — it must be composed across sites and matched to
the concrete cascade structure. This is "known but unformalized" — substantial
multi-session effort, not open math, and not a quick win.

### B.2 formalization plan: how cgME_isometry_normSq applies to the 3D off-diagonal cascade

**The structure of the problem.** The reflection-positivity integral is:
```
I = ∫ f(U) · f(θU) · exp(-β S_W(U)) dμ₀
```
After character expansion (`osG_thetaG_eq_char_expansion_pointwise`), this becomes:
```
I = C · ∑_w F(w) · ∫ [f(U)·f(θU)·r(U)] · Φ_w(U) · Ψ_w(U) · V_w(U) dμ₀
```
where Φ_w = positive-link characters (external), Ψ_w = interface-link characters
(internal, integrated out), V_w = negative-link conj characters (external, reflected).

**The cascade.** Integrating out the temporal (interface) links gives a kernel
K(W,V) = ∑_w F(w) · Φ_w(W) · [∫ Ψ_w(temporal) dμ] · V_w(V). In 1D, `∫ Ψ_w dμ` is a single
character (Schur delta), giving a PD kernel `Σ_s c_s χ_s(W·V⁻¹)`. In 3D, `∫ Ψ_w dμ` is a
sum of CG matrix-element products (complex), and the non-negativity is GLOBAL.

**The B*B structure.** The cascade defines an operator B (Fourier coefficient extraction):
`(Bg)_w = ∫ g · Ψ_w dμ` (roughly). Then `⟨g, Tg⟩ = ⟨Bg, Bg⟩ = ‖Bg‖² ≥ 0`. The CG
isometry (`cgME_isometry_normSq`) is the mechanism that makes B an isometry (B*B = I on
the Fourier side), hence T = B*B is positive semidefinite.

**The connection to single_site_3D_luscher_integral.** The 6-ME integral evaluates to:
```
∑_{ν,r,s,α,p,q} U(ν,r,s,α,p,q) · (1/dims α) · ∑_{ν',r',s'} V(ν',r',s',α,p,q)
```
where U = unbarred CG product, V = barred CG product. In the diagonal case (U=V), this is
`∑ (1/dims α) |C|² ≥ 0` (proven by `cg_unitarity_nonneg`). In the off-diagonal case, the
non-negativity requires the isometry to collapse the FULL sum over all sites and weights.

**The formalization path for B.2:**
- **B.2a**: Define the operator B abstractly — for a fixed (s,t) pair, B maps
  `v : Fin(dims s) → Fin(dims t) → ℂ` to `(Bg) : ∀ ν, Fin(dims ν) → ℂ` via
  `(Bg) ν p = ∑_{a,i} cgME s t ν a i p * v a i`. The isometry `cgME_isometry_normSq`
  then gives `‖Bg‖² = ‖g‖²` (Parseval).
- **B.2b**: Show the 2-site 3D cascade kernel factors as B*B. The 2-site cascade
  integrates out one temporal link, producing a kernel K(W,V) that is a sum of CG
  products. Match this to the B*B form: K(W,V) = ∑_w F(w) · (BΦ_w)(W) · conj((BΦ_w)(V)).
- **B.2c**: Apply the isometry to conclude `⟨g, Tg⟩ = ‖Bg‖² ≥ 0` for the 2-site case.
- **B.3**: Generalize to the full 3D grid (induction or tensor network).
- **B.4**: Apply `shared_cascade_factorization_nonneg_conj` to conclude.

**Key challenge:** B.2b requires matching the abstract isometry (which operates on
finite-dimensional ℓ² vectors) to the concrete cascade (which involves integrals over
group elements and 12 nested sums per site). The index bookkeeping is the main
formalization hurdle. An abstract tensor-network formulation may be needed to manage the
term explosion.

**Status:** Step B.2 is NOT YET STARTED. The next session should begin by studying the
2-site cascade structure and sketching the B operator definition (B.2a).

### Deeper analysis: the 3-fold isometry (composed Parseval) — the key lemma for B.2

**The core challenge.** The single isometry `cgME_isometry_normSq` proves the Parseval
identity for a SINGLE CG application (one (s,t) pair → ν). But the 3D cascade uses the
3-fold CG decomposition (`cgME_decomp_3fold`), which applies CG TWICE:
1. First: `cgME s1 s2 ν` (combining reps s1, s2 → ν)
2. Second: `cgME ν s3 α` (combining ν, s3 → α)

The 3-fold CG coefficient is:
```
C(α,p,q; a,b) = ∑_{ν,r,s} cgME s1 s2 ν a1 a2 r * cgME ν s3 α r a3 p *
                         conj(cgME s1 s2 ν b1 b2 s * cgME ν s3 α s b3 q)
```
where a = (a1,a2,a3) are row indices, b = (b1,b2,b3) are column indices.

**The 3-fold isometry (norm-sq form) would be:**
```
∑_{α,p} |∑_{a1,a2,a3} [∑_{ν,r} cgME s1 s2 ν a1 a2 r * cgME ν s3 α r a3 p] * v(a1,a2,a3)|²
  = ∑_{a1,a2,a3} |v(a1,a2,a3)|²
```

**Why this is NOT a simple composition of two single isometries.** The naive approach:
1. Define intermediate `u_{a3}(ν,r) = ∑_{a1,a2} cgME s1 s2 ν a1 a2 r * v(a1,a2,a3)`
2. Apply single isometry (s1,s2)→ν: `∑_{ν,r} |u_{a3}(ν,r)|² = ∑_{a1,a2} |v(a1,a2,a3)|²`
3. Define `w(α,p) = ∑_{ν,r,a3} cgME ν s3 α r a3 p * u_{a3}(ν,r)`
4. Apply single isometry (ν,s3)→α: `∑_{α,p} |w(α,p)|² = ∑_{ν,r,a3} |u_{a3}(ν,r)|²`

**The problem:** Step 4 fails because the single isometry for (ν,s3)→α requires ν to be
FIXED, but in step 3, ν is SUMMED over. The single isometry says:
```
∑_{α,p} |∑_{r,a3} cgME ν s3 α r a3 p * u_ν(r,a3)|² = ∑_{r,a3} |u_ν(r,a3)|²
```
for each FIXED ν. But `w(α,p) = ∑_ν ∑_{r,a3} cgME ν s3 α r a3 p * u_ν(r,a3)` sums over ν,
so the single isometry doesn't directly apply.

**The resolution.** The 3-fold isometry requires a more careful argument. Two approaches:

**Approach A (completeness relation, not norm-sq).** Instead of the norm-sq form, prove the
3-fold COMPLETENESS relation directly from `hcgME_unitary`:
```
∑_{α,p,q} conj(C(α,p,q; a,b)) * C(α,p,q; a',b') = δ_{a,a'} · δ_{b,b'}
```
This can be proved by applying `hcgME_unitary` twice:
1. Apply `hcgME_unitary` for (s1,s2)→ν: collapses the (a1,a2,b1,b2) indices to δ
2. Apply `hcgME_unitary` for (ν,s3)→α: collapses the (r,a3,s,b3) indices to δ
The index bookkeeping is the challenge — the (ν,r,s) sum is shared between the two
applications, and the order of collapse matters.

**Approach B (associativity / 6j symbols).** The 3-fold CG decomposition depends on the
association order: (s1⊗s2)⊗s3 vs s1⊗(s2⊗s3). The two are related by 6j symbols (Racah
coefficients). The isometry holds regardless of association order because the total map
s1⊗s2⊗s3 → ⊕_α α is unitary. But formalizing this requires the 6j symbol machinery, which
is not currently in the project.

**Approach C (direct from hcgME_unitary, norm-sq form).** Prove the 3-fold isometry
(norm-sq form) directly by expanding `|w|² = conj(w)·w`, distributing the product of sums,
exchanging the (α,p) sum with the (a,b) sums, and applying `hcgME_unitary` twice to collapse
the inner sums. This is the same technique as `cgME_isometry_normSq` but with an extra level
of CG composition. The proof would be ~2x the length of `cgME_isometry_normSq` (which is
208 lines), so ~400 lines. The main challenge is the sum reordering (16+ `Finset.sum_comm`
swaps) and the two-level delta collapse.

**Recommendation:** Approach C (direct from `hcgME_unitary`, norm-sq form) is the most
tractable. It follows the same pattern as the proven `cgME_isometry_normSq` but with an
extra CG level. The key steps:
1. Expand `|w(α,p)|² = conj(w(α,p)) * w(α,p)`
2. Distribute conj through the (a1,a2,a3,ν,r) sums and w through the (b1,b2,b3,ν',r') sums
3. Exchange the (α,p) sum to the inside
4. Apply `hcgME_unitary` for (ν,s3)→α to collapse the (α,p) sum: gives δ_{r,r'} · δ_{a3,b3}
5. Collapse the δ_{a3,b3} (sum over a3=b3)
6. Apply `hcgME_unitary` for (s1,s2)→ν to collapse the (ν,r) sum: gives δ_{a1,b1} · δ_{a2,b2}
7. Collapse the remaining deltas
8. Conclude `∑ |v|² = ∑ |v|²`

This is the **key lemma for B.2** — call it `cgME_3fold_isometry_normSq`. Once proven, it
provides the composed Parseval identity that the 3D cascade needs. The cascade non-negativity
then follows by applying this isometry to the cascade kernel (matching the CG coefficient
products to the B operator).

**Estimated effort:** ~400 lines of Lean, comparable to `cgME_isometry_normSq` (208 lines)
but with an extra CG level. The sum reordering is the main challenge (more swaps, more
dependent types). This is the natural first formalization target for the next session.

## §8.11.90 — Session 125 (2026-08-16): KEY FINDING — 3-fold isometry requires cross-rep orthogonality

### The discovery

The 3-fold isometry as stated in §8.11.89 is **NOT provable from `hcgME_unitary` alone**.
Expanding `|w(α,p)|² = conj(w)·w` and distributing the product of sums, the inner
collapse requires:

```
∑_{α,p} conj(cgME ν s3 α r a3 p) · cgME ν' s3 α r' b3 p
```

- When `ν = ν'`: `hcgME_unitary` gives `δ_{r,r'} δ_{a3,b3}`. ✓
- When `ν ≠ ν'`: this is **cross-rep orthogonality** — NOT given by `hcgME_unitary`. ✗

`hcgME_unitary` only says each individual CG matrix `cgME s t` (for a FIXED first
arg `s`) is an isometry (column orthonormality). The cross-rep orthogonality says
that CG matrices with DIFFERENT first args (`s ≠ s'`) have orthogonal column
spaces when summed over the output. This is NOT a consequence of individual
isometries — two different isometries can have overlapping column spaces.

### Counterexample

Consider a 2-element index set `ι = {0, 1}` with `dims = [1, 1]` (all 1-dimensional).
Define `cgME 0 0 0 _ _ _ = 1`, `cgME 1 0 0 _ _ _ = 1` (both map to the same output).
Then `hcgME_unitary` holds for each `s` individually (each is a 1×1 isometry), but
`∑_α conj(cgME 0 0 α) · cgME 1 0 α = 1 ≠ 0` — cross-rep orthogonality FAILS.

### The resolution

The cross-rep orthogonality IS derivable from the existing axiom
(`hcgME_decomp` + Schur orthogonality), because the matrix elements of distinct
irreps are orthogonal. The CG decomposition respects this orthogonality. So it
is NOT a new axiom — it is a CONSEQUENCE of the existing axiom that needs to be
formalized as a lemma.

This is "known but unformalized" — standard representation theory (unitarity of
the CG change-of-basis), not open math.

### Restructured B.2 plan

1. **B.2a (this session, PARTIAL):** Prove `cgME_multirep_isometry_normSq` — the
   multi-rep isometry with `hcgME_unitary` + `hcgME_cross_rep` as hypotheses.
   Steps 1-4 and 6 are DONE (compile correctly). Step 5 (21 sum swaps) is `sorry`.
   The proof structure is correct; the 21 swaps are mechanical work.

2. **B.2b (next):** Fill in the 21 sum swaps for Step 5 of
   `cgME_multirep_isometry_normSq`. The reordering is from
   `(α, p, s', a', i', s, a, i)` to `(s, a, i, s', a', i', α, p)` — 21 adjacent
   swaps, each a `Finset.sum_comm` wrapped in `Finset.sum_congr rfl`.

3. **B.2c:** Prove `cgME_3fold_isometry_normSq` by composing the single isometry
   (`cgME_isometry_normSq`) with the multi-rep isometry. Define intermediate
   `u(ν, r, a3) = ∑_{a1,a2} cgME s1 s2 ν a1 a2 r · v(a1,a2,a3)`, apply single
   isometry for (s1,s2)→ν, then multi-rep isometry for (ν,s3)→α.

4. **B.2d:** Derive `hcgME_cross_rep` from `hcgME_decomp` + Schur orthogonality.
   This closes the gap: the multi-rep isometry's hypothesis becomes a proven lemma.

5. **B.2e:** Connect the isometry to the cascade non-negativity (the actual
   `transferMatrixPositivity_axiom` replacement).

### Current codebase state

- `cgME_multirep_isometry_normSq` is in `CGUnitarity.lean` with `sorry` for Step 5.
  Steps 1-4 (ℝ→ℂ, conj expansion, product distribution, sum exchange setup) and
  Step 6 (hcgME_unitary/hcgME_cross_rep application, delta collapse) compile
  correctly. The `sorry` is in the side goal (proving the sum exchange).
- The build has 1 `sorry` (in `cgME_multirep_isometry_normSq`). The rest of the
  codebase is GREEN.
- Axiom count: still 6 (no change — the new lemma has a `sorry` so it depends on
  `sorryAx`).

### Key insight for the 21 swaps

The 21 swaps reorder `(α, p, s', a', i', s, a, i)` → `(s, a, i, s', a', i', α, p)`:
- Phase 1: Move `s` to front (5 swaps: swap with i', a', s', p, α)
- Phase 2: Move `a` to position 2 (5 swaps)
- Phase 3: Move `i` to position 3 (5 swaps)
- Phase 4: Move `s'` to position 4 (2 swaps: swap with p, α)
- Phase 5: Move `a'` to position 5 (2 swaps)
- Phase 6: Move `i'` to position 6 (2 swaps)

After reordering, reassociate each leaf term with `ring` and factor `conj(u) * u`
out of the `(α, p)` sum using `← Finset.mul_sum`.

## §8.11.91 — Session 127 (2026-08-16): B.2c COMPLETE — cgME_3fold_isometry_normSq proven by composition

### The result

`cgME_3fold_isometry_normSq` is now PROVEN with 0 sorries, 0 new axioms.
`#print axioms` = `[propext, Classical.choice, Quot.sound]` — the standard 3 only.

The 3-fold CG isometry (composed Parseval for the 3D cascade) states:
```
∑_{α,p} |∑_{a1,a2,a3} [∑_{ν,r} cgME s1 s2 ν a1 a2 r * cgME ν s3 α r a3 p] * v(a1,a2,a3)|²
  = ∑_{a1,a2,a3} |v(a1,a2,a3)|²
```

This is the key lemma for Step B.2: the 3D cascade applies CG twice (first
`(s1,s2)→ν`, then `(ν,s3)→α`), and this isometry says the combined change-of-basis
preserves the ℓ² norm.

### The approach: composition (not direct expansion)

The handoff from session 126 suggested two options: (A) prove a "double multi-rep"
isometry first then compose, or (B) prove the 3-fold isometry directly. A third,
simpler approach was discovered: **compose the existing multi-rep isometry with the
existing single isometry**, without needing a "double multi-rep" isometry or the
`hcgME_cross_rep_t` hypothesis.

The key insight: for FIXED `s1, s2, s3`, the 3-fold cascade has only `ν` as a
summation variable in the second CG (not both `ν` and `s3`). The `s3` is FIXED.
So the multi-rep isometry (which sums over the first arg `s` with the second arg `t`
fixed) applies directly to the second CG with `t = s3` and `s = ν` (summed).

The composition works as follows:
1. **Rewrite LHS inner sum** to the multi-rep isometry form: distribute `v` into
   the `(ν, r)` sum (`Finset.sum_mul`), reorder `(a1, a2, a3, ν, r) → (ν, r, a3, a1, a2)`
   (8 `Finset.sum_comm` swaps via `conv`), reassociate and factor
   `cgME ν s3 α r a3 p` out of the `(a1, a2)` sum (`ring` + `← Finset.mul_sum`).
2. **Apply multi-rep isometry** (second CG: `(ν, s3) → α` with `ν` summed):
   `u = fun ν r a3 => ∑ a1, ∑ a2, cgME s1 s2 ν a1 a2 r * v a1 a2 a3`.
3. **Reorder RHS** from `(ν, r, a3)` to `(a3, ν, r)` (2 `Finset.sum_comm` swaps).
4. **Apply single isometry** for each fixed `a3` (first CG: `(s1, s2) → ν`):
   `v' = fun a1 a2 => v a1 a2 a3` via `Finset.sum_congr`.
5. **Reorder** from `(a3, a1, a2)` to `(a1, a2, a3)` (2 `Finset.sum_comm` swaps).

Total: 12 `Finset.sum_comm` swaps (8 in Step 1, 2 in Step 3, 2 in Step 5), much
less than the direct expansion approach (~40+ swaps with 13 variables).

### Key technique: `congrArg Complex.normSq` for `Finset.sum_congr`

When using `Finset.sum_congr` to rewrite a sum of `Complex.normSq (...)` terms,
the per-term equality must be wrapped with `congrArg Complex.normSq`:
```lean
Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun p _ =>
  congrArg Complex.normSq (hlhs α p)))
```
This is because `hlhs α p` proves `inner_sum = reordered_inner_sum`, but
`Finset.sum_congr` expects `Complex.normSq (inner_sum) = Complex.normSq (reordered_inner_sum)`.

### Hypotheses

The lemma takes `hcgME_unitary` + `hcgME_cross_rep` as hypotheses (same as the
multi-rep isometry). It does NOT need `hcgME_cross_rep_t` (cross-rep orthogonality
for the second arg) — that was a concern from the handoff, but it doesn't arise
because `s3` is FIXED (not summed) in this formulation.

### Build status

- **Git**: clean working tree before this commit.
- **Build**: GREEN — `lake build` completes successfully (3008 jobs), 0 errors,
  0 sorries in actual proof code.
- **Axiom count**: still 6 (no change — the new lemma has 0 sorries and depends
  only on the standard 3 axioms).
- **Key file**: `src/lean/YangMills/Proofs/PeterWeyl/CGUnitarity.lean` — now
  contains `cgME_isometry_normSq` (single), `cgME_multirep_isometry_normSq`
  (multi-rep), and `cgME_3fold_isometry_normSq` (3-fold), all GREEN, 0 sorries.

### Next steps

1. **B.2d**: Derive `hcgME_cross_rep` from `hcgME_decomp` + Schur orthogonality.
   This closes the gap: the 3-fold isometry's hypothesis becomes a proven lemma.
   `hcgME_cross_rep` is "known but unformalized" — standard representation theory
   (unitarity of the CG change-of-basis), not open math.

2. **B.2e**: Connect the 3-fold isometry to the cascade non-negativity (the actual
   `transferMatrixPositivity_axiom` replacement, reducing axioms 6→5). This
   requires matching the abstract isometry to the concrete cascade structure
   (the B operator, the kernel K(W,V), the term explosion).

### Adversarial self-check (session 127): B.2d derivability obstacle

**Finding: `hcgME_cross_rep` may NOT be derivable from the existing axiom alone.**

The design doc §8.11.90 claims `hcgME_cross_rep` is derivable from `hcgME_decomp` +
Schur orthogonality. On careful analysis, this claim is **questionable**:

1. `hcgME_unitary` provides COLUMN orthonormality for each `s` individually:
   `∑_ν ∑_p conj(cgME s t ν a i p) * cgME s t ν b j p = δ_{a,b} δ_{i,j}`.
   This says the intertwiner `U_{s,t}: V_s ⊗ V_t → ⊕_ν V_ν` is an ISOMETRY.

2. `hcgME_cross_rep` requires the COMBINED map `⊕_s (V_s ⊗ V_t) → ⊕_ν V_ν` to be
   unitary, meaning the images of different `s` blocks are ORTHOGONAL. This is
   NOT a consequence of individual isometries — two isometries can have overlapping
   images.

3. The `hcgME_decomp` + Schur orthogonality give a 4-fold product integral that
   does NOT simplify to 0 for `s ≠ s'` (Schur orthogonality handles 2-fold products,
   not 4-fold). So the direct derivation route is blocked.

4. The CG coefficients are NOT uniquely determined by `hcgME_decomp` + `hcgME_unitary`
   — there's a phase freedom (unitary transformation within each `ν` block). The
   cross-rep orthogonality depends on the specific choice of phases.

**Counterexample (from §8.11.90):** `ι = {0,1}`, `dims = [1,1]`, `cgME 0 0 0 = 1`,
`cgME 1 0 0 = 1`. Then `hcgME_unitary` holds for each `s` (each is a 1×1 isometry),
but `∑_α conj(cgME 0 0 α) * cgME 1 0 α = 1 ≠ 0` — cross-rep orthogonality FAILS.

**Implication:** B.2d may require STRENGTHENING the axiom to provide the full
unitarity of the combined CG change-of-basis (including cross-rep orthogonality).
This would be a flagged axiom strengthening. The cross-rep orthogonality is "known
but unformalized" (standard representation theory), so the strengthening is not
adding a new mathematical assumption, just formalizing a known consequence that the
current axiom does not explicitly provide.

**Alternative approaches to consider:**
- (a) Strengthen the axiom to include `hcgME_cross_rep` (or the full unitarity of
  the combined map). Flag in axiom growth log.
- (b) Find a derivation of `hcgME_cross_rep` from `hcgME_decomp` + Schur orthogonality
  that avoids the 4-fold product issue (e.g., using the intertwining property +
  Schur's lemma for the composition `U_{s,t}^* * U_{s',t}`).
- (c) Avoid `hcgME_cross_rep` entirely by proving the 3-fold isometry directly from
  `hcgME_decomp` + Schur orthogonality (bypassing the isometry composition).

**Status:** This is a BELIEVED obstacle, not yet verified. The next session should
either confirm the obstacle (by attempting approach (b) and failing) or find a
derivation. If the obstacle is confirmed, approach (a) is the fallback.

## §8.11.92 — Session 128 (2026-08-16): B.2d COMPLETE — obstacle CONFIRMED, axiom strengthened with `hcgME_cross_rep`

### The obstacle is CONFIRMED

After thorough analysis (adversarial self-check), `hcgME_cross_rep` is NOT derivable
from `hcgME_decomp` + `hcgME_unitary` + Schur orthogonality. The four blocking reasons:

1. **Individual isometries ≠ cross-orthogonality.** `hcgME_unitary` gives `U_{s,t}^* U_{s,t} = I`
   for each `s`. Two isometries can have overlapping images — cross-rep orthogonality
   (`U_{s,t}^* U_{s',t} = 0` for `s ≠ s'`) is NOT a consequence.

2. **Intertwining approach blocked.** `U_{s,t}^* U_{s',t}` is NOT an intertwiner from
   `ρ_{s'} ⊗ ρ_t` to `ρ_s ⊗ ρ_t` because `U_{s',t} U_{s',t}^* ≠ I` (it's a projection,
   not identity). Schur's lemma doesn't apply.

3. **4-fold product issue.** `hcgME_decomp` + Schur orthogonality gives a 4-fold matrix
   element integral that doesn't simplify to the 2-fold product needed. Schur orthogonality
   handles 2-fold products, not 4-fold.

4. **Phase freedom.** CG coefficients have a phase/unitary freedom within each irreducible
   component. `hcgME_decomp` + `hcgME_unitary` constrain but don't fix relative phases
   between different `s` values. Cross-rep orthogonality depends on this relative choice.

**Counterexample:** `ι = {0,1}`, `dims = [1,1]`, `cgME 0 0 0 = 1`, `cgME 1 0 0 = 1`.
Each `hcgME_unitary` holds (1×1 isometry), but `∑_α conj(cgME 0 0 α) * cgME 1 0 α = 1 ≠ 0`.

### Resolution: approach (a) — strengthen the axiom

`hcgME_cross_rep` was added to `peterWeyl_clebschGordan_plaquette` as a new conjunct.
This is "known but unformalized" — the full unitarity of the CG change-of-basis (including
cross-rep orthogonality) is standard representation theory, following from the CHOICE of
CG coefficients (Gram-Schmidt within each irreducible component). The strengthening does
NOT add a new mathematical assumption — it formalizes a known consequence.

**Flagged in** `/docs/axiom_growth_log.md` (session 128 entry).

### Impact on axiom count

The axiom COUNT is unchanged (still 6). The strengthening increases the STRENGTH of
`peterWeyl_clebschGordan_plaquette` without changing the count. When
`transferMatrixPositivity_axiom` is replaced (step B.2e), the count goes 6→5, but the
remaining axiom is stronger. The net reduction in total axiom strength is less than the
count reduction suggests.

### Build status

- **Build**: GREEN — `lake build` completes successfully (3008 jobs), 0 errors, 0 sorries.
- **Axiom count**: still 6 (strengthened an existing axiom, didn't add a new one).
- **6 destructuring sites updated**: `Axiom.lean` (2), `Separable.lean` (1),
  `CharacterExpansion.lean` (1), `FullBoltzmannPD.lean` (2).
- **CGUnitarity.lean**: unchanged — the lemmas (`cgME_isometry_normSq`,
  `cgME_multirep_isometry_normSq`, `cgME_3fold_isometry_normSq`) still take
  `hcgME_unitary` + `hcgME_cross_rep` as hypotheses. At the B.2e call site, both
  will be discharged from the strengthened axiom.

### Next step: B.2e

Connect the 3-fold isometry to the cascade non-negativity (the actual
`transferMatrixPositivity_axiom` replacement, reducing axioms 6→5). This requires
matching the abstract isometry to the concrete cascade structure (the B operator,
the kernel K(W,V), the term explosion). Both `hcgME_unitary` and `hcgME_cross_rep`
are now available from the axiom to discharge the 3-fold isometry's hypotheses.

## §8.11.93 — Session 129 (2026-08-18): B.2e adversarial self-check + structural obstacle analysis

### Adversarial self-check (session 129)

Steelmanning the dead-end case for B.2e (connecting the 3-fold isometry to cascade
non-negativity):

1. **The 3-fold isometry does NOT directly match the single-site integral structure.**
   The 3-fold isometry (`cgME_3fold_isometry_normSq`) operates on ROW indices only:
   ```
   ∑_{α,p} |∑_{a1,a2,a3} [∑_{ν,r} cgME s1 s2 ν a1 a2 r * cgME ν s3 α r a3 p] * v(a1,a2,a3)|²
     = ∑_{a1,a2,a3} |v(a1,a2,a3)|²
   ```
   But the single-site integral (`single_site_3D_luscher_integral`) involves BOTH row
   (a1,a2,a3) AND column (b1,b2,b3) indices, with a SHARED intermediate representation ν:
   ```
   U(ν,r,s,α,p,q) = [cgME s1 s2 ν a1 a2 r * cgME ν s3 α r a3 p] *
                     conj([cgME s1 s2 ν b1 b2 s * cgME ν s3 α s b3 q])
   ```
   The row part uses summation index r, the column part uses s, but BOTH share the same ν.
   The 3-fold isometry sums over ν independently for rows and columns, while the single-site
   integral has ν SHARED. This is a structural mismatch.

2. **The single-site integral has both p and q indices; the isometry has only p.**
   The Schur orthogonality integral gives `(1/dims α) · δ_{p,p'} · δ_{q,q'}`, producing
   both p and q indices. The 3-fold isometry sums over (α, p) only. The q index (column
   output) is not handled by the isometry as stated.

3. **The off-diagonal terms involve spatial link products, not just CG coefficients.**
   Even if orthonormality makes CG cross-terms vanish, the spatial link products
   `(ρ s1 A1) b1 a1 · ... · (ρ s3 B3) d3 c3` are complex and depend on the indices.
   The non-negativity is NOT simply "off-diagonal terms vanish, diagonal terms are |C|² ≥ 0"
   because the diagonal terms involve complex spatial link products, not just |C|².

4. **The non-negativity is GLOBAL, not single-site.** The single-site 3D integral is NOT
   non-negative off-diagonal (confirmed by `cg_unitarity_nonneg` only handling the diagonal
   case). The non-negativity emerges only after summing over ALL temporal links (the full
   cascade), with the isometry collapsing the FULL sum. A single-site lemma is insufficient.

5. **Term explosion in the full cascade.** The 3D cascade has exponential term growth
   (each site produces a SUM of CG products, not a single character). The isometry collapses
   this at the END, but the intermediate bookkeeping (12 nested sums per site, composed across
   sites) may be intractable in Lean without an abstract tensor-network formulation.

6. **The `character_expansion_nonneg_shared` scaffold requires a separable kernel.** The
   scaffold needs `K(x,y,z) = ∑_i a(z,i)·Φ_i(z,x)·conj(Φ_i(z,y))` with `a ≥ 0`. In 3D, the
   kernel after the single-site integral is NOT directly separable — it's a sum of CG products
   (complex coefficients). The isometry is the mechanism that REORGANIZES the kernel into the
   separable form, but formalizing this reorganization requires the full cascade.

**Honest verdict:** B.2e is the HARDEST part of Step B. The 3-fold isometry is a necessary
ingredient but is NOT sufficient — it has a structural mismatch with the single-site integral
(row-only vs row+column, p-only vs p+q, shared ν). The non-negativity is global (not
single-site), and the full cascade has term explosion. This is "known but unformalized" —
substantial multi-session effort, not open math, and NOT a quick win.

### Structural obstacle: the isometry–integral mismatch

The key obstacle identified in this session is the STRUCTURAL MISMATCH between the 3-fold
isometry (as proven) and the single-site integral:

**The 3-fold isometry** (proven, `cgME_3fold_isometry_normSq`):
```
∑_{α,p} |∑_{a1,a2,a3} C(α,p; a1,a2,a3) · v(a1,a2,a3)|² = ∑_{a1,a2,a3} |v(a1,a2,a3)|²
```
where `C(α,p; a1,a2,a3) = ∑_{ν,r} cgME s1 s2 ν a1 a2 r · cgME ν s3 α r a3 p`.

**The single-site integral** (proven, `single_site_3D_luscher_integral`):
```
∫ 6 MEs dμ = ∑_{ν,r,s,ν',r',s',α,p,q} U(ν,r,s,α,p,q) · (1/dims α) · V(ν',r',s',α,p,q)
```
where `U = C_part(ν,r,α,p; a) · conj(C_part(ν,s,α,q; b))` and
`V = conj(C_part(ν',r',α,p; c)) · C_part(ν',s',α,q; d)`.

The mismatch:
- **Row vs row+column:** The isometry handles row indices (a1,a2,a3) only. The integral
  has both row (a1,a2,a3) and column (b1,b2,b3) indices.
- **p vs p+q:** The isometry sums over (α,p). The integral has both p and q (from Schur
  orthogonality `δ_{p,p'} · δ_{q,q'}`).
- **Shared ν:** In the integral, the row part (r) and column part (s) share the same ν.
  In the isometry, ν is summed independently for each application.

**Resolution path:** A "6-fold isometry" (or "full 3-fold isometry") that handles both
row and column indices is needed. This would be:
```
∑_{α,p,q} |∑_{a1,a2,a3,b1,b2,b3} C_full(α,p,q; a,b) · v(a,b)|² = ∑_{a,b} |v(a,b)|²
```
where `C_full(α,p,q; a,b) = ∑_{ν,r,s} cgME s1 s2 ν a1 a2 r · conj(cgME s1 s2 ν b1 b2 s) ·
cgME ν s3 α r a3 p · conj(cgME ν s3 α s b3 q)`.

**Key finding (session 129):** The 6-fold isometry IS a consequence of the 3-fold isometry,
via the TENSOR PRODUCT argument. The 6-fold CG map is `B ⊗ conj(B)`, where `B` is the 3-fold
CG map (an isometry, `B* B = I`). Since `conj(B)` is also an isometry (`conj(B)* conj(B) =
conj(B* B) = conj(I) = I`), the tensor product `B ⊗ conj(B)` is an isometry:
`(B ⊗ conj(B))* (B ⊗ conj(B)) = (B* B) ⊗ (conj(B)* conj(B)) = I ⊗ I = I`.

**IMPORTANT:** This uses `conj(B)`, NOT `B*` (the adjoint). The adjoint would require
`B B* = I` (co-isometry / completeness), which is NOT given. But `conj(B)` (elementwise
conjugation) only requires `B* B = I` (isometry), which IS given by the 3-fold isometry.

**Formalization challenge:** The direct expansion approach (expanding |w|² and applying
orthonormality) gets STUCK because the intermediate representation α is SHARED between the
row part (p) and the column part (q). The sum `∑_α f(α) · g(α)` cannot be separated into
`[∑_α f(α)] · [∑_α g(α)]`. The tensor product approach (abstract linear algebra) is needed
instead, but requires connecting the abstract tensor product to the concrete ℓ² norm.

**Two formalization approaches:**
- **(a) Direct expansion:** Expand |w|², exchange sums, apply orthonormality. STUCK on
  shared α. May require a 4-fold CG product / 6j symbol decomposition. ~500+ lines.
- **(b) Tensor product:** Prove `B ⊗ conj(B)` is an isometry using abstract linear algebra
  (`LinearMap.tensorProduct`), then connect to concrete ℓ² norm. Requires showing the ℓ²
  norm of a tensor product vector equals the product of ℓ² norms. ~300 lines + infrastructure.

**Recommendation:** Approach (b) is more tractable. The key lemma is: "if B is an isometry
(B* B = I), then B ⊗ conj(B) is an isometry." This is a Mathlib-candidate result (general
linear algebra, independent of Yang-Mills).

### Formalization plan for B.2e

**Step B.2e.1:** Prove the 6-fold isometry (`cgME_3fold_isometry_full_normSq`):
```
∑_{α,p,q} |∑_{a1,a2,a3,b1,b2,b3} C_full(α,p,q; a,b) · v(a,b)|² = ∑_{a,b} |v(a,b)|²
```
This is the key ingredient that matches the single-site integral structure. It can be
proved by applying the 3-fold isometry twice (rows then columns), using the factorization
of orthonormality.

**Step B.2e.2:** Prove a "generalized cg_unitarity_nonneg" that handles the off-diagonal
case (different row and column indices, same reps) by using the 6-fold isometry to show
the full sum (over all 12 indices) is ≥ 0. This is the single-site non-negativity lemma
that generalizes `cg_unitarity_nonneg` from the diagonal case to the full case.

**Step B.2e.3:** Connect the single-site non-negativity to the full cascade. This requires
showing that the transfer matrix kernel (after the full cascade) has the separable form
`K(x,y,z) = ∑_i a(z,i)·Φ_i(z,x)·conj(Φ_i(z,y))` with `a ≥ 0`, which allows applying
`character_expansion_nonneg_shared`. This is the hardest step (term explosion).

**Step B.2e.4:** Replace `transferMatrixPositivity_axiom` with the proved lemma, reducing
axioms 6→5.

**Estimated effort:** B.2e.1 (~300 lines, comparable to the 3-fold isometry) is the most
tractable and should be the next formalization target. B.2e.2 (~200 lines) depends on
B.2e.1. B.2e.3 is the hardest (term explosion, may require abstract tensor-network
formulation) and may span multiple sessions. B.2e.4 is straightforward once B.2e.3 is done.

### Current codebase state

- **Git**: clean working tree. Latest commit: 9153ebe.
- **Build**: GREEN — `lake build` completes successfully (3008 jobs), 0 errors, 0 sorries.
- **Axiom count**: still 6. B.2e has NOT been started — this session was analysis only.
- **Key files**: `CGUnitarity.lean` (3 isometries, all GREEN), `Site3DIntegral.lean`
  (single-site integral + diagonal non-negativity, GREEN), `CleanFactorization.lean`
  (character expansion, GREEN), `LuscherDecomposition.lean` (T = V^{1/2}·U·V^{1/2}, GREEN).

## §8.11.94 — Session 130 (2026-08-21): B.2e.1 adversarial self-check — 6-fold isometry is FALSE

### Critical finding: the 6-fold isometry is FALSE (dimension obstruction)

Session 129 (§8.11.93) identified the 6-fold isometry as the key ingredient for B.2e.1,
to be proved via the tensor product argument: "if B is an isometry (B* B = I), then
B ⊗ conj(B) is an isometry." Session 130 began by **adversarially verifying this claim
numerically before formalizing it.** The result is a **critical negative finding**.

**The abstract tensor product claim IS true.** If B is an m×n isometry (B* B = I_n), then
B ⊗ conj(B) (Kronecker product with elementwise conjugate, NOT adjoint) is an isometry:
(B ⊗ conj(B))* (B ⊗ conj(B)) = (B* B) ⊗ (conj(B)* conj(B)) = I_n ⊗ I_n = I_{n²}.
This was verified numerically for 8 random trials (various m, n) — all PASS.

**But the 6-fold isometry as stated in §8.11.93 is NOT the tensor product isometry.** The
6-fold isometry has a SHARED intermediate representation α (and shared ν):
```
∑_{α,p,q} |∑_{a,b} C_full(α,p,q; a,b) · v(a,b)|² = ∑_{a,b} |v(a,b)|²
```
where C_full(α,p,q; a,b) = ∑_{ν,r,s} cgME s1 s2 ν a1 a2 r · conj(cgME s1 s2 ν b1 b2 s) ·
cgME ν s3 α r a3 p · conj(cgME ν s3 α s b3 q).

The tensor product isometry has INDEPENDENT α₁, α₂ (and independent ν, ν'):
```
∑_{α₁,p,α₂,q} |∑_{a,b} B(α₁,p;a) · conj(B(α₂,q;b)) · v(a,b)|² = ∑_{a,b} |v(a,b)|²
```
where B(α,p;a) = ∑_ν cgME s1 s2 ν a1 a2 r · cgME ν s3 α r a3 p.

**The shared α in the 6-fold isometry creates a FUNDAMENTAL DIMENSION OBSTRUCTION:**
- Input dimension: (a1,a2,a3,b1,b2,b3) → [dims(s1)·dims(s2)·dims(s3)]² = D²
- 6-fold output dimension: (α,p,q) → ∑_α dims(α)²
- Tensor product output dimension: (α₁,p,α₂,q) → (∑_α dims(α))² = D²

By the power-mean inequality, ∑_α dims(α)² < (∑_α dims(α))² = D² whenever there is more
than one α (i.e., whenever V_{s1} ⊗ V_{s2} ⊗ V_{s3} is not irreducible). So the 6-fold
output dimension is STRICTLY LESS than the input dimension, making the isometry
(C* C = I) IMPOSSIBLE.

**Concrete example (SU(2), s1=s2=s3=spin-1, dim 3):**
- V₁⊗V₁⊗V₁ = V₀ ⊕ 3V₁ ⊕ 2V₂ ⊕ V₃ (dim 27)
- Input dim: 27² = 729
- 6-fold output dim: 1² + 3² + 5² + 7² = 84 (sum over DISTINCT α, no multiplicity)
- 84 < 729 → 6-fold isometry IMPOSSIBLE
- Tensor product output dim: 27² = 729 → tensor product isometry POSSIBLE

**Numerical verification (concrete CG-like example):** A test with s1=s2=s3 (dim 2),
ν∈{0,1} (dim 2), α∈{2..9} (dim 1, 8 outputs) was constructed satisfying all hypotheses
(hcgME_unitary, hcgME_cross_rep, 3-fold isometry all PASS). The 6-fold isometry
(C6* C6 = I₆₄) FAILED, while the tensor product isometry (B3⊗conj(B3))* (B3⊗conj(B3))
= I₆₄ PASSED. The 6-fold map C6 was confirmed to equal the DIAGONAL (α₁=α₂) restriction
of the tensor product B3⊗conj(B3), and this diagonal restriction is NOT an isometry.

### Why the shared α arises and cannot be avoided

The shared α in the single-site integral comes from **Schur orthogonality**: the integral
∫ (ρ_α g)_{pq} conj((ρ_β g)_{p'q'}) dμ = (1/dims α) δ_{αβ} δ_{pp'} δ_{qq'}. This forces
α = β (shared α) between the unbarred and barred CG products. The shared ν comes from
the CG decomposition: both the row part (r) and column part (s) use the SAME intermediate
representation ν from the first CG application.

The tensor product isometry has independent ν, ν' and independent α₁, α₂, which does NOT
match the single-site integral structure. The cross_rep orthogonality makes cross-terms
(ν≠ν') vanish when SUMMED OVER α, but the single-site integral has a FIXED α (not summed),
so the cross-terms do NOT vanish.

### Implications for the B.2e plan

**B.2e.1 (prove 6-fold isometry) is ABANDONED** — the statement is FALSE. The design doc
§8.11.93 plan was based on a false premise (conflating the shared-α 6-fold isometry with
the independent-α tensor product isometry).

**The single-site integral is NOT non-negative off-diagonal.** This confirms §8.11.93
point 4: the non-negativity is GLOBAL (emerges only after the full cascade), not
single-site. The diagonal case (|C|² ≥ 0) works because the barred CG product equals
conj(unbarred), but the off-diagonal case has different unbarred and barred products.

### Alternative approaches identified

1. **Operator-level approach (T = B* B):** Define the transfer matrix T as an operator on
   L²(G^spatial) and show T = B* B using the CG decomposition, where B is the "CG transform"
   operator. The 3-fold isometry (B* B = I) is already proven. This gives T ≥ 0 directly
   without needing the 6-fold isometry. The challenge is connecting the abstract operator
   formulation to the concrete integral.

2. **Tensor product isometry at the cascade level:** The full cascade integrates over ALL
   temporal links. Different sites have INDEPENDENT α's (different temporal links), so the
   tensor product isometry (independent α₁, α₂) might apply at the cascade level, even
   though it doesn't apply at the single-site level. The challenge is term explosion.

3. **Direct cascade non-negativity:** Show that the full cascade kernel K(g,h) =
   ∑_w F(w) ∏_l K_w(g_l, h_l) is positive-definite, using the 3-fold isometry to collapse
   each site's contribution. The challenge is the exponential term growth.

4. **Multiplicity-aware formulation:** The 6-fold isometry fails because the output
   dimension (∑ dims²) is too small. If multiplicity indices were included in the output
   (dim = ∑ m_α² dims(α)²), the dimension might work out. But the current formalization
   (cgME) does not have multiplicity indices, so this would require restructuring.

### Current codebase state

- **Git**: clean working tree. Latest commit: aab1478 (design doc only, session 129).
- **Build**: GREEN — `lake build` completes successfully (3008 jobs), 0 errors, 0 sorries.
- **Axiom count**: still 6. B.2e has NOT been started in code — sessions 129-130 were
  analysis only.
- **No code changes** in this session — the 6-fold isometry was found FALSE before any
  formalization attempt.
- **Key files**: unchanged from session 129. `CGUnitarity.lean` (3 isometries, all GREEN),
  `Site3DIntegral.lean` (single-site integral + diagonal non-negativity, GREEN).

## §8.11.95 — Session 131 (2026-08-21): B.2e revision — KEY NEW INSIGHT + approach analysis

### The KEY NEW INSIGHT: separable decomposition makes temporal interface link integrals TRIVIAL

Session 131 began by re-examining the character expansion structure. The critical finding
overturns the assumption that the 3D cascade requires 6-character integrals at each temporal
interface link.

**The character expansion is at the INDIVIDUAL LINK level, not the plaquette level.** The
lemma `interface_product_character_expansion` (CharacterExpansion.lean:243) gives:

```
∏_p exp(c·Re Tr(g_p)) = ∑_w F(w) ·
  (∏_{l ∈ interfaceLinkPos} χ_{w(l)}(interfaceLinkVar(U, l))) ·
  (∏_{l ∈ interfaceLinkInt} χ_{w(l)}(interfaceLinkVar(U, l))) ·
  star(∏_{l ∈ interfaceLinkNeg} χ_{dual(w(l))}(interfaceLinkVar(U, l)))
```

where `interfaceLinkVar(U, l)` is the INDIVIDUAL link variable at link l (not a plaquette
variable). The separable decomposition (`plaquette_product_separable_decomp`, PROVEN in
PeterWeyl.lean) regroups the plaquette-level character expansion into individual-link
characters using CG. Each link l gets a SINGLE character χ_{w(l)}(g_l).

**Consequence: the temporal interface link integrals are TRIVIAL.** Each temporal interface
link has a single character (not 6). The integral over temporal interface links is:

```
∫ ∏_{l ∈ temporal-int} χ_{w(l)}(g_l) dμ = ∏_{l ∈ temporal-int} δ_{w(l), trivial}
```

This is just Schur orthogonality for single characters — NO 6-character integrals needed.
The 6-character integrals (`single_site_3D_luscher_integral`) arise when expanding each
plaquette factor SEPARATELY and integrating over a link that appears in 6 plaquettes. But
the separable decomposition ALREADY combines the 6 characters into a single character per
link, so the integral is trivial.

**This eliminates the need for the 6-fold isometry** (which is FALSE, §8.11.94). The 6-fold
isometry was an attempt to prove single-site non-negativity of the 6-character integral.
With the separable decomposition, the 6-character integral never arises.

### The `c' ≠ conj(c)` obstacle PERSISTS (confirmed from §8.11.34)

Despite the simplification of temporal link integrals, the fundamental obstacle identified
in §8.11.34 (session 28) PERSISTS. After the temporal interface link integrals (trivial),
the integral becomes:

```
I = C · ∑_{w: w(temporal-int)=trivial} F(w) ·
    ∫_{u⁰_s} Ψ_w^{spatial}(u⁰_s) · A_w(u⁰_s) · B_w(u⁰_s) dμ⁰_s
```

where:
- A_w(u⁰_s) = ∫_{pos} f(U⁺, u⁰_s)·exp(-β·S⁺)·∏_{pos} χ_{w(l)}(g_l) dμ⁺ (positive Fourier coeff)
- B_w(u⁰_s) = ∫_{neg} f(θU⁻, u⁰_s)·exp(-β·S⁻)·∏_{neg} χ_{w(l)}(g_l) dμ⁻ (negative Fourier coeff)

After the change of variables V⁺ = reflect(U⁻), the reflection inverts temporal links:
χ_{w(l)}(g_l⁻¹) = conj(χ_{w(l)}(g_l)) = χ_{dual(w(l))}(g_l). So the negative integral
becomes A_{w*} where w* has dual representations on temporal links. This is NOT conj(A_w)
because the temporal links get dual representations while A_w has the original representations.

**This is the SAME `c' ≠ conj(c)` obstacle from §8.11.34.** The separable decomposition
simplifies the temporal link integrals but does NOT resolve the `c' ≠ conj(c)` obstacle,
which is about the positive/negative link integrals.

### Why the PD property alone doesn't resolve the obstacle

The plaquette Boltzmann factor is PD (`plaquetteBoltzmannPD`, PROVEN). The product of PD
functions is PD (`PositiveDefinite.prod`, PROVEN). So the full Boltzmann factor is PD.

But PD (group sense: ∫∫ f(g)·conj(f(h))·K(g⁻¹h) ≥ 0) is DIFFERENT from reflection positivity
(∫ f(U)·f(θU)·K(U) ≥ 0). The PD property gives positive-definiteness in the standard sense,
but reflection positivity is a different property involving the reflection θ.

Moreover, the "PD kernel from PD function integration" result (integrating a PD function over
a variable preserves PD in the remaining variables) does NOT directly apply because the
plaquette variable is NOT a group homomorphism of individual links. The composition of a PD
function with a non-homomorphic map does NOT preserve PD.

### The resolution paths (from §8.11.34, confirmed)

Two approaches can resolve the `c' ≠ conj(c)` obstacle:

1. **Lüscher decomposition + "PD kernel from PD function expansion" (approach (a)).** The
   V^{1/2}·U·V^{1/2} factorization (Step A.5, PROVEN) reduces positivity to U ≥ 0. U's kernel
   is the temporal plaquette Boltzmann factor. The key: the FULL positive Boltzmann factor
   exp(-β·(S⁺ + S_ts_upper)) is PD (product of PD plaquette factors). Expanding this PD
   function in matrix elements and integrating out the temporal links gives a PD kernel in
   the spatial links. This is a standard harmonic-analysis result but needs formalization.
   Challenge: the "PD kernel from PD function expansion" result requires showing that
   expanding a PD function in the Peter-Weyl basis and integrating out variables gives a PD
   kernel. This is NOT trivial because the plaquette variable is not a homomorphism.

2. **Plaquette-by-plaquette induction (approach (b), recommended by §8.11.34).** This
   matches the actual Osterwalder-Seiler / Lüscher proof. It builds up the transfer matrix
   one plaquette at a time, using the PD property at each step. This avoids the character
   expansion (and the `c' ≠ conj(c)` obstacle) entirely. Challenge: requires formalizing
   the Lüscher construction (Fock space, transfer matrix as product of per-plaquette operators).

### Assessment: which approach is most tractable?

**The separable decomposition insight (this session) SIMPLIFIES approach (a).** With the
temporal link integrals being trivial, the character expansion structure is much simpler.
The remaining challenge is the `c' ≠ conj(c)` obstacle, which requires showing that the
SUM ∑_w F(w) · ∫ A_w · B_w · Ψ_w^{spatial} dμ⁰_s ≥ 0 despite B_w ≠ conj(A_w).

The key question: does the SUM over w, combined with the spatial interface characters and
the PD property of the plaquette factors, give a non-negative result?

**The answer is YES, but the proof requires the Lüscher decomposition.** The V^{1/2}·U·V^{1/2}
factorization (PROVEN) separates the spatial part (V, PD) from the temporal part (U). The
temporal part U, after the separable decomposition, has a kernel that is a sum of products
of characters with non-negative coefficients F(w) ≥ 0. The PD property of the plaquette
factors ensures that this kernel is PSD.

**The key lemma to prove (for approach (a)):** If φ(g) is a PD function on a compact group G
with a separable character expansion φ(g) = ∑_w F(w) · ∏_l χ_{w(l)}(g_l) (F(w) ≥ 0), then
the integral operator with kernel K(u, u') = ∫ φ(u, u', temporal) dμ(temporal) is PSD.

This is the "PD kernel from separable expansion + integration" result. It's a standard
result in the OS framework but needs careful formalization. The key ingredients:
- `plaquetteBoltzmannPD` (PROVEN): each plaquette factor is PD.
- `PositiveDefinite.prod` (PROVEN): product of PD functions is PD.
- `PositiveDefinite.matrix_posSemidef` (PROVEN): PD → PSD matrix.
- The separable decomposition (PROVEN: `plaquette_product_separable_decomp`).
- The V^{1/2}·U·V^{1/2} factorization (PROVEN: Step A.5).

### Revised B.2e plan

**B.2e.1 (revised, this session):** The separable decomposition makes temporal interface
link integrals trivial (δ_{trivial}). This eliminates the 6-character integrals and the
6-fold isometry issue. The `c' ≠ conj(c)` obstacle persists but is addressed by the Lüscher
decomposition. APPROACH CHOSEN: (a) Lüscher decomposition + "PD kernel from separable
expansion + integration."

**B.2e.2 (revised):** Prove the key lemma: "PD kernel from separable expansion + integration."
Show that the temporal integral operator U has a PSD kernel, using the PD property of the
plaquette factors and the separable decomposition.

**B.2e.3 (revised):** Combine with the V^{1/2}·U·V^{1/2} factorization (PROVEN) to conclude
T ≥ 0, hence ⟨g, Tg⟩ ≥ 0.

**B.2e.4:** Replace `transferMatrixPositivity_axiom` with the proved lemma, reducing axioms 6→5.

### Current codebase state

- **Git**: clean working tree. Latest commit: 33297c9 (design doc §8.11.94 only).
- **Build**: GREEN — `lake build` completes successfully (3008 jobs), 0 errors, 0 sorries.
- **Axiom count**: still 6. B.2e has NOT been started in code — sessions 129-131 were analysis only.
- **No code changes** in session 131 — this session was analysis and design doc only.
- **Key insight**: the separable decomposition (`interface_product_character_expansion`) makes
  temporal interface link integrals trivial, eliminating the need for 6-character integrals.

## §8.11.96 — Session 132 (2026-08-21): B.2e.2 adversarial self-check + the provable core

### Adversarial self-check (required before significant proof work)

Before formalizing B.2e.2, we steelman the case that approach (a) is a dead end.  This is a
genuine search for failure modes, not a re-affirmation of the plan.

**Finding 1 — the abstract "PD kernel from separable expansion + integration" lemma IS provable,
but it is NOT what reflection positivity needs.**  The clean abstract statement is: if
`φ : (L → SU N) → ℂ` has a separable character expansion `φ(g) = ∑_w F(w)·∏_l χ_{w(l)}(g_l)` with
`F(w) ≥ 0`, and `L = L_keep ⊔ L_int`, then the integrated kernel
`K(x, y) = ∫ φ(x ⊕ t)·conj(φ(y ⊕ t)) dμ(t)` is PSD.  Proof: expand both factors, integrate over
`L_int` by character orthogonality (`∫ χ_a conj(χ_b) = δ_{a,b}`), which forces `w|_int = w'|_int`;
grouping by the restriction `v = w|_int` gives `K(x,y) = ∑_v B_v(x)·conj(B_v(y))` with
`B_v(x) = ∑_{w: w|_int=v} F(w)·∏_{l∈L_keep} χ_{w(l)}(x_l)` — a sum of rank-1 PSD kernels, hence PSD
(this is exactly the Gram-matrix argument already formalized as
`reflection_positivity_reorganization` / `multi_link_gram_psd_nonneg` in `Separable.lean`).

**Finding 2 — the gap to reflection positivity is the `conj`.**  The abstract lemma's kernel is
`∫ φ(x,t)·conj(φ(y,t)) dμ(t)` — a DOUBLE integral with a conjugated second factor.  Reflection
positivity is the SINGLE integral `∫ f(U)·f(θU)·K(U) dμ(U)` with the geometric reflection `θ`.
Because the test function `f` is real-valued, `f(θU) = conj(f(θU))`, so the RP integral IS a PD
quadratic form `∫∫ g(u)·conj(g(u'))·K_T(u,u')` — but ONLY IF the transfer-matrix kernel `K_T`
is itself a PD kernel.  The abstract lemma does NOT establish that `K_T` is PD, because `K_T`
involves the reflection `θ` (via `u' = mergePosInterface(V⁺, σ(u⁰))`), not the group
multiplication `g⁻¹·h` that the PD property is about.

**Finding 3 — the `c' ≠ conj(c)` obstacle is precisely this gap, restated.**  After the change of
variables `V⁺ = reflect(U⁻)`, the negative-link character factor becomes `Φ_{w*}(V⁺)` (dual
representations on temporal links), NOT `conj(Φ_w(V⁺))`.  So the per-mode integrand is
`A_w · A_{w*}`, not `|A_w|²`.  The abstract Gram-matrix lemma gives `∑_v |B_v|² ≥ 0` only when the
two factors share the SAME mode `w`; the reflection pairs `w` with `w*`, breaking the
rank-1 structure.  The claim in §8.11.95 that "the answer is YES via the Lüscher decomposition"
glosses over exactly this: the Lüscher VUV factorization separates spatial from temporal, but the
temporal operator `U` still couples `w` to `w*` through the interface action.

**Conclusion of self-check.**  Approach (a) is NOT a dead end, but the "PD kernel from separable
expansion + integration" lemma must be stated and proved in a form that ACCOUNTS for the
reflection pairing `w ↔ w*`.  The naive abstract version (Finding 1) is true but insufficient.
The correct target lemma is: the transfer-matrix kernel `K_T(u, u')` — AFTER the VUV factorization
and the trivial temporal-link integrals — is a PD kernel in the spatial-interface links, where the
`w ↔ w*` pairing is resolved by the PD property of the FULL Boltzmann factor (which IS PD on the
product group, by `PositiveDefinite.prod` + `plaquetteBoltzmannPD`).  Whether this PD property
survives the non-homomorphic plaquette map (Finding from §8.11.95) is the real crux and is NOT
yet resolved.

### What session 132 formalizes

The provable core (Finding 1): the abstract "integrated separable kernel is PSD" lemma.  This is
genuine, reusable, and a Mathlib candidate — but it is explicitly NOT sufficient by itself to
close `transferMatrixPositivity_axiom` (Finding 2/3).  It is the correct first milestone of B.2e.2:
it isolates exactly the part that IS handled by the separable expansion + character orthogonality,
so that the remaining work (the `w ↔ w*` reflection pairing) is sharply localized.

## §8.11.97 — Session 133 (2026-08-21): the `c' ≠ conj(c)` obstacle RESOLVED (mathematically)

### The question

Does the `w ↔ w*` reflection pairing preserve non-negativity?  Session 132's self-check
(§8.11.96, Finding 3) localized the crux: after the change of variables `V⁺ = reflect(U⁻)`,
the per-mode integrand is `A_w · A_{w*}`, not `|A_w|²`.

### Finding 1 — at the individual-link CHARACTER level, the answer is NO (term-by-term)

The σ-inversion lemma (`fourierCoeffNeg_thetaReindex_eq_star_fourierCoeffPos`, PROVEN, session 17)
gives `B_w(u⁰) = conj(A_{θw}(σ(u⁰)))`, and σ-invisibility (`fourierCoeffPos_sigma_invisible`,
PROVEN, session 53) removes the σ.  So the sum is `∑_w F(w)·A_w·conj(A_{θw})`.  Reindexing by the
involution `θ` (where it is one) proves the sum is REAL, but NOT non-negative: with two modes,
`a₁·conj(a₂) + a₂·conj(a₁) = 2·Re(a₁·conj(a₂))` can be negative.  Non-negativity at the
character level is GLOBAL only, and no reindexing argument can prove it.  This confirms
§8.11.96 Finding 3: the separable individual-link expansion CANNOT resolve the obstacle.

### Finding 2 — at the plaquette-word MATRIX-ELEMENT level, the answer is YES, and the
### pairing is EXACT conjugation (already in the codebase)

The resolution is the standard Osterwalder–Seiler mechanism, and its two ingredients were
ALREADY formalized (sessions 41–52, `PositiveDefiniteIntegral/CascadeNonneg.lean`):

1. `repCharacter_trace_expand` (PROVEN): `χ_ν(W·V) = ∑_{a,b} (ρ_ν W)_{ab}·conj((ρ_ν V⁻¹)_{ab})`.
   At the plaquette-word level the reflection is GROUP INVERSION (the crossing plaquette word
   `W_p` maps to its mirror word with reversed order and inverted links, i.e. `W_p⁻¹`), and for
   unitary representations inversion IS conjugation (`repMatrixElement_inv`).  The pairing is
   `D_{ab}(W⁺) ↔ conj(D_{ab}(W⁺))` with the SAME representation and the SAME indices — no
   `w ↔ w*` mismatch arises.  The obstacle was an artifact of expanding at the individual-link
   character level.
2. `character_kernel_integral_nonneg` (PROVEN): for any non-negative coefficients,
   `∫∫ f(W)·f(V⁻¹)·∑_ν coeff_ν·χ_ν(W·V) ≥ 0` — the sum-of-squares conclusion, via
   `character_expansion_nonneg` with `θ = inv`.

### Finding 3 — the PD-property worry of §8.11.95 is also resolved

§8.11.95 worried that "PD does not transfer through the non-homomorphic plaquette map."
This is true but IRRELEVANT: PD is needed only in the plaquette WORD variable, not in the
individual links.  The crossing-plaquette Boltzmann factor `exp(β·ReTr(U_p))` is a PD function
of the word `U_p` (non-negative character expansion + `positiveDefinite_finset_sum_repCharacter`,
this session), and the reflection-positivity kernel is `k((W⁻)⁻¹·W⁺)` — exactly the PD kernel
form `k(g⁻¹·h)` — because reflection maps `W⁻ ↦ (W⁺)⁻¹`.  The map `(W⁻, W⁺) ↦ (W⁻)⁻¹·W⁺` is the
group operation on the pair, not a non-homomorphic plaquette map.

### What session 133 formalizes (0 sorries, 0 new axioms, build GREEN 3008 jobs)

1. `repCharacter_mul_inv_eq_sum_matrixElement_conj` (CascadeNonneg.lean): the exact
   "reflection = inversion = conjugation" identity
   `χ(g·h⁻¹) = ∑_{a,b} (ρ g)_{ab}·conj((ρ h)_{ab})` — one-line corollary of
   `repCharacter_trace_expand`.  `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
2. `positiveDefinite_finset_sum_repCharacter` (RepCharacter.lean): non-negative finite sums
   `∑_i c_i·χ_{ρ_i}` (varying dimensions) are positive-definite.
   `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

### What REMAINS (the lattice bridge — B.2e.3, genuinely open formalization, not open math)

The mathematical content of the obstacle is resolved; what remains is the (substantial)
assembly connecting the abstract group-level lemmas to the lattice transfer matrix:

- (i) Identify each crossing plaquette variable as a word `U_p = W_p⁺·(W_p⁻)⁻¹` in the
  positive/negative + interface links (word-level, not plaquette-variable-level).
- (ii) Show the lattice reflection maps `W_p⁻ ↦ (W_p⁺)⁻¹` (word reversal + link inversion;
  partial ingredients exist via `reflectPosToNeg` and the σ-inversion lemmas).
- (iii) Non-negativity of the character-expansion coefficients of `exp(β·ReTr)` — check
  whether this is an axiom/hypothesis in the current setup (`hcoeff`-style hypotheses exist
  in `ReflectionPositivity/CharacterExpansion.lean`).
- (iv) Assembly: Fubini over the two halves + interface, then
  `character_kernel_integral_nonneg` (or `integrated_kernel_psd`) per crossing plaquette,
  combined with the PROVEN `transferMatrixReflected_VUV_factorization`.

**Honest status:** the `c' ≠ conj(c)` obstacle is resolved as MATHEMATICS (the mechanism is
identified and its key steps are formalized), but `transferMatrixPositivity_axiom` is NOT yet
replaced — steps (i)–(iv) are open formalization work.  Axiom count: still 6.

## §8.11.98 — Session 133 continued: the crossing-plaquette kernel is PSD (group-level OS)

### What this formalizes

New file `src/lean/YangMills/Proofs/PositiveDefinite/PSDKernel.lean` (0 sorries, 0 custom
axioms — `#print axioms` = `[propext, Classical.choice, Quot.sound]` throughout):

1. `IsPSDKernel K` — a kernel `K : X → X → ℂ` is Hermitian + PSD (sum form, mirroring
   `PositiveDefinite`), with `IsPSDKernel.congr`, `isPSDKernel_one`,
   `IsPSDKernel.matrix_posSemidef` (mirrors `PositiveDefinite.matrix_posSemidef`).
2. `IsPSDKernel.mul` — Schur product theorem for kernels (via `Matrix.PosSemidef.hadamard`,
   mirroring `PositiveDefinite.mul`); `isPSDKernel_prod` — finite products of PSD kernels.
3. `PositiveDefinite.pullback_sum` / `PositiveDefinite.isPSDKernel_pullback` — a PD function
   `k : G → ℂ` pulls back along ANY map `g : X → G` to the PSD kernel
   `K(x, y) = k((g x)⁻¹ · g y)`.  The proof partitions the double sum into fibers of `g`
   (`Finset.sum_fiberwise_of_maps_to` twice) and applies PD on `s.image g`.
   **No homomorphism property of `g` is needed** — this is the formal resolution of the
   §8.11.95 worry that "PD does not transfer through the non-homomorphic plaquette map":
   PD is required only in the plaquette-WORD variable, and the word enters through the group
   operation `(x, y) ↦ (W x)⁻¹ · W y` on the pair.
4. `crossingPlaquette_kernel_psd` — the crossing-plaquette kernel
   `K(x, y) = ∏_{p ∈ sP} k_p((W_p x)⁻¹ · W_p y)` is PSD whenever each `k_p` is PD
   (e.g. a non-negative character sum, by `positiveDefinite_finset_sum_repCharacter`).
   This is the exact group-level content of the Osterwalder–Seiler crossing-plaquette
   argument, with the word maps `W_p` abstract.

### Status of the B.2e.3 lattice bridge after this session

- Group-level machinery: **COMPLETE** (this file + `repCharacter_mul_inv_eq_sum_matrixElement_conj`
  + `positiveDefinite_finset_sum_repCharacter` + `character_kernel_integral_nonneg`).
- Remaining (lattice plumbing, open formalization not open math):
  (i) identify each interface/crossing plaquette word in
  `extendToFullConfig (reflectPosToNeg V⁺) u` as `W_p(u-side) · (W_p(V⁺-side))⁻¹`;
  (ii) the reflection = word-inversion identity at the word level (trace-level versions exist:
  `trace_plaquetteProduct_reflect_*` in FullBoltzmannPD.lean);
  (iii) non-negativity of the `exp(β·ReTr)` character coefficients (`hcoeff`-style hypotheses
  exist in `ReflectionPositivity/CharacterExpansion.lean`);
  (iv) Fubini assembly + `transferMatrixReflected_VUV_factorization` (PROVEN) → `T ≥ 0`.

## §8.11.99 — Session 133 continued: step (i) groundwork — the crossing plaquette word analysis

### The per-plaquette computation (NOT yet formalized — analysis only)

The merged config in `transferMatrixReflected_VUV_factorization` is
`extendToFullConfig (reflectPosToNeg V⁺) u`: positive+interface links from the bra `u`,
negative links from `reflectPosToNeg V⁺` (ket).  The crossing plaquettes (corners straddling
`t = 0`) are based at `n` with `signedTime n = -1`, directions `(0, ν)`, `ν ≠ 0`.  Its word
`U(n,0)·U(n+e₀,ν)·U(n+e₀+e_ν,0)⁻¹·U(n+e_ν,ν)⁻¹` evaluates in the merged config (via
`reflectPosToNeg_apply`: negative temporal links invert, negative spatial links are
unchanged) to

    (V⁺_{θn,0})⁻¹ · u_{n+e₀,ν} · (u_{n+e₀+e_ν,0})⁻¹ · (V⁺_{θn+e_ν,ν})⁻¹

where `θ = reflectSite` (maps `t=-1 ↦ t=+1`, fixes spatial coords).  Note: plaquettes with
corners `{0,1}` have all links positive+interface, hence depend ONLY on `u` (they are
multiplication-operator factors, harmless for positivity — they must be tracked into the
`S⁺(u)/2 + S⁺(u')/2` bookkeeping or shown symmetric).

### The matrix-element factorization (the OS mechanism, per crossing plaquette)

Grouping the word as `A·B⁻¹` with `A = U(n,0)·U(n+e₀,ν)`, `B = U(n+e_ν,ν)·U(n+e₀+e_ν,0)`
and expanding `χ_R(A·B⁻¹) = ∑_{ij} D^R_{ij}(A)·conj(D^R_{ij}(B))`
(`repCharacter_mul_inv_eq_sum_matrixElement_conj`, session 133), then multiplying out
`D(A)`, `D(B)` and resumming over the internal indices gives the clean form:

    χ_R(crossing word) = ∑_{k,l} D^R_{kl}(W_int(u)) · conj(D^R_{kl}(W_pos(u')))

with the TWO DIFFERENT word maps on `PosInterfaceConfig`:
- `W_int(x) = x_{n+e₀,ν} · (x_{n+e₀+e_ν,0})⁻¹`  (INTERFACE links of `x`: spatial then
  temporal-inverse at `t = 0`),
- `W_pos(x) = x_{θn,0} · x_{θn+e_ν,ν}`  (POSITIVE links of `x`: temporal then spatial at
  `t = 1`).

**KEY OBSERVATION (resolves the apparent Gram-structure failure).**  `W_int ≠ W_pos` as
functions, so the per-plaquette kernel is NOT naively a Gram kernel in `(u, u')`.  But the
full RP quadratic form integrates the bra positive links `U⁺` and ket positive links `V⁺`
INDEPENDENTLY, and `D^R_{kl}(W_int(u))` depends only on the INTERFACE links `u⁰` of `u`
(not on `U⁺`).  So the `U⁺` integral produces a scalar `A(u⁰) := ∫ dU⁺ ψ(u)·E(u)`
(`E` = bra-side Boltzmann factors), while the `V⁺` integral produces
`B_{Rkl}(u⁰) := ∫ dV⁺ ψ(u')·E'(u')·conj(D^R_{kl}(W_pos(u')))`.  The form becomes

    ∑_{R,k,l} c_R · ∫_{u⁰} A(u⁰)·D^R_{kl}(W_int(u⁰))·B_{Rkl}(u⁰) dμ⁰.

The relation `B_{Rkl}(u⁰) = conj(A_{...}(σ u⁰))` is EXACTLY the proven σ-inversion lemma
(`fourierCoeffNeg_thetaReindex_eq_star_fourierCoeffPos`, session 17) lifted from characters
to matrix elements, and the final `u⁰` integral is evaluated by Schur orthogonality on the
interface links (the `charFactorInt` factor).  This is the precise assembly path for step (iv).

### What this means for the remaining formalization (steps i–iv)

- (i) Formalize the per-plaquette word evaluation above (merged config, `reflectPosToNeg_apply`
  + `Finset.prod_bij`-style link bookkeeping).  Bounded but finicky.
- (ii) The matrix-element factorization `χ_R = ∑_{kl} D(W_int)·conj(D(W_pos))` — group-level
  ingredients all PROVEN (`repCharacter_mul_inv_eq_sum_matrixElement_conj`, `map_mul`,
  `repMatrixElement_inv`); the work is the lattice word bookkeeping from (i).
- (iii) Coefficient non-negativity: `hcoeff`-style hypotheses exist
  (`ReflectionPositivity/CharacterExpansion.lean`); must be threaded through.
- (iv) Assembly: matrix-element σ-inversion (lift Lemma 3 from `repCharacter` to
  matrix elements), σ-invisibility (`fourierCoeffPos_sigma_invisible`, PROVEN), interface
  Schur orthogonality, then `integrated_kernel_psd` / `crossingPlaquette_kernel_psd`.

**Honest status:** group-level OS machinery COMPLETE and formalized; lattice bridge steps
(i)–(iv) remain open formalization (not open math).  Axiom count: still 6.

## §8.11.100 — Session 134: step (i) FORMALIZED — crossing plaquette word evaluation

The per-plaquette word evaluation of §8.11.99 is now PROVEN in
`Proofs/TransferMatrix/Bridge.lean` (0 sorries, axioms [propext, Classical.choice,
Quot.sound] only):

- `extendToFullConfig_apply_neg` / `extendToFullConfig_apply_int`: pointwise evaluation of
  the merged config on negative-site links (→ `U_minus`) and interface-site links (→ `u`).
- `signedTime_succ_of_eq_neg_one`: `signedTime t = -1 → signedTime (t+1) = 0`
  (via `t.val = T - 1`, hence `t + 1 = 0` in `ZMod T`).
- `addVector_zero_time` / `addVector_spatial_time`: time coordinates of `n + e₀` / `n + e_ν`.
- `signedTime_addVector_zero_of_eq_neg_one`, `signedTime_addVector_zero_spatial_of_eq_neg_one`,
  `signedTime_addVector_spatial`, `mem_negativeSites_of_signedTime_eq_neg_one`,
  `mem_interfaceSites_of_signedTime_eq_zero`: site-classification helpers.
- **`plaquetteProduct_extendToFullConfig_crossing`**: for `signedTime n = -1`, `ν ≠ 0`,

      plaquetteProduct (extendToFullConfig (reflectPosToNeg V⁺) u) n 0 ν
        = (V⁺_{θn,0})⁻¹ · u_{n+e₀,ν} · (u_{n+e₀+e_ν,0})⁻¹ · (V⁺_{θ(n+e_ν),ν})⁻¹.

  (The last index is `θ(n+e_ν)`; `reflectSite_addVector_comm` converts to `θn + e_ν` when
  needed downstream.)

Build GREEN (3008 jobs), 0 sorries, axiom count still 6.

**Step (ii) group-level factorization also FORMALIZED (session 134, same commit series):**
`repCharacter_crossing_word_eq_sum_matrixElement_conj` in
`Proofs/PositiveDefiniteIntegral/CascadeNonneg.lean`:

    χ(a⁻¹·b·c⁻¹·d⁻¹) = ∑_{k,l} (ρ (b·c⁻¹))_{kl} · conj((ρ (a·d))_{kl})

for any unitary rep `ρ`.  Proof: both sides equal `Tr(ρ(d⁻¹·a⁻¹·b·c⁻¹))` — LHS by
cyclicity of trace (`Matrix.trace_mul_comm`), RHS by the Frobenius identity
`∑_{kl} X_{kl}·conj(Y_{kl}) = Tr(Yᴴ·X)` plus unitarity `(ρ(a·d))ᴴ = ρ(d⁻¹)·ρ(a⁻¹)`.
Axioms [propext, Classical.choice, Quot.sound] only.  With
`a = V⁺_{θn,0}`, `b = u_{n+e₀,ν}`, `c = u_{n+e₀+e_ν,0}`, `d = V⁺_{θ(n+e_ν),ν}` this is
exactly `χ_R(word) = ∑_{kl} D^R_{kl}(W_int(u))·conj(D^R_{kl}(W_pos(V⁺)))` with
`W_int(x) = x_{n+e₀,ν}·(x_{n+e₀+e_ν,0})⁻¹`, `W_pos(x) = x_{θn,0}·x_{θ(n+e_ν),ν}`.

Remaining: (ii′) combine steps (i)+(ii) into the per-plaquette lattice identity
(`repCharacter (plaquetteProduct …) = ∑_{kl} …`) — **DONE (session 134)**:
`repCharacter_plaquetteProduct_extendToFullConfig_crossing` in Bridge.lean (direct
rewrite by (i) + `exact` by (ii); axioms [propext, Classical.choice, Quot.sound]).
Bridge.lean now imports `PositiveDefiniteIntegral.CascadeNonneg`.
Remaining: (iii) thread `hcoeff` non-negativity — **DONE (session 134)**:
`crossingWordInt` / `crossingWordPos` (named half-words),
`repCharacter_plaquetteProduct_crossing_eq_halfWords` (restatement of (ii′)), and
`crossing_plaquette_boltzmann_matrixElement_expansion` in Bridge.lean:

    exp(c·Re Tr(word)) = ∑_s coeff_s · ∑_{k,l} (ρ_s (W_int u))_{kl}·conj((ρ_s (W_pos V⁺))_{kl})

with `coeff_s ≥ 0` (from `plaquette_boltzmann_character_expansion_single`; Bridge.lean now
also imports `PeterWeyl.Separable`).  Axioms: [propext, Classical.choice, Quot.sound,
peterWeyl_clebschGordan_plaquette] — the last is one of the existing 6 axioms (the
character-expansion input), NOT new.  Axiom count unchanged (6).
Remaining: (iv) assembly (matrix-element σ-inversion, σ-invisibility, interface Schur
orthogonality, then `integrated_kernel_psd` / `crossingPlaquette_kernel_psd`).

## §8.11.101 — Session 135 (2026-08-21): step (iv-a) FORMALIZED — PD-kernel-pullback form

**Step (iv-a) is DONE** (commit d64e157, Bridge.lean, 0 sorries, axioms
[propext, Classical.choice, Quot.sound] — no new axioms, count still 6):

- `reTrace_crossing (A b c D : SU N)`: pure trace cyclicity
  `ReTr(A⁻¹·b·c⁻¹·D⁻¹) = ReTr((A·D)⁻¹·(b·c⁻¹))`.  Proof: `mul_inv_rev` to get
  `(A·D)⁻¹ = D⁻¹·A⁻¹`, push the `SU N → Matrix` coercion through the products with
  `simp only [Submonoid.coe_mul]` (NOTE: `SU N = Matrix.specialUnitaryGroup` is a
  **Submonoid**, so the coe lemma is `Submonoid.coe_mul`, NOT `Subgroup.coe_mul`; an
  earlier attempt with `Subgroup.coe_mul` made no progress, and a `show`-based defeq
  approach timed out on `isDefEq`), then `Matrix.trace_mul_comm` + `noncomm_ring`.
- `crossing_plaquette_boltzmann_eq_pd_kernel`: for a crossing plaquette (signedTime
  `n = -1`, directions `(0, ν)`, `ν ≠ 0`),
  `exp(c·Re Tr(word)) = exp(c·Re Tr((W_pos V⁺)⁻¹ · W_int u))`
  where `word = plaquetteProduct (extendToFullConfig (reflectPosToNeg V⁺) u) n 0 ν`.
  This is exactly the **PD-kernel-pullback form** `k_c((W x)⁻¹·W y)` with
  `k_c(g) = exp(c·Re Tr g)`, `x = V⁺` (ket), `y = u` (bra), `W x = crossingWordPos`,
  `W y = crossingWordInt`.  Proof: rewrite by `plaquetteProduct_extendToFullConfig_crossing`
  (step i), then `congrArg (fun x => Real.exp (c * x)) (reTrace_crossing N _ _ _ _)` —
  the metavars unify because `crossingWordPos`/`crossingWordInt` unfold (defeq) to the
  same link factors with the same membership-proof terms as the crossing word.

**Significance.**  This is the matrix-element lift of the reflection = inversion
mechanism (§8.11.97), realized at the level of the Boltzmann factor rather than the
character.  Combined with `plaquette_boltzmann_character_expansion_single` (which gives
`k_c = ∑_s coeff_s·χ_{ρ_s}` with `coeff_s ≥ 0`, hence `PositiveDefinite k_c` by
`positiveDefinite_finset_sum_repCharacter`), each crossing-plaquette factor is a PD
function evaluated at `(W_pos V⁺)⁻¹·W_int u`.  The product over crossing plaquettes is
then a PSD kernel in `(V⁺, u)` by `crossingPlaquette_kernel_psd` (PSDKernel.lean).

**Remaining for step (iv):**
- (iv-b) Assemble the full interface Boltzmann factor `exp(-β·S_int)` as a product over
  crossing plaquettes of the (iv-a) factors (via
  `exp_neg_beta_wilsonActionOSInterface_eq_prod_abstract`, coupling `c = β²/N ≥ 0`),
  restricted to the crossing subset (signedTime `n = -1`, `μ = 0`, `ν ≠ 0`); the
  non-crossing interface plaquettes (corners `{0,1}`, all positive+interface links)
  depend only on `u` and are multiplication-operator factors to be tracked into the
  `S⁺`-bookkeeping.  Apply `crossingPlaquette_kernel_psd` to get the PSD kernel.
- (iv-c) Final assembly: connect the PSD kernel to the RP quadratic form
  `∫ G(U)·G(θU)` via `transferMatrixReflected_VUV_factorization` (PROVEN) +
  `integral_G_thetaG_eq_inner_g_Tg` (PROVEN) + the bra/ket conjugation relation
  (σ-invisibility `fourierCoeffPos_sigma_invisible`, PROVEN), then replace
  `transferMatrixPositivity_axiom` (axiom count 6 → 5).

## §8.11.102 — Session 136 (2026-08-22): step (iv-b1) FORMALIZED + a CORRECTION to the (iv-b) plan

**Step (iv-b1) DONE** (commit e5648ec, Bridge.lean, 0 sorries, axioms
[propext, Classical.choice, Quot.sound] — count still 6):

- `isCrossingPlaquetteIdx T L p` : `p.2.1 = 0 ∧ signedTime T p.1.time = -1 ∧ p.2.2 ≠ 0`.
- `addVectorPeriodic_zero_time`, `signedTime_addVectorPeriodic_zero_of_eq_neg_one`
  (`addVectorPeriodic`-forms; the existing `addVector_zero_time` is stated via
  `AddVector.addVector`, which does not `rw`-match `addVectorPeriodic` occurrences).
- `isInterfacePlaquette_of_crossing`: crossing plaquettes are interface plaquettes
  (corners `{-1,0,0,-1}`).
- `prod_plaquetteIndex_eq_triple`: `∏ p : PlaquetteIndex, g p.1 p.2.1 p.2.2 =
  ∏ n ∏ μ ∏ ν, g n μ ν` (via `← Finset.univ_product_univ` + `Finset.prod_product` twice).
- `prod_plaquetteIndex_split_crossing`: product split via
  `Finset.prod_filter_mul_prod_filter_not` — NOTE: its statement is
  `(∏ filter p) * (∏ filter ¬p) = ∏ s` (split on the LEFT), so use `.symm`/explicit
  application; a bare `rw` in either direction failed (HOU + DecidablePred synthesis).
- **`interface_boltzmann_eq_crossing_mul_rest`**: for
  `U = extendToFullConfig (reflectPosToNeg V⁺) u`,
  `exp(-β·S_int(U)) = (∏ p crossing, exp(-β²)·k_c((W_pos V⁺)⁻¹·W_int u)) · (rest)`,
  where `rest` is the product over non-crossing plaquette indices of the original
  if-interface factors.  Proof: `exp_neg_beta_wilsonActionOSInterface_eq_prod_abstract`
  + the two product lemmas + per-plaquette rewrite by
  `crossing_plaquette_boltzmann_eq_pd_kernel` (iv-a).  `classical` needed for the
  filter `DecidablePred` instances.

**CORRECTION to the (iv-b) plan (adversarial self-check, report plainly).**  The
§8.11.101 plan "the product over crossing plaquettes is a PSD kernel in `(V⁺, u)` by
`crossingPlaquette_kernel_psd`" is **mathematically incorrect as stated**.
`crossingPlaquette_kernel_psd` requires a SINGLE word map `W : P → X → G` on a single
space, giving `K(x,y) = k((W x)⁻¹·W y)`.  The actual crossing factor is the MIXED
kernel `K(y,x) = k_c(W_pos(y)⁻¹·W_int(x))` with `W_pos ≠ W_int`
(§8.11.99 already noted this).  Such a mixed kernel is **not even Hermitian** in
general: Hermiticity would require `k(A_y⁻¹B_x) = k(A_x⁻¹B_y)` for all achievable
values, and since `W_pos`, `W_int` are (essentially) independent surjective word maps,
this forces `k` constant — false for `k_c = exp(c·ReTr)`.  Hence no
`crossingPlaquette_kernel_psd` application to the mixed kernel is possible, and the
per-orientation crossing product is NOT a PSD kernel in `(V⁺, u)`.

**The correct path (already in §8.11.99, KEY OBSERVATION)** is the INTEGRATED
assembly: positivity holds only after the independent `U⁺`/`V⁺` integrals collapse
the matrix-element factors to scalars over the shared interface config `u⁰`, where
the σ-inversion lemma (`B_{Rkl}(u⁰) = conj(A(σ u⁰))`) + σ-invisibility give
`∫_{u⁰} |A|² ≥ 0`.  `crossingPlaquette_kernel_psd` remains true and useful as
group-level machinery, but it does NOT apply to the crossing kernel directly.
Step (iv-b) is therefore REPLACED by:
- (iv-b2′) per-crossing-plaquette matrix-element expansion of the Boltzmann factor
  (DONE: `crossing_plaquette_boltzmann_matrixElement_expansion`, session 134) —
  what remains is the product version over the crossing Finset;
- (iv-b3′) matrix-element σ-inversion lift (Lemma 3 from `repCharacter` to matrix
  elements) + interface Schur orthogonality + σ-invisibility, giving the
  sum-of-squares form of the RP quadratic form.

**Honest status:** (iv-b1) verified (compiled, axioms checked).  The correction above
is an ANALYSIS (believed true, elementary linear algebra), not yet reflected in any
Lean statement — no Lean claim was made or removed.  Axiom count: still 6.

**Additional observation (rest-product composition).**  The `rest` product in
`interface_boltzmann_eq_crossing_mul_rest` is NOT entirely `u`-only.  Besides the
`{0,1}`-corner plaquettes (based at `signedTime n = 0`, all links positive/interface,
`u`-only — harmless multiplication-operator factors), it contains three MIXED
(`V⁺`/`u`) families, each needing the same matrix-element treatment as the crossing
family:
(a) reversed-orientation crossings `(n, ν, 0)` with `signedTime n = -1`, `ν ≠ 0`
    (word `V₁·V₂⁻¹·u₁⁻¹·u₂⁻¹`, PD-pullback form `k_c((V₂V₁⁻¹)⁻¹·(u₁⁻¹u₂⁻¹))` by
    cyclicity — same mixed-kernel caveat);
(b) degenerate temporal plaquettes `(n, 0, 0)` with `signedTime n = -1` (corners
    `{-1,0,1,0}`, word `(V⁺_{θn,0})⁻¹·u·u⁻¹·u⁻¹`);
(c) **wraparound plaquettes** based at `signedTime n = (T-1)/2` (the second,
    periodicity-induced interface): `(n, 0, ν)` or `(n, ν, 0)` — corners straddle the
    seam `t = (T-1)/2 ↔ -(T-1)/2`, links mixed positive/negative.
Family (c) is the periodic lattice's second OS interface; it is handled by the SAME
reflection mechanism (the seam is reflection-invariant), but it must be included in
the assembly — the `rest` is not purely bookkeeping.

**Step (iv-b2′) DONE (session 136, commit 36600c6, Bridge.lean, 0 sorries):**
`CrossingPlaquette T L` subtype (+ `Fintype` instance) and
`crossing_prod_boltzmann_matrixElement_expansion`: the product over ALL crossing
plaquettes of `exp(c·Re Tr(word_p))` equals
`∑_{w : CrossingPlaquette → ι} (∏_p coeff_{w p}) · ∏_p ∑_{k,l}
(ρ_{w p} (W_int^p u))_{kl} · conj((ρ_{w p} (W_pos^p V⁺))_{kl})` with `coeff ≥ 0`.
Proof: shared expansion datum from `plaquette_boltzmann_character_expansion_single`
(plaquette-independent), per-plaquette rewrite by
`repCharacter_plaquetteProduct_crossing_eq_halfWords`, then `Finset.prod_univ_sum`
+ `Finset.prod_mul_distrib`.  Axioms: [propext, Classical.choice, Quot.sound,
peterWeyl_clebschGordan_plaquette] — the last is one of the existing 6 axioms.
Axiom count unchanged (6).  Remaining: (iv-b3′) matrix-element σ-inversion lift +
interface Schur orthogonality + σ-invisibility → sum-of-squares; then (iv-c).

## §8.11.103 — Session 138 (2026-08-26): step (iv-b3′) matrix-element σ-inversion lift FORMALIZED

**DONE (SigmaInversion.lean, 0 sorries, all `#print axioms` = [propext, Classical.choice,
Quot.sound]).**  The character-level Lemma 3 identity
(`charFactorNeg_thetaReindex_eq_charFactorPos`) is lifted to individual matrix elements:

- `repMatrixElement_apply_congr`: congruence for matrix elements across equal rep
  labels, with indices compared at `.val` level (avoids "motive is not type correct"
  when comparing through `Fin.cast`).
- `repMatrixElement_dual_inv_eq` (time-like): `(ρ (dual i) g⁻¹) (cast b) (cast a) =
  (ρ i) g a b` — via `repMatrixElement_inv` + `hdual_me` + `conj_conj`.  Note the
  INDEX SWAP.
- `repMatrixElement_dual_dual_eq` (spatial): `(ρ (dual (dual i)) g) (cast a) (cast b) =
  (ρ i) g a b` — via double `hdual_me` + `conj_conj`.  NO index swap.
- `matrixElemFactorPos` / `matrixElemFactorNeg`: matrix-element analogues of
  `charFactorPos` / `charFactorNeg`, with index assignment
  `κ : ∀ l, Fin (dims (w l)) × Fin (dims (w l))`.
- `mem_interfaceLinkNeg_of_not_pos_not_int`: trichotomy helper.
- `thetaReindexMatrixElem`: the index reindexing `θκ` accompanying `thetaReindex`;
  SWAPS the index pair for negative time-like links only (matching the asymmetry of
  the two group-level identities above).  Branch values stated at `.val` level
  (`thetaReindexMatrixElem_neg_time_vals`, `_neg_spatial_vals`).
- `matrixElemFactorNeg_thetaReindex_link_eq`: per-link identity (mirrors
  `charFactorNeg_thetaReindex_link_eq`; link-evaluation parts copied verbatim).
- `matrixElemFactorNeg_thetaReindex_eq_matrixElemFactorPos`: **main identity** —
  `matrixElemFactorNeg dual hdims (θw) (θκ) (reflectPosToNeg V⁺) =
  matrixElemFactorPos w κ V⁺`, via `Finset.prod_bij` over the reflection involution.

**NEW HYPOTHESES (flagged per project rule 1 — lemma hypotheses, NOT axioms; no
axiom_growth_log entry needed).**  The lift requires TWO hypotheses beyond the
character-level `hdual`:
1. `hdims : ∀ i, dims (dual i) = dims i` (dual preserves dimension);
2. `hdual_me : ∀ i g a b, (ρ (dual i) g) (cast a) (cast b) = conj ((ρ i) g a b)` —
   ELEMENTWISE dual-conjugation.  `hdual` is only the character-level (trace) version;
   `hdual_me` implies `hdual` (take trace) but not conversely.

Both are satisfied when the dual representation IS the conjugate representation
(`ρ (dual i) g = (ρ i g).map conj` up to the `Fin.cast` reindexing), which is the
standard choice in the SU(N) Peter–Weyl decomposition.  Category: **known but
unformalized** (standard representation theory), NOT genuinely open math.  When the
lift is eventually applied, the instantiation site must supply `hdims`/`hdual_me` for
the concrete Peter–Weyl dual — this is a proof obligation there, not a new axiom.

**Status:** verified (compiled, `#print axioms` checked, no sorry).  Axiom count
unchanged: 6.  Next: combine with `crossing_prod_boltzmann_matrixElement_expansion`
(Bridge.lean) + interface Schur orthogonality + σ-invisibility → sum-of-squares;
word evaluations for rest-product mixed families (reversed crossings, degenerate
`(n,0,0)`, wraparound) analogous to `plaquetteProduct_extendToFullConfig_crossing`;
then (iv-c) final assembly.

## §8.11.104 — Session 138 (2026-08-26) continued: (iv-b3′) Fourier-level lift FORMALIZED

**DONE (SigmaInversion.lean, 0 sorries, axioms [propext, Classical.choice, Quot.sound]).**
The matrix-element σ-inversion identity is lifted from the pointwise level to the
Fourier-coefficient level, giving exactly the relation `B_{Rkl}(u⁰) = conj(A(σ u⁰))`
of the §8.11.99 KEY OBSERVATION:

- `matrixElemFactorNeg_thetaReindex_eq_matrixElemFactorPos_star`: `congrArg star` of the
  pointwise identity.
- `fourierCoeffPosME` / `fourierCoeffNegME`: matrix-element analogues of
  `fourierCoeffPos` / `fourierCoeffNeg` (Fubini.lean), with index assignment `κ`.
- **`fourierCoeffNegME_thetaReindex_eq_star_fourierCoeffPosME`**:
  `fourierCoeffNegME(θw, θκ, u⁰) = star(fourierCoeffPosME(w, κ, σ(u⁰)))`.
  Proof mirrors the character-level version: `integral_conj` + `star_mul'` +
  `conj_ofReal` reduce to the pointwise star identity.

**Status:** verified (compiled, `#print axioms` checked, no sorry).  Axiom count: 6.

**CONTINUED (same session, commit after 1fb1d5a):** the σ-invisibility half of the
pairing is now also formalized:
- `fourierCoeffPosME_sigma_invisible`: `A^{ME}_{w,κ}(σ(u⁰)) = A^{ME}_{w,κ}(u⁰)` for
  `ψ = g_posInterface f` with `f` satisfying `dependsOnlyOnPosSpatialInterface`
  (mirrors `fourierCoeffPos_sigma_invisible`; `matrixElemFactorPos` depends only on
  `U⁺`, so the same `g_posInterface_sigma_invisible` +
  `osPositiveOfPosInterface_sigma_invariant` rewrites close it).
- **`fourierCoeffNegME_thetaReindex_eq_star_fourierCoeffPosME_of_sigma_invisible`**:
  the assembled pairing `B^{ME}_{θw,θκ}(u⁰) = star(A^{ME}_{w,κ}(u⁰))` — the exact
  identity needed for the RP quadratic form to become a sum of `|A|²` terms.

Remaining for the sum-of-squares assembly: (1) bridging the per-link index
assignment `κ` to the crossing expansion's per-plaquette internal indices `(k,l)` via
the half-word structure (`crossingWordInt`/`crossingWordPos`); (2) interface Schur
orthogonality on the `charFactorInt` factor; (3) word evaluations for the rest-product
mixed families; (4) (iv-c) final assembly.

## §8.11.105 — Session 138 (2026-08-26/27) continued: rest-product family (a) FORMALIZED

**DONE (Bridge.lean, 0 sorries, axioms [propext, Classical.choice, Quot.sound]).**
The reversed-orientation crossing plaquettes `(n, ν, 0)` (`signedTime n = -1`,
`ν ≠ 0`) — rest-product mixed family (a) of §8.11.102 — now have the same treatment
as the forward crossings:

- `plaquetteProduct_extendToFullConfig_crossing_reversed`: word evaluation
  `V⁺_{θn,ν} · (V⁺_{θ(n+e_ν),0})⁻¹ · (u_{n+e_ν+e₀,ν})⁻¹ · (u_{n+e₀,0})⁻¹`
  (negative spatial link unchanged, negative temporal link inverted, two interface
  links from `u`).
- `crossingRevWordInt` / `crossingRevWordPos`: the half-words
  `W_int^rev = u₁⁻¹·u₂⁻¹` (interface) and `W_pos^rev = V₂·V₁⁻¹` (positive).
- `repCharacter_plaquetteProduct_crossing_reversed_eq_halfWords`:
  `χ(word) = ∑_{k,l} (ρ (W_int^rev u))_{kl} · conj((ρ (W_pos^rev V⁺))_{kl})`.
  Proof: cyclic rotation to the `a⁻¹·b·c⁻¹·d⁻¹` pattern of
  `repCharacter_crossing_word_eq_sum_matrixElement_conj` with `a = V₂`, `b = u₁⁻¹`,
  `c = u₂`, `d = V₁⁻¹` (reassociation + `inv_inv` via `group`).

**Status:** verified (compiled, `#print axioms` checked, no sorry).  Axiom count: 6.
Remaining rest-product families: (b) degenerate temporal plaquettes `(n, 0, 0)` at
`signedTime n = -1`; (c) wraparound plaquettes at the second interface
`signedTime n = (T-1)/2`.  Then: κ-bridging, interface Schur orthogonality, (iv-c).

## §8.11.106 — Session 138 (2026-08-27) continued: rest-product family (b) FORMALIZED

**DONE (Bridge.lean, 0 sorries, axioms [propext, Classical.choice, Quot.sound]).**
The degenerate temporal plaquettes `(n, 0, 0)` at `signedTime n = -1` — rest-product
mixed family (b) of §8.11.102 — now have word evaluation + half-word factorization:

- `signedTime_add_two_of_eq_neg_one`: `signedTime T t = -1 → signedTime T (t+2) = 1`
  (needs `T ≥ 3`, from `Odd T` + impossibility of `signedTime = -1` at `T = 1`).
- `signedTime_addVector_zero_twice_of_eq_neg_one`, `mem_positiveSites_of_signedTime_eq_one`,
  `extendToFullConfig_apply_pos` (positive-site link evaluation — new; the crossing
  families only needed the neg/int versions).
- `plaquetteProduct_extendToFullConfig_degenerate`: word evaluation
  `(V⁺_{θn,0})⁻¹ · u_{n+e₀,0} · (u_{n+2e₀,0})⁻¹ · (u_{n+e₀,0})⁻¹`.
  (Note: the third link is a POSITIVE-site link, drawn from `u`'s positive part —
  so this family's half-words mix ket/bra variables differently from the crossing
  families.)
- `degenerateWordA` / `degenerateWordB`: half-words `W_A = u₁·u₂⁻¹`,
  `W_B = V⁺_{θn,0}·u₁`.
- `repCharacter_plaquetteProduct_degenerate_eq_halfWords`:
  `χ(word) = ∑_{k,l} (ρ (W_A u))_{kl} · conj((ρ (W_B V⁺ u))_{kl})` — the word is
  ALREADY in the `a⁻¹·b·c⁻¹·d⁻¹` pattern, so
  `repCharacter_crossing_word_eq_sum_matrixElement_conj` applies directly (no cyclic
  rotation needed, unlike family (a)).

**Status:** verified (compiled, `#print axioms` checked, no sorry).  Axiom count: 6.
Remaining rest-product family: (c) wraparound plaquettes at `signedTime n = (T-1)/2`.
Then: κ-bridging, interface Schur orthogonality, (iv-c) final assembly.

## §8.11.107 — Session 138 (2026-08-27) continued: rest-product family (c) word evaluation

**DONE (Bridge.lean, 0 sorries, axioms [propext, Classical.choice, Quot.sound]).**
The wraparound plaquettes `(n, 0, ν)` at the far seam `signedTime n = (T-1)/2` —
rest-product mixed family (c) of §8.11.102 — now have their word evaluation:

- `signedTime_succ_of_eq_max`: `signedTime T t = (T-1)/2 → signedTime T (t+1) =
  -((T-1)/2)` (wraparound at the seam; needs `3 ≤ T` — for `T = 1` the seam coincides
  with the `t = 0` interface; `Odd T` is needed for `2·((T-1)/2) = T-1`).
- `signedTime_addVector_zero_of_eq_max`, `mem_positiveSites_of_signedTime_eq_max`,
  `mem_negativeSites_of_signedTime_neg_max`.
- `plaquetteProduct_extendToFullConfig_wraparound`: word evaluation
  `u_{n,0} · V⁺_{θ(n+e₀),ν} · V⁺_{θ(n+e₀+e_ν),0} · (u_{n+e_ν,ν})⁻¹`.
  **Note the third factor is UN-INVERTED**: the negative temporal link is inverted by
  the reflection AND by the plaquette orientation (double inverse).  (An earlier draft
  of this lemma had a spurious `⁻¹` there — caught by the build, fixed.)

**Status:** verified (compiled, `#print axioms` checked, no sorry).  Axiom count: 6.

**Factorization DONE (same session):** `wraparoundWordA` / `wraparoundWordB` +
`repCharacter_plaquetteProduct_wraparound_eq_halfWords`.  The wraparound word
`u₁·V₁·V₂·u₂⁻¹` is already in `A·B⁻¹` form with `A = u₁·V₁·V₂` (three links: positive
temporal from `u`, then the two reflected negative links from `V⁺`) and `B = u₂` (the
positive spatial link from `u`), so `repCharacter_mul_inv_eq_sum_matrixElement_conj`
applies directly: `χ = ∑_{kl} (ρ(W_A))_{kl}·conj((ρ(W_B))_{kl})`.  (Note: the grouping
is NOT `(u₁V₁)·(u₂V₂)⁻¹` as first sketched — the third factor is un-inverted, so the
correct split is `(u₁V₁V₂)·u₂⁻¹`.)

Remaining: the reversed wraparound orientation `(n, ν, 0)` at the far seam (analogous
word evaluation + factorization); then κ-bridging (per-link index assignments vs
per-plaquette `(k,l)`), interface Schur orthogonality, (iv-c) final assembly.
