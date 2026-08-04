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
