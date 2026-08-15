# Path Forward to Solve the Yang-Mills Gap

**Status: ANALYSIS. Written session 113, 2026-08-15.**
**This document is paused — do not resume until housekeeping (project refactoring) is complete.**

## Current state

- **Build: GREEN.** Axiom count: 6. 0 sorries.
- The 6 axioms: `propext`, `Classical.choice`, `Quot.sound`, `characterOrthogonality`,
  `peterWeyl_clebschGordan_plaquette`, `transferMatrixPositivity_axiom`.
- The closeable axiom is `transferMatrixPositivity_axiom` (ReflectionPositivity.lean:3761).
- Closing it reduces 6 → 5.

## What is already proven (0 sorries, 0 custom axioms beyond Peter-Weyl)

The existing machinery is FAR more extensive than it appears. The reflection conjugation
— the key step — is ALREADY PROVEN:

1. **`fullReflectReindex` (w*)** (TransferMatrix.lean:5749): The reflection reindexing
   that swaps pos ↔ neg via `reflectInterfaceLink`, applying `dual` on time-like links.

2. **`charFactorNeg_eq_star_charFactorPos_fullReflect`** (TransferMatrix.lean:5884):
   `charFactorNeg w (reflectPosToNeg V⁺) = star(charFactorPos (w*) V⁺)` — the reflection
   conjugation identity.

3. **`fourierCoeffNeg_eq_fourierCoeffPos_fullReflect`** (TransferMatrix.lean:5970):
   `B_w(u⁰) = A_{w*}(σ(u⁰))` — the negative Fourier coefficient equals the positive
   Fourier coefficient at the reflected weight and reflected interface.

4. **`transfer_matrix_fubini_integrated_pull_fullReflect`** (TransferMatrix.lean:6005):
   The FULL transfer matrix inner product form:
   `∫ ψ·Tψ = C · ∑_w F(w) · ∫_{u⁰} Ψ_w(u⁰) · A_w(u⁰) · A_{w*}(σ(u⁰)) dμ⁰`
   where A_w = fourierCoeffPos, Ψ_w = charFactorInt, F(w) ≥ 0.

5. **`character_expansion_positivity`** (PositiveDefiniteIntegral.lean:1010): The
   abstract scaffold: if K(x,y) = ∑_i a_i · Φ_i(x) · conj(Φ_i(θy)) with a_i ≥ 0 and
   θ measure-preserving, then ∫∫ f(x)·f(θy)·K(x,y) dν dμ = ∑_i a_i · ‖∫ f·Φ_i dμ‖² ≥ 0.

6. **`integral_G_thetaG_eq_inner_g_Tg`** (TransferMatrix.lean:5149): The bridge identity
   ∫ G(U)·G(θU) dμ₀ = ∫ g(u)·(Tg)(u) dμ⁺⁰.

## The exact remaining obstacle

The transfer matrix inner product is:
```
∫ ψ·Tψ = C · ∑_w F(w) · ∫_{u⁰} Ψ_w(u⁰) · A_w(u⁰) · A_{w*}(σ(u⁰)) dμ⁰
```

**Key simplification from `dependsOnlyOnPosSpatialInterface`:** Since ψ (hence f)
doesn't depend on temporal interface links, and σ only inverts temporal interface
links, we have `A_w(σ(u⁰)) = A_w(u⁰)`. So the integral becomes:
```
∫_{u⁰} Ψ_w(u⁰) · A_w(u⁰) · A_{w*}(u⁰) dμ⁰
```

**The obstacle:** Ψ_w(u⁰) = ∏_{l ∈ interfaceLinks} χ_{w(l)}(g_l) is COMPLEX (product
of characters). The integral `∫ Ψ_w · A_w · A_{w*} dμ⁰` is NOT obviously ≥ 0.

The interface character factor Ψ_w couples the positive and negative sides. It appears
in BOTH the positive factor and the reflected negative factor, preventing the clean
separation needed for `character_expansion_positivity`.

## Three paths forward

### Path 1: Half-weight expansion (RECOMMENDED — most standard OS approach)

Expand `exp(-β·S_int/2)` in characters instead of `exp(-β·S_int)`. This splits the
interface character factor between the positive and negative sides:
- `G(U) = f·exp(-β·S⁺)·exp(-β·S_int/2)` uses the half-weight expansion
- `G(θU) = f(θU)·exp(-β·S⁻)·exp(-β·S_int/2)` uses the same half-weight at reflected config
- The product `G(U)·G(θU)` then has the FULL-weight expansion

The key: the half-weight expansion may have a separable form where the interface
factor is split as `Ψ_w^{1/2} · Ψ_w^{1/2}`, one half in each factor. This requires
a character expansion of `exp(-β·S_int/2)`, which may need `√coeff` (square root of
expansion coefficients). This is standard in the OS literature but requires careful
formalization.

**Why this works:** The half-weight `exp(-β·S_int/2) = (exp(-β·S_int))^{1/2}`. If the
character expansion of `exp(-β·S_int)` has non-negative coefficients (which it does,
via `peterWeyl_clebschGordan_plaquette` Part 1), then the half-weight expansion can
be obtained by taking square roots of the coefficients. The square root of a PD
function with non-negative coefficient sum is also PD.

**Formalization steps:**
1. Prove that `exp(-β·S_int/2)` admits a character expansion with non-negative
   coefficients (using the PD property + square root of coefficients).
2. Show that the half-weight expansion gives a separable form
   `exp(-β·S_int/2) = ∑_w c_w · Φ_w^{1/2}(U⁺,u⁰) · conj(Φ_w^{1/2}(θU⁻,σu⁰))`.
3. Apply `character_expansion_positivity` to conclude `∫ G·G(θU) ≥ 0`.

### Path 2: PD kernel approach

Use `plaquetteBoltzmannPD` (proven) + Schur product theorem to show `exp(-β·S_int)` is
PD on the interface link group. Then show the transfer matrix kernel
`K(u, U⁻) = exp(-β·(S⁺/2 + S⁻/2 + S_int))` is PD, giving `⟨g, Tg⟩ ≥ 0`.

The key lemma needed: "if K is a PD kernel and θ is measure-preserving, then
`∫ f(x)·f(θy)·K(x,y) dμ dν ≥ 0`" — this is `character_expansion_positivity` with
the PD property replacing the separable decomposition.

**Status:** The PD property of `exp(-β·S_int)` on the interface link group is NOT yet
proven (only the plaquette-level and full-lattice PD are proven). The connection
between PD kernels and reflection positivity needs a new lemma.

### Path 3: Direct |...|² approach

Show that the sum `∑_w F(w) · ∫_{u⁰} Ψ_w(u⁰) · A_w(u⁰) · A_{w*}(u⁰) dμ⁰` can be
reorganized as `∑_w' F'(w') · |∫_{u⁰} A_{w'}(u⁰) · Ψ'_{w'}(u⁰) dμ⁰|² ≥ 0` for some
reindexed sum and modified character factors.

**Status:** NOT yet analyzed in detail. The coupling through F(w) is the key difficulty.

## Recommendation

**Path 1 (half-weight expansion)** is the most standard OS approach and most likely
to work. The next session (after housekeeping) should investigate whether the
half-weight character expansion can be formalized using the existing
`peterWeyl_clebschGordan_plaquette` axiom (Part 1).

## What does NOT work

- **Change-of-variables + gauge projection (session 112):** FLAWED. The simplified
  plaquette formula doesn't match the actual lattice. Partial gauge transformation
  doesn't preserve S_int for type 2 plaquettes (T-1→0). See §8.11.85.

- **1D cascade / 3D global cascade (§8.11.84):** The 1D cascade is a 1D tool but the
  3D lattice has each temporal link in 6 plaquettes. Requires matrix-element-level CG
  decomposition with off-diagonal CG unitarity (NOT proven). See §8.11.84.

- **Direct separable form without half-weight:** The interface character factor Ψ_w
  appears in both positive and negative factors, preventing clean separation for
  `character_expansion_positivity`.
