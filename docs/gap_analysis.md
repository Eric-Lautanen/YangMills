# Gap Analysis: Correct Reflection Positivity Proof

## Current Status

The reflection positivity proof for the Wilson action on a finite periodic lattice
(`gibbsExpectationPeriodic_reflection_positive` in `ReflectionPositivity.lean`)
is complete except for the final positivity step (the integral of G·θG).

### ✅ Correction applied (2026-06-28)

The `TransferMatrix.lean` file has been rewritten with the **correct** transfer matrix
definitions.  The previous approach (using `G_plus` with negative links set to 1) was
mathematically incorrect.  The file now contains:

- **`reflectToPosInterface`**: The map θ⁻⁰ from negative+interface to positive+interface
  configurations via the full geometric reflection.
- **`g_posInterface`**: The function `g(u) = f(u)·exp(-β·S_OS⁺(u)/2)` for `u` in the
  positive+interface space.
- **`transferMatrixCorrect`**: The correct transfer matrix T acting on PosInterfaceConfig:
  `(T ψ)(u) = ∫ ψ(θ⁻⁰(U⁻,u⁰))·exp(-β·(S_OS⁻(U⁻)+S_OS_int(u,U⁻))/2) dμ⁻(U⁻)`
- **`integral_G_thetaG_eq_inner_g_Tg`**: The key identity (proof is `sorry`).
- **`transferMatrixCorrect_positive`**: Positivity of T (proof is `sorry`, requires Peter-Weyl).
- **`integral_G_thetaG_nonneg'`**: The final positivity result under the hypothesis.

The old incorrect `transferMatrix_identity` has been removed.  See `docs/found_issues.md`
for details on the mathematical error.

### What is proved (no gaps):
### What is proved (no gaps):

1. **Action decomposition**: $S_W = S^+_{OS} + S^-_{OS} + S^0_{OS}$ (OS plaquette decomposition)
   - `total_decomposition_os_periodic`
   - `neg_action_reflection_os_periodic`: $S^-_{OS}[U] = S^+_{OS}[\theta U]$
   - `interface_action_reflection_symmetric_os_periodic`: $S^0_{OS}[\theta U] = S^0_{OS}[U]$

2. **Algebraic factorization**: $\exp(-\beta S_W) = G(U) \cdot G(\theta U)$ where
   $G(U) = f(U) \exp(-\beta S^+_{OS}(U)) \exp(-\beta S^0_{OS}(U)/2)$
   - `h_factorization`, `h_integrand_eq`

3. **Reduction to integral**: $\langle f \cdot \theta f \rangle = \int G(U) G(\theta U) \, d\mu_0(U)$

### The remaining gap:

$$\int_{\text{config}} G(U) \cdot G(\theta U) \, d\mu_0(U) \ge 0$$

where $\mu_0$ is the product Haar measure on $\text{SU}(N)^{\text{links}}$.

### ✅ Key identity PROVEN (2026-06-28)

The measure-theoretic identity
$$\int G(U) \cdot G(\theta U) \, d\mu_0(U) = \int_{\text{PosInt}} g(u) \cdot (Tg)(u) \, d\mu^{\pm 0}(u)$$
is fully proven in `TransferMatrix.lean` (`integral_G_thetaG_eq_inner_g_Tg`, 0 sorries).
This reduces the problem to showing $\langle g, Tg \rangle \ge 0$.

### ❌ Transfer matrix positivity — abstract sub-steps proved, wiring remaining

The transfer matrix $T$ is positive **if and only if** its integral kernel is a
positive-definite function on the group of link variables. The kernel is a product of
plaquette Boltzmann factors $\exp(c \cdot \operatorname{Re} \operatorname{Tr}(U_{\partial p}))$.

**Both abstract sub-steps of the positivity chain are now proved** (in
`PositiveDefiniteIntegral.lean`, 0 sorries, 0 custom axioms):

1. `PositiveDefinite.integral` — an integral average of PD functions is PD
   (closes "integrate out interior links ⟹ the resulting kernel is PD").
2. `PositiveDefinite.integralOperator_nonneg` — a PD kernel $K$ on a compact
   group $G$ defines a positive integral operator:
   $\iint f(x)\,\overline{f(y)}\,K(x^{-1}y)\,d\mu(x)\,d\mu(y) \ge 0$.
   The proof approximates the integral by Riemann sums (each non-negative by
   `PositiveDefinite.sum_nonneg_of_map`) and controls the error via uniform
   continuity on $G \times G$.

**Approach (a) — Mercer-type PD kernel theory — is now also built** (same file,
0 sorries, 0 custom axioms).  This removes the group-structure requirement:

3. `PositiveDefiniteKernel` — a kernel $K : X \to X \to \mathbb{C}$ is
   positive-definite in the Mercer sense: $\sum c_i \overline{c_j} K(x_i, x_j)
   \ge 0$ for every finite set and coefficients.  No group structure on $X$.
4. `PositiveDefiniteKernel.sum_nonneg_of_map` — the quadratic form is
   non-negative even under a non-injective index map.
5. `PositiveDefiniteKernel.integralOperator_nonneg` — a *continuous* Mercer-PD
   kernel on a compact space defines a positive integral operator, with no
   Haar-measure invariance or group structure needed.  This is the strictly more
   general version of (2); `PositiveDefinite.toPositiveDefiniteKernel` shows the
   group-theoretic notion embeds into the Mercer one.

**Building blocks for the full Boltzmann factor** are now proved in
`PositiveDefinite.lean` (0 sorries):

6. `PositiveDefinite.comp_mulEquiv` — PD is preserved by group isomorphisms
   (permute/rearrange factors of a product group).
7. `PositiveDefinite.fst` / `.snd` — a PD function on one factor, viewed as a
   function on a product that ignores the other factor, is PD (extension by
   constants).
8. `PositiveDefinite.finprod` — a finite product of PD functions on the same
   group is PD (n-ary Schur product theorem).

These are the abstract ingredients for promoting the single-plaquette result
`plaquetteBoltzmannPD` to PD-ness of the full Boltzmann factor
$\exp(-\beta S_W) = \prod_p \exp(\beta\,\operatorname{Re}\operatorname{Tr}(U_{\partial p}))$
on the entire link-variable group.  The remaining combinatorial wiring (which
links belong to which plaquette, permuting factors into position) is
lattice-specific and not yet formalized.

**Additional infrastructure** proved in `PositiveDefinite.lean` and
`PeterWeyl.lean` (0 sorries, 0 custom axioms beyond the Peter–Weyl axiom):

9. `PositiveDefinite.comp_hom` — PD is preserved by group *homomorphisms*
   (generalizes `comp_mulEquiv` from isomorphisms to arbitrary homomorphisms,
   e.g. coordinate projections from a product group to a sub-product).
10. `repCharacter_inv` — for a unitary representation, the character satisfies
    $\chi(g^{-1}) = \overline{\chi(g)}$ (from $\rho(g^{-1}) = \rho(g)^{-1} =
    \rho(g)^H$ and $\operatorname{Tr}(M^H) = \overline{\operatorname{Tr}(M)}$).
11. `plaquetteBoltzmannPD_inv` — the plaquette Boltzmann factor with **inverse
    links** $\exp(c \cdot \operatorname{Re}\operatorname{Tr}(g_1 g_2 g_3^{-1}
    g_4^{-1}))$ is PD on $\text{SU}(N)^4$.  This is the version needed for the
    actual lattice plaquette product $U(n,\mu) \cdot U(n{+}e_\mu,\nu) \cdot
    U(n{+}e_\mu{+}e_\nu,\mu)^{-1} \cdot U(n{+}e_\nu,\nu)^{-1}$, which has
    inverses on the 3rd and 4th links (orientation reversal).  The proof
    substitutes $(g_1, g_2, g_3^{-1}, g_4^{-1})$ into the Peter–Weyl axiom,
    then replaces $\chi_u(g_3^{-1}) = \overline{\chi_u(g_3)}$ and
    $\chi_v(g_4^{-1}) = \overline{\chi_v(g_4)}$ via `repCharacter_inv`; each
    factor $\chi_s \cdot \chi_t \cdot \overline{\chi_u} \cdot \overline{\chi_v}$
    is PD by `charProduct4_inv_positiveDefinite` (using `PositiveDefinite.conj`
    on the 3rd and 4th factors), and the sum with non-negative coefficients is
    PD by `PositiveDefinite.sum`.

**Promotion to the full link-variable group** is now proved in
`BoltzmannFactor.lean` (0 sorries, 0 custom axioms beyond the Peter–Weyl axiom;
full `lake build` clean):

12. `plaquetteProjection` — the group homomorphism
    `LinkVariable (SU N) Λ →* ((SU N × SU N) × SU N) × SU N` extracting the four
    link variables around a plaquette `(n, μ, ν)`.  It is a homomorphism because
    the group operation on `LinkVariable` is pointwise (the product group
    `SU(N)^{Λ × Fin 4}`) and the operation on `SU(N)^4` is componentwise; both
    `map_one'` and `map_mul'` hold by `rfl` (definitional pointwise structure).
13. `plaquetteFactorPD` — the plaquette Boltzmann factor
    $\exp((\beta/N)\,\operatorname{Re}\operatorname{Tr}(U_{\partial p}))$ is PD on
    the **full** link-variable group `LinkVariable (SU N) Λ`.  This is
    `plaquetteBoltzmannPD_inv` (item 11) composed with `plaquetteProjection` via
    `PositiveDefinite.comp_hom` (item 9); the composition equals the plaquette
    factor because `plaquetteProduct` is exactly the `g₁ g₂ g₃⁻¹ g₄⁻¹` pattern
    that `plaquetteBoltzmannPD_inv` expects.
14. `plaquetteContributionPD` — the full plaquette contribution
    $\exp(-S_p) = \exp(-\beta)\cdot\exp((\beta/N)\,\operatorname{Re}\operatorname{Tr}(U_{\partial p}))$
    is PD on the full link-variable group, by `PositiveDefinite.smul_nonneg`
    applied to the non-negative constant $\exp(-\beta)$ and `plaquetteFactorPD`.
15. `boltzmannFactorPD` — the **full Boltzmann factor**
    $\exp(-S_W) = \prod_{n,\mu,\nu} \exp(-S_p(n,\mu,\nu))$ is PD on the full
    link-variable group `LinkVariable (SU N) Λ`.  The Wilson action is a sum of
    plaquette contributions, so the Boltzmann factor factorises as a product;
    each factor is PD by `plaquetteContributionPD` (item 14), and a finite
    product of PD functions on the same group is PD by
    `PositiveDefinite.finprod` (item 8, the n-ary Schur product theorem).  The
    proof flattens the product over `(sites ×ˢ Fin 4) ×ˢ Fin 4` via
    `Finset.prod_product`, pushes the negation through the nested sums via
    `Finset.sum_neg_distrib`, and applies `Real.exp_sum` three times.  0
    sorries, 0 custom axioms beyond the Peter–Weyl axiom, full `lake build`
    clean (2967 jobs).

**Mercer-PD kernel building blocks** are now proved in
`PositiveDefiniteIntegral.lean` (0 sorries, 0 custom axioms; full `lake build`
clean).  These are the algebraic ingredients needed to construct the TM kernel
as a Mercer-PD kernel from the group-PD `boltzmannFactorPD`:

16. `PositiveDefiniteKernel.conj_symm` — a Mercer-PD kernel is Hermitian:
    $K(x, y) = \overline{K(y, x)}$ (the kernel analogue of
    `PositiveDefinite.conj_inv`).
17. `PositiveDefiniteKernel.one` — the constant-one kernel is Mercer-PD.
18. `PositiveDefiniteKernel.matrix_posSemidef` (private) — a Mercer-PD kernel
    gives a positive-semidefinite matrix on any finite subset (the bridge to
    `Matrix.PosSemidef.hadamard`).
19. `PositiveDefiniteKernel.mul` — the **Schur (Hadamard) product theorem** for
    Mercer-PD kernels: the pointwise product of two Mercer-PD kernels is
    Mercer-PD (kernel analogue of `PositiveDefinite.mul`).
20. `PositiveDefiniteKernel.smul_nonneg` — non-negative scaling preserves
    Mercer-PD.
21. `PositiveDefiniteKernel.finprod` — a finite product of Mercer-PD kernels is
    Mercer-PD (n-ary Schur product theorem, kernel analogue of
    `PositiveDefinite.finprod`).
22. `PositiveDefiniteKernel.comp` — Mercer-PD is preserved by composition with a
    function $f : X \to Y$ on both arguments: if $K$ is Mercer-PD on $Y$, then
    $(x, y) \mapsto K(f(x), f(y))$ is Mercer-PD on $X$.  This is the key
    operation for composing the Boltzmann-factor kernel with the
    reflection/projection maps.
23. `PositiveDefiniteKernel.continuous_comp` — continuity of a Mercer-PD kernel
    is preserved by composition with a continuous function on both arguments
    (needed to apply `integralOperator_nonneg` to the composed TM kernel).

Together with `PositiveDefinite.toPositiveDefiniteKernel` (group-PD → Mercer-PD,
item 5), these allow the construction chain: group-PD Boltzmann factor →
Mercer-PD kernel → compose with reflection/projection maps → Mercer-PD TM kernel
→ `integralOperator_nonneg`.  The **remaining** gap is showing that the
concrete TM kernel (with the geometric reflection map $\theta^{-0}$) *is*
Mercer-PD — which still requires the Peter–Weyl character expansion to
decompose the Boltzmann factor into separable positive terms (approach (c)).

**The remaining work is the concrete wiring**: showing that the transfer-matrix
kernel (a product of plaquette Boltzmann factors, integrated over negative-time
links) is a PD function of the interface link variables — applying
`PositiveDefinite.integral` to integrate out the negative-time links from the
full Boltzmann factor (now proved PD by `boltzmannFactorPD`, item 15), and
finally applying `integralOperator_nonneg` to the resulting PD kernel.

**The character-orthogonality path (new)**: the `characterOrthogonality` axiom
(Schur orthogonality, now in `PositiveDefinite.lean`) provides the key
ingredient to turn the character expansion of the Boltzmann factor into a
`|Fourier coefficient|²` decomposition of the reflection-positivity integral.
The path: (1) expand `exp(-β S_W) = ∑_λ a_λ χ_λ` (Peter–Weyl), (2) substitute
into `∫ f(U)·f(θU)·exp(-β S_W) dμ` (shown equivalent to the axiom by
`osG_thetaG_factorization`), (3) use reflection-invariance of Haar measure +
`characterOrthogonality` to rewrite each term as `|∫ f·χ_λ|² ≥ 0`, (4) sum
with `a_λ ≥ 0`.  Steps 1–2 are formalized; steps 3–4 are the remaining wiring.

### Precise analysis of the character-orthogonality path (2026-06-29 session)

A detailed analysis of the character-orthogonality path was performed in the
2026-06-29 session.  The key findings are:

**The correct abstract lemma** is NOT at the level of the full Boltzmann
factor (where `χ_λ(θU) ≠ conj(χ_λ(U))` in general, so the naive
`|∫ f·χ_λ|²` decomposition fails).  It is at the level of the **transfer
matrix kernel**:

    K_TM(u, U⁻) = exp(-β·(S⁺(u)/2 + S⁻(U⁻)/2 + S_int(u, U⁻)))

If this kernel decomposes as

    K_TM(u, U⁻) = ∑_λ a_λ · Φ_λ(u) · conj(Φ_λ(θ⁻⁰(U⁻, u⁰)))

with `a_λ ≥ 0`, then (using `reflectLinkVariable_measurePreserving` for the
change of variables `U⁻ ↦ θ⁻⁰(U⁻, u⁰)`):

    ∫∫ g(u)·g(θ⁻⁰(U⁻, u⁰))·K_TM(u, U⁻) dμ⁻(U⁻) dμ⁺⁰(u)
    = ∑_λ a_λ · ∫_{u⁰} |∫_{u⁺} g(u⁺, u⁰)·Φ_λ(u⁺, u⁰) dμ⁺(u⁺)|² dμ⁰(u⁰) ≥ 0

The key steps are:
1. **Kernel decomposition** (the hard part): the interface Boltzmann factor
   `exp(-β·S_int)` has a character expansion that separates into
   `u`-dependent and `U⁻`-dependent parts, related by reflection.
2. **Change of variables**: `θ⁻⁰` maps `μ⁻` to `μ⁺` (by
   `reflectLinkVariable_measurePreserving`).
3. **Algebra**: the integral becomes a sum of `|Fourier coefficients|² ≥ 0`.

**The key obstruction** to formalizing step 1: the interface Boltzmann factor
is a **product of multiple interface plaquette factors**.  Each single
plaquette factor has a character expansion (by
`peterWeyl_clebschGordan_plaquette`), but the **product** of multiple
expansions involves **products of characters of the same link variable**
(when a link appears in multiple plaquettes).  Reducing such a product to a
sum of single characters requires the **Clebsch–Gordan decomposition**
`χ_s(g)·χ_t(g) = ∑_w N^w_{st} χ_w(g)` with `N^w_{st} ≥ 0`, which is NOT
currently axiomatized.  The existing `peterWeyl_clebschGordan_plaquette` axiom
bakes Clebsch–Gordan into the single-plaquette expansion, but does not
provide it as a separate tool for combining characters of the same group
element across different plaquettes.

**The abstract lemma to formalize** (no new axioms needed): if a kernel
`K : X → Y → ℂ` has a finite separable decomposition
`K(x, y) = ∑_i a_i · Φ_i(x) · conj(Φ_i(θ y))` with `a_i ≥ 0` and `θ`
measure-preserving (`θ_*ν = μ`), then for real-valued `f`:

    ∫∫ f(x) · f(θ y) · K(x, y) dν(y) dμ(x) = ∑_i a_i · |∫ f · Φ_i dμ|² ≥ 0

This is a pure measure-theory lemma (uses only `MeasurePreserving` for the
change of variables, no group structure, no character orthogonality).  It is
the abstract scaffold that the concrete character expansion would plug into.
Formalizing it is the natural next step; it was sketched but not completed in
the 2026-06-29 session (the integrability bookkeeping for exchanging the
finite sum with the integral needs care).

**Key obstruction**: the TM kernel
`(Tψ)(u) = ∫ ψ(θ⁻⁰(U⁻,u⁰))·exp(-β·(...)) dμ⁻(U⁻)` is NOT of the form
`φ(u⁻¹·v)` for a PD function `φ` on a group — the reflection map `θ⁻⁰` is a
geometric operation, not group multiplication.  While `PosInterfaceConfig` is a
product of SU(N)'s (hence a group), the kernel does not factor through the group
structure.  The Mercer framework (3–5 above) removes the *group-structure*
obstruction, but showing the TM kernel *is* Mercer-PD still requires the
Peter–Weyl character expansion to decompose the Boltzmann factor into separable
positive terms (approach (c)).  This is a fundamental mathematical gap, not just
formalization work.

**Fundamental obstruction (resolved by Peter–Weyl, not by the abstract lemmas)**:
The function $(g_1, g_2, g_3, g_4) \mapsto \exp(c \cdot \operatorname{Re} \operatorname{Tr}(g_1 g_2 g_3 g_4))$ is **NOT** positive-definite on $\text{SU}(N)^4$ for $N \ge 2$ as a naive composition, because even the simpler function $(g, h) \mapsto \operatorname{Tr}(gh)$ is NOT
positive-definite on $\text{SU}(N) \times \text{SU}(N)$. A concrete counterexample for
$N=2$ uses the Pauli matrices $i\sigma_1, i\sigma_2, i\sigma_3 \in \text{SU}(2)$:

With $(g_a, h_a) = (i\sigma_a, i\sigma_a)$ for $a=1,2,3$ and $c_a = 1$, the kernel matrix
$K_{ab} = \operatorname{Tr}(g_a^{-1} g_b h_a^{-1} h_b)$ has eigenvalues $-2, 4, 4$, giving
$\sum c_a \overline{c_b} K_{ab} = -6 < 0$.

The character expansion (Peter–Weyl) resolves this: $\exp(c \cdot \operatorname{Re} \operatorname{Tr}(g_1g_2g_3g_4)) = \sum_\lambda a_\lambda \sum_{\mu,\nu,\rho,\sigma} C_{\mu\nu\rho\sigma}^\lambda \chi_\mu(g_1) \chi_\nu(g_2) \chi_\rho(g_3) \chi_\sigma(g_4)$
where $a_\lambda \ge 0$, $C_{\mu\nu\rho\sigma}^\lambda \ge 0$ (Littlewood-Richardson), and each
$\chi_\mu(g_1) \chi_\nu(g_2) \chi_\rho(g_3) \chi_\sigma(g_4)$ is PD on $\text{SU}(N)^4$ (product of PD functions on
different factors). This decomposition is captured by the `peterWeyl_clebschGordan_plaquette` axiom and proved as `plaquetteBoltzmannPD` in `PeterWeyl.lean`.

See `docs/found_issues.md` §3 for the full analysis.

### Precise analysis of why `character_expansion_positivity` does NOT directly apply (2026-07-02 session)

A detailed analysis was performed of whether the abstract lemma
`character_expansion_positivity` (proved 2026-07-01, 0 sorries, 0 axioms) can
be directly wired into the lattice-gauge-theory setup to close
`transferMatrixPositivity_axiom`.  **The answer is no — three interconnected
obstructions prevent direct application.**  This section documents the precise
mathematical situation.

**Recap of the abstract lemma.**  `character_expansion_positivity` states: if
`K : X → Y → ℂ` has a finite separable decomposition
`K(x, y) = ∑_i a_i · Φ_i(x) · conj(Φ_i(θ y))` with `a_i ≥ 0` and
`θ : Y → X` measure-preserving (`θ_*ν = μ`), then for real-valued `f`:
`∫∫ f(x) · f(θ y) · K(x, y) dν dμ = ∑_i a_i · ‖∫ f · Φ_i dμ‖² ≥ 0`.

The lattice integral we need to show is ≥ 0 is (after `osG_thetaG_factorization`
and `integral_G_thetaG_eq_inner_g_Tg`):

    I = ∫_u ∫_{U⁻} g(u) · g(θ⁻⁰(U⁻, u⁰)) · K_TM(u, U⁻) dμ⁻(U⁻) dμ⁺⁰(u)

where `u = (u⁺, u⁰)` is a `PosInterfaceConfig` (positive + interface links),
`U⁻` is a negative config, `θ⁻⁰(U⁻, u⁰)` is the reflection from negative +
interface to positive + interface, and `K_TM` is the transfer-matrix kernel.

**Obstruction 1: `θ⁻⁰` depends on both `x` and `y`.**  The lemma requires
`θ : Y → X` (a function of `y` only).  But `θ⁻⁰(U⁻, u⁰)` depends on `u⁰`,
which is part of `x = u = (u⁺, u⁰)`.  So `θ` is NOT a function of `y` only —
it depends on `x` too.  The lemma's proof uses the change of variables
`z = θ y` (for the inner integral over `y`), which requires `θ` to be a
function of `y` only.  With `x`-dependent `θ`, the change of variables gives
a result that depends on `x`, preventing the factorization into
`|∫ f · Φ_i dμ|²`.

**Obstruction 2: the pushforward of `μ⁻` by `θ⁻⁰(·, u⁰)` is singular.**  Even
if we generalize the lemma to allow `x`-dependent `θ`, the proof requires
(for each fixed `x`) that `θ(x, ·)` be measure-preserving from `ν` to `μ`
(the FULL measure on `X`).  In our case, for fixed `u⁰`, the map
`θ⁻⁰(·, u⁰) : U⁻ → PosInterfaceConfig` sends `μ⁻` to `μ⁺ × δ_{σ(u⁰)}`
(the product of the positive Haar measure and a POINT MASS at the reflected
interface config `σ(u⁰)`).  This is NOT the full measure `μ⁺⁰ = μ⁺ × μ⁰`.
The image is a "slice" (fixed interface part), not the whole space.  So the
change of variables gives an integral over a slice, not the full space, and
the factorization into `|∫ f · Φ_i dμ|²` fails.

**Obstruction 3: the `σ` reflection on interface time-like links.**  The
reflection `θ` on link variables is:
- `(θ U)(n, μ) = U(θn, μ)⁻¹` if `μ = 0` (time direction)
- `(θ U)(n, μ) = U(θn, μ)` if `μ ≠ 0` (spatial direction)

For interface sites (`signedTime = 0`), `θn = n` (since `-0 = 0` in `ZMod T`).
So on interface links:
- Time-like (`μ = 0`): `(θ U)(n, 0) = U(n, 0)⁻¹` — **inverted**
- Spatial (`μ ≠ 0`): `(θ U)(n, μ) = U(n, μ)` — **unchanged**

Define `σ` as this reflection on interface links (invert time-like, keep
spatial).  Then `g(θ⁻⁰(U⁻, u⁰))` has interface part `σ(u⁰)`, while `g(u)`
has interface part `u⁰`.  These are DIFFERENT (for time-like links).

Even if we split the integral `∫_u = ∫_{u⁰} ∫_{u⁺}` and apply the lemma for
each fixed `u⁰` (making `θ⁻⁰(·, u⁰)` a function of `y` only), the result is:

    I = ∑_i a_i · ∫_{u⁰} A_i(u⁰) · conj(A_i(σ(u⁰))) dμ⁰(u⁰)

where `A_i(u⁰) = ∫_{u⁺} g(u⁺, u⁰) · Φ_i(u⁺, u⁰) dμ⁺(u⁺)`.  This is
`⟨A_i, A_i ∘ σ⟩_{L²(μ⁰)}`, which is **NOT necessarily non-negative** — it is
the inner product of `A_i` with `A_i ∘ σ`, not `‖A_i‖²`.

The root cause: for interface time-like links, the reflection inverts the
link (`g ↦ g⁻¹`), and `χ(g⁻¹) = conj(χ(g))` by `repCharacter_inv`.  In the
separable form `Φ_i(u) · conj(Φ_i(θ⁻⁰(U⁻, u⁰)))`, the inversion + conjugation
gives `χ(g) · χ(g) = χ(g)²` for interface time-like links, NOT
`χ(g) · conj(χ(g)) = |χ(g)|²`.  And `χ(g)²` is complex in general, not
non-negative.

**Why the OS proof still works.**  The Osterwalder–Seiler proof does NOT
directly show the integral is a sum of `|Fourier coefficients|²` via
`character_expansion_positivity`.  Instead, it shows the transfer matrix `T`
is a **positive operator** by demonstrating `T = B* · B` for some operator `B`
defined via the character expansion (or equivalently, by showing the kernel of
`T` is a positive-definite kernel on the interface config space, after a
proper change of variables that accounts for `σ`).  The positivity
`⟨g, Tg⟩ ≥ 0` then follows from `⟨g, B* B g⟩ = ‖Bg‖² ≥ 0`.

The operator `B` involves the Peter–Weyl character expansion of the Boltzmann
factor, combined across plaquettes via the Clebsch–Gordan decomposition.  The
key steps are:
1. Expand each interface plaquette factor in characters (Peter–Weyl).
2. For interface time-like links appearing in both a plaquette `p` and its
   reflection `θp`, the product `χ_s(g) · conj(χ_t(g))` arises.  This is a
   matrix coefficient of `ρ_s ⊗ ρ_t*`, decomposable via CG into
   `∑_w N^w_{s,t*} χ_w(g)` with `N^w_{s,t*} ≥ 0`.
3. For links appearing in multiple plaquettes, CG reduces products of
   characters of the same link to single characters.
4. The resulting decomposition defines the operator `B` (Fourier coefficient
   extraction), and `T = B* · B` gives positivity.

This is a fundamentally different argument from `character_expansion_positivity`,
which tries to directly show the integral is a sum of `|coefficients|²`.  The
lattice case requires the operator-theoretic approach (`T = B* B`), not the
direct integral approach.

**What's needed to close `transferMatrixPositivity_axiom`:**
1. **Clebsch–Gordan axiom**: `χ_s(g) · χ_t(g) = ∑_w N^w_{st} χ_w(g)` with
   `N^w_{st} ≥ 0` (Littlewood–Richardson).  **DONE (2026-07-03 session):**
   the existing `peterWeyl_clebschGordan_plaquette` axiom has been
   **strengthened** to also provide this decomposition (as additional
   existential components `cg`, `hcg`, `hcg_decomp`).  Two new lemmas proved
   from it (0 sorries, 0 custom axioms — verified by `#print axioms`):
   `charProduct_PD` (product of two chars is PD via CG) and
   `charProduct_finset_decomp` (finite product of chars of the same element
   decomposes as a non-negative-weighted sum of single characters via iterated
   CG).  Two further lemmas proved from the strengthened axiom (0 sorries, 0
   custom axioms — verified by `#print axioms`): `charSum_product_decomp`
   (product of two non-negative-weighted char sums decomposes as a
   non-negative-weighted char sum via CG) and `charSum_finprod_decomp`
   (finite product of non-negative-weighted char sums decomposes as a
    non-negative-weighted char sum via iterated CG), and
     `charSum_product_link_decomp` (product of per-link character sums decomposes
     as a non-negative-weighted sum of products of characters — the separable
     decomposition of the full Boltzmann factor).  Two further lemmas proved
     (2026-07-05 session, 0 sorries, 0 custom axioms — verified by `#print
     axioms`: only `propext`, `Classical.choice`, `Quot.sound`):
     `charProduct_finset_decomp'` (generalized CG decomposition for a product of
     characters indexed by a finset of *appearances* `A` via `appChar : A → ι`,
     handling the case where the same character index appears multiple times —
     which happens when a single link variable appears in multiple plaquettes
     with the same representation index) and `charProduct_link_separable_decomp`
     (per-term separable decomposition: a product of characters grouped by link
     `∏_l (∏_{a ∈ S_l} χ_{charIdx l a}(g_l))` decomposes as a non-negative-weighted
     sum of products of single characters `∑_w F(w) · ∏_l χ_{w(l)}(g_l)` — this
     is the key algebraic ingredient for the interface Boltzmann factor
     decomposition, combining per-link CG with the product-of-sums identity).  The
     axiom count remains **six** (the strengthening enriches an existing axiom,
     it does not add a new one).
     
     The axiom was **further strengthened** (2026-07-30 session) to also provide a
     dual (contragredient) map `dual : ι → ι` with
     `repCharacter (ρ (dual i)) g = conj (repCharacter (ρ i) g)` — the standard
     fact that the contragredient of a unitary representation has conjugate
     character.  This is needed because the lattice plaquette product has
     **inverted links** (`g₃⁻¹, g₄⁻¹`), and `χ(g⁻¹) = conj(χ(g)) = χ_{dual}(g)`
     by `repCharacter_inv`.  Two further lemmas proved from the strengthened
     axiom (2026-07-30 session, 0 sorries, 0 custom axioms — verified by
     `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`):
     `charProduct_mixed_finset_decomp'` (mixed-conjugation CG decomposition: a
     product of characters with mixed conjugation — some `χ(g)`, some
     `conj(χ(g))` — of the same group element decomposes as a non-negative-
     weighted sum of single characters, using the dual map to convert
     `conj(χ)` to `χ_{dual}` and then applying `charProduct_finset_decomp'`)
     and `charProduct_mixed_link_separable_decomp` (per-term separable
     decomposition with mixed conjugation: a product of characters with mixed
     conjugation grouped by link decomposes as a non-negative-weighted sum of
     products of single unconjugated characters — this is the key algebraic
     ingredient for the interface Boltzmann factor decomposition with inverted
     links, combining per-link mixed-conjugation CG with the product-of-sums
     identity).  The axiom count remains **six**.
 2. **Formalization of the operator `B`**: define `B` via the character
    expansion, show `T = B* · B`, and conclude `⟨g, Tg⟩ = ‖Bg‖² ≥ 0`.  This
    requires the full combinatorial wiring of the interface plaquette expansion
    (which links belong to which plaquettes, the reflection structure, the CG
    reduction) — a major formalization effort.  **This is the remaining work.**
    The per-term separable decomposition (`charProduct_link_separable_decomp`)
    is now proved; the remaining steps are:
    (a) Expand the product of plaquette factors (product of sums = sum of
        products) and apply `charProduct_link_separable_decomp` to each term to
        get the full separable decomposition of the interface Boltzmann factor.
    (b) Change variables in the transfer-matrix integral (reflecting negative
        links to positive), using `reflectLinkVariable_measurePreserving`.
    (c) Use CG (with dual representations, via `repCharacter_inv`) to combine
        the reflected characters with the unreflected ones.
    (d) Use `characterOrthogonality` to evaluate the integrals and obtain
        `∑_w a_w · |Fourier coefficient|² ≥ 0`.
3. **Alternatively**: axiomatize the separable decomposition of the TM kernel
   directly (as a consequence of Peter–Weyl + CG + character orthogonality),
   and prove positivity from it.  This would replace
   `transferMatrixPositivity_axiom` with a more fundamental representation-
   theoretic axiom, but would not reduce the axiom count (6 → 6) unless the
   CG content is folded into the existing `peterWeyl_clebschGordan_plaquette`
   axiom (6 → 5).  **The CG content is now folded in (step 1 done); closing
   `transferMatrixPositivity_axiom` would reduce the count to 5.**

**Key insight for future sessions**: the `character_expansion_positivity`
lemma, while a valuable abstract result, is NOT the right scaffold for the
lattice case.  The correct approach is the operator-theoretic `T = B* B`
argument, which requires CG and the full plaquette combinatorics.  The
abstract lemma's requirement that `θ : Y → X` be a function of `y` only (and
measure-preserving to the FULL measure on `X`) is fundamentally incompatible
with the lattice setup's shared interface structure and the `σ` reflection on
interface time-like links.

### ✅ Clean factorization PROVEN (2026-06-29)

The lemma `osG_thetaG_factorization` (in `ReflectionPositivity.lean`, 0 sorries,
0 axioms) proves the purely algebraic identity:

$$\texttt{osG}(U) \cdot \texttt{osG}(\theta U) = f(U) \cdot f(\theta U) \cdot \exp(-\beta S_W(U))$$

This follows from the reflection symmetries $S^+_{OS}(\theta U) = S^-_{OS}(U)$ and
$S^0_{OS}(\theta U) = S^0_{OS}(U)$, together with the action decomposition
$S_W = S^+_{OS} + S^-_{OS} + S^0_{OS}$.  No support hypothesis on $f$ is needed.

This shows that `transferMatrixPositivity_axiom` is equivalent to:

$$\int f(U) \cdot f(\theta U) \cdot \exp(-\beta S_W(U)) \, d\mu_0(U) \ge 0$$

where $\exp(-\beta S_W)$ is the full Boltzmann factor, proved positive-definite on
the full link-variable group by `boltzmannFactorPD` (item 15).

### ❌ Why PD-ness of the Boltzmann factor is NOT sufficient

The integral $\int f(U) \cdot f(\theta U) \cdot \exp(-\beta S_W(U)) \, d\mu_0(U)$
is **NOT** the standard positive-definite quadratic form

$$\iint f(g)\,\overline{f(h)}\,K(g^{-1} h)\,d\mu(g)\,d\mu(h) \ge 0$$

which follows from PD-ness of $K$ on a group (proven as
`PositiveDefinite.integralOperator_nonneg`).  Instead, it is a **single** integral
$\int f(g)\,f(\theta g)\,K(g)\,d\mu(g)$ with:

1. The **geometric reflection** $\theta$ (not group multiplication or inversion).
2. $K$ evaluated at $g$ (not $g^{-1} h$ — there is no "second variable" $h$).
3. $f(\theta g)$ (not $\overline{f(h)}$ — no complex conjugation, and the argument
   is $\theta g$, not $h$).

PD-ness of $K = \exp(-\beta S_W)$ on the group does **not** imply this integral is
non-negative.  The Peter–Weyl character expansion of $K$ and character
orthogonality are needed to decompose the integrand into $|\text{Fourier
coefficients}|^2$, which are manifestly non-negative.  This is the fundamental
mathematical gap that remains.

## Why This Is Non-Trivial

The integrand $G(U) \cdot G(\theta U)$ is **not pointwise non-negative**. The
non-negativity holds only after integration. This is the essence of reflection
positivity: it is a global property of the measure, not a pointwise one.

## Mathematical Proof (Osterwalder-Seiler 1979, §3)

### Step 1: Measure factorization

The links are partitioned into three sets:
- $L^+$: links with positive signed time
- $L^-$: links with negative signed time
- $L^0$: links at the time interface (signed time = 0)

The product Haar measure factorizes:
$$\mu_0 = \mu^+ \otimes \mu^- \otimes \mu^0$$

### Step 2: Transfer matrix

Define the transfer matrix $T$ acting on $L^2(\mu^+ \otimes \mu^0)$ by:

$$(T\psi)(U^+, U^0) = \int_{U^-} \psi(U^-, U^0) \cdot K(U^+, U^-, U^0) \, d\mu^-(U^-)$$

where $K(U^+, U^-, U^0) = \exp(-\beta \cdot S^0_{OS}(U^+, U^-, U^0))$ is the
interface Boltzmann factor.

### Step 3: Key identity

$$\int G(U) G(\theta U) \, d\mu_0 = \langle G^+, T G^+ \rangle_{L^2(\mu^+ \otimes \mu^0)}$$

where $G^+$ is the restriction of $G$ to $L^+ \cup L^0$.

### Step 4: Positivity of $T$

The transfer matrix $T$ is a **positive operator** (self-adjoint with non-negative
spectrum). This follows from the Peter-Weyl theorem on $\text{SU}(N)$:

1. The kernel $K(U^+, U^-, U^0)$ is a product over interface plaquettes:
   $$K = \prod_{\text{interface plaquettes } p} \exp\left(\frac{\beta}{N} \operatorname{Re} \operatorname{Tr}(U_{\partial p})\right)$$

2. For a single plaquette, the function $\exp(c \operatorname{Re} \operatorname{Tr}(g))$ on
   $\text{SU}(N)$ can be expanded in characters (representations):
   $$\exp(c \operatorname{Re} \operatorname{Tr}(g)) = \sum_{\lambda} a_\lambda(c) \chi_\lambda(g)$$
   with $a_\lambda(c) \ge 0$ for $c > 0$.

3. The characters $\chi_\lambda$ are positive-definite functions on $\text{SU}(N)$,
   and the tensor product of positive-definite functions is positive-definite.

4. By the Peter-Weyl theorem, the matrix elements of irreducible representations
   form an orthonormal basis of $L^2(\text{SU}(N))$, and any positive-definite
   function expands with non-negative coefficients in this basis.

5. Therefore $K$ is a positive-definite kernel, $T$ is a positive operator,
   and $\langle G^+, T G^+ \rangle \ge 0$.

## Required Mathlib Infrastructure

### 1. Peter-Weyl Theorem for $\text{SU}(N)$

**Not yet in Mathlib.** The following pieces are needed:

| Piece | Status in Mathlib | Notes |
|-------|-------------------|-------|
| Compact Lie group $\text{SU}(N)$ | Done (`SpecialUnitary.lean`) | Topological group, compactness, Haar measure |
| Representation theory of compact groups | Partial | `RepresentationTheory/` covers finite groups |
| Unitary irreps of $\text{SU}(N)$ | Not available | Requires highest weight theory |
| Peter-Weyl theorem | Not available | $L^2(G) \cong \bigoplus_\lambda V_\lambda \otimes V_\lambda^*$ |
| Characters of irreps | Partial (finite groups) | `RepresentationTheory/Character` |
| Orthogonality of characters | Partial (finite groups) | |
| Positive-definite functions on groups | Not available | |
| Bochner theorem for compact groups | Not available | |

### 2. Transfer Matrix Framework

**Nothing in Mathlib.** The following need to be built:

| Component | Description |
|-----------|-------------|
| $L^2$ space on $\text{SU}(N)^n$ | Built on existing measure theory |
| Integral operators on $L^2$ | As kernel operators |
| Positivity of operators | Spectral theory of bounded operators |
| Product measures and Fubini | Available in Mathlib |

### 3. Character Expansion of Wilson Action

| Component | Description |
|-----------|-------------|
| Expansion of $\exp(c \operatorname{Re} \operatorname{Tr}(g))$ in characters | Requires representation theory |
| Positivity of expansion coefficients | Known result (Osterwalder-Seiler) |
| Factorization over plaquettes | Already done algebraically |

## Alternative Approaches

### A. Product of PD on different factors (✅ PROVEN)

The lemma `PositiveDefinite.prod` (in `PositiveDefinite.lean`) proves that if
`φ : G → ℂ` is positive-definite and `ψ : H → ℂ` is positive-definite, then
`(g, h) ↦ φ(g) * ψ(h)` is positive-definite on `G × H`.

**Proof**: For any finset `s ⊂ G × H` and coefficients `c`, define matrices
`A_{ij} = φ(g_i⁻¹ g_j)` and `B_{ij} = ψ(h_i⁻¹ h_j)`. Both are PSD by the
grouping argument (`PositiveDefinite.sum_nonneg_of_map`), which handles
non-injective maps `f : α → G` by regrouping the quadratic form by fibers.
By the Schur product theorem (`Matrix.PosSemidef.hadamard`), `A ⊙ B` is PSD,
and the quadratic form of `A ⊙ B` equals the PD sum for the product function.

This is one of the three ingredients needed for the character expansion approach
(see `docs/found_issues.md` §3). The remaining ingredients are:
1. ✅ Product of PD on different factors — **PROVEN** (`PositiveDefinite.prod`)
2. ❌ Peter-Weyl theorem: `exp(c·Re Tr(g)) = ∑_λ a_λ χ_λ(g)` with `a_λ ≥ 0`
3. ❌ Clebsch-Gordan decomposition: `χ_λ(gh) = ∑_{μ,ν} N^λ_{μν} χ_μ(g) χ_ν(h)`

### B. Heat Kernel Approach

Instead of the character expansion, one could use the heat kernel on $\text{SU}(N)$:

$$\exp\left(\frac{\beta}{N} \operatorname{Re} \operatorname{Tr}(g)\right) = \int_{\mathfrak{su}(N)} e^{\langle X, \log g \rangle} \, d\mu_\beta(X)$$

where $\mu_\beta$ is a Gaussian measure on the Lie algebra $\mathfrak{su}(N)$.
This represents the Boltzmann factor as the Fourier transform of a positive measure,
which is automatically positive-definite.

**Status in Mathlib**: 
- Gaussian measures: Available (`Mathlib/MeasureTheory/`)
- Lie algebra $\mathfrak{su}(N)$: Defined as `LieAlgebraSU` in `SpecialUnitary.lean`
- Matrix exponential: Not available
- Fourier transform on Lie groups: Not available

### B. Reflection Positivity per Plaquette

One could attempt to prove that each individual plaquette contribution is
reflection-positive, and then use the fact that the product of reflection-positive
functions is reflection-positive. This would reduce the problem to proving
reflection positivity for a single plaquette.

**Status**: This is essentially equivalent to the character expansion approach,
since a single plaquette is the fundamental building block.

### C. Finite Lattice Spectral Argument

For a strictly finite lattice, the transfer matrix is a finite-rank operator
(acting on a finite-dimensional space if we discretize the group... but SU(N) is
continuous, so still infinite-dimensional).

### Current Status

The corrected transfer matrix framework has been implemented in `TransferMatrix.lean`:

- **`reflectToPosInterface`**: The map θ⁻⁰ from negative+interface to positive+interface.
- **`g_posInterface`**: The restricted function `g(u) = f(u)·exp(-β·S_OS⁺(u)/2)`.
- **`transferMatrixCorrect`**: The correct transfer matrix with reflection kernel.
- **`integral_G_thetaG_eq_inner_g_Tg`**: ✅ PROVEN (0 sorries). The key identity.
- **`transferMatrixCorrect_positive`**: ❌ BLOCKED — requires Peter-Weyl theorem.
  See `docs/found_issues.md` §3 for the precise obstruction (counterexample showing
  `Tr(gh)` is not PD on `SU(N) × SU(N)`).
- **`integral_G_thetaG_nonneg'`**: Depends on the above.

### Remaining Steps:

### Short-term (measure-theoretic bookkeeping, no representation theory):

1. **Prove `integral_G_thetaG_eq_inner_g_Tg`**: ✅ DONE. The identity
   ∫ G(U)·G(θU) dμ₀ = ∫ g(u)·(T g)(u) dμ⁺⁰(u)
   is fully proven using `measure_factorization'`, the action reflection lemmas, Haar measure
   invariance under reflection, and the definition of `transferMatrixCorrect`.
   This is purely measure-theoretic — no representation theory is needed.

### Medium-term (requires representation theory — BLOCKED):

2. **Prove `transferMatrixCorrect_positive`**: ❌ BLOCKED. The transfer matrix T is positive
   iff its kernel is a positive-definite function on the link-variable group. The kernel is a
   product of plaquette factors exp(c·Re Tr(U_∂p)), and each factor must be PD on SU(N)^4.

   **Obstruction**: The function (g,h) ↦ Tr(gh) is NOT positive-definite on SU(N) × SU(N)
   for N ≥ 2 (counterexample with Pauli matrices, see `docs/found_issues.md` §3). The
   multiplication map SU(N)^k → SU(N) is NOT a group homomorphism for non-abelian groups,
   so composing a PD function with it does NOT preserve PD-ness.

   **What's needed**: The character expansion (Peter-Weyl theorem) decomposes
   exp(c·Re Tr(g₁g₂g₃g₄)) into a sum of products χ_μ(g₁)·χ_ν(g₂)·χ_ρ(g₃)·χ_σ(g₄)
   with non-negative coefficients, where each factor is a PD function on SU(N). This
   requires:
   - Peter-Weyl theorem for compact Lie groups (NOT in Mathlib)
   - Clebsch-Gordan / Littlewood-Richardson decomposition (NOT in Mathlib)
   - Character expansion of exp(c·Re Tr(g)) with non-negative coefficients (NOT in Mathlib)

3. **Prove `exp_reTrace_positiveDefinite`** (`PositiveDefinite.lean`): ✅ DONE.
   exp(c Re Tr(g)) is positive-definite on SU(N) for c ≥ 0. This is the core analytic fact
   needed for (2), but it is NOT SUFFICIENT by itself — the composition with the plaquette
   product map does not preserve PD-ness for non-abelian groups.

### Long-term (upstream to Mathlib):

1. **Peter-Weyl theorem** for compact Lie groups
2. **Character theory** for compact (not just finite) groups
3. **Positive-definite functions** and Bochner's theorem for compact groups

1. K. Osterwalder, E. Seiler, "Gauge Field Theories on a Lattice"
   (Ann. Phys. 110, 1978, pp 440–471), §3.
   - The original proof of reflection positivity for lattice gauge theories.
   - Uses the character expansion and Peter-Weyl theorem.

2. M. Lüscher, "General Proof of Osterwalder-Schrader Positivity for the
   Wilson Action" (Commun. Math. Phys. 113, 1987, pp 311–325).
   - Alternative proof using explicit transfer matrix construction.
   - Does not require fermions.

3. P. Menotti, A. Pelissetto, "General Proof of Osterwalder-Schrader Positivity
   for the Wilson Action" (Commun. Math. Phys. 113, 1987, pp 369–373).
   - Extension to reflections about planes containing sites.

4. J. Glimm, A. Jaffe, "Quantum Physics" (2nd ed.), §6.1.
   - Textbook treatment of reflection positivity.

5. M. Salmhofer, "Construction of a Higgs field" (thesis, 1990).
   - Detailed treatment of the transfer matrix for lattice gauge theories.

6. T. Bröcker, T. tom Dieck, "Representations of Compact Lie Groups"
   (Springer, 1985).
   - Standard reference for the Peter-Weyl theorem.
