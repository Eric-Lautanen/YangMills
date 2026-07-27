# Gap Analysis: Correct Reflection Positivity Proof

## Current Status

The reflection positivity proof for the Wilson action on a finite periodic lattice
(`gibbsExpectationPeriodic_reflection_positive` in `ReflectionPositivity.lean`)
is complete except for the final positivity step (the integral of G·θG).

### ✅ Correction applied (2025-06-28)

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

### ✅ Key identity PROVEN (2025-06-28)

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

**The remaining work is the concrete wiring**: showing that the transfer-matrix
kernel (a product of plaquette Boltzmann factors, integrated over negative-time
links) is a PD function of the interface link variables — applying
`PositiveDefinite.integral` to the plaquette factors (themselves PD by
`plaquetteBoltzmannPD`, modulo the Peter–Weyl axiom) — and then applying
`integralOperator_nonneg` to the resulting PD kernel.

**Key obstruction**: the TM kernel
`(Tψ)(u) = ∫ ψ(θ⁻⁰(U⁻,u⁰))·exp(-β·(...)) dμ⁻(U⁻)` is NOT of the form
`φ(u⁻¹·v)` for a PD function `φ` on a group — the reflection map `θ⁻⁰` is a
geometric operation, not group multiplication.  While `PosInterfaceConfig` is a
product of SU(N)'s (hence a group), the kernel does not factor through the group
structure.  Closing the axiom requires either (a) a more general PD kernel
theory (Mercer-type), (b) showing the TM kernel reduces to the group-theoretic
form, or (c) applying the Peter–Weyl character expansion directly to the TM
kernel.  This is a fundamental mathematical gap, not just formalization work.

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
