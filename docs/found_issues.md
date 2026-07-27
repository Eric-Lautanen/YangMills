# Found Issues (2025-06-28)

## 1. Reflection positivity lemma was stated with too-weak hypothesis

### What was wrong

The lemma `gibbsExpectationPeriodic_reflection_positive` in
`ReflectionPositivity.lean` originally claimed:

```lean4
lemma gibbsExpectationPeriodic_reflection_positive (N T L : ℕ) (β : ℝ) [NeZero T] [NeZero L]
    (hT : Odd T) (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ) :
    0 ≤ gibbsExpectation N β (PeriodicSite T L) (Finset.univ : Finset (PeriodicSite T L))
      (λ U => f U * reflectObservable N f U) := ...
```

This claims that for **any** function `f` (depending on all link variables),
the integral `∫ f(U)·f(θU)·exp(-β·S_W(U)) dμ₀(U)` is non-negative.

This is **mathematically false**. A counterexample exists even for β=0 (free theory):

Take a positive-site link ℓ and its reflection θℓ (a distinct negative-site link).
Define:
```
f(U) = a(U(ℓ))·b(U(θℓ)) - a(U(θℓ))·b(U(ℓ))
```
for non-zero functions a,b: SU(N) → ℝ.

Then `f(θU) = -f(U)`, so `f·θf = -(f)² ≤ 0`, and the integral is strictly negative.

### The fix

The correct Osterwalder-Schrader theorem requires `f` to depend only on links in
the **positive-time region** (including the interface at time 0).  The predicate
`dependsOnlyOnPosInterface` enforces this:

```lean4
def dependsOnlyOnPosInterface (N T L : ℕ) [NeZero T] [NeZero L]
    (f : LinkVariable (SU N) (PeriodicSite T L) → ℝ) : Prop :=
  ∀ (U V : LinkVariable (SU N) (PeriodicSite T L)),
    (∀ (n : PeriodicSite T L) (μ : Fin 4),
      n ∈ (positiveSites T L ∪ interfaceSites T L) → U.value n μ = V.value n μ) → f U = f V
```

The lemma now takes `(hf_supported : dependsOnlyOnPosInterface N T L f)` as an
additional hypothesis.

### Impact

- `PeriodicExpectation.reflectionPositive` field now requires the hypothesis.
- `lattice_ym_reflection_positive_periodic` theorem now requires the hypothesis.
- The `Z4Expectation` structure (in the same file) has a similar issue but is
  already known to be vacuous for nonempty lattices due to the `hadd` issue.

## 2. `transferMatrix_identity` in TransferMatrix.lean is incorrect

### What was wrong

The lemma claimed:

```
∫ G(U)·G(θU) dμ₀(U) = ∫ G_plus(u)·(T G_plus)(u) dμ⁺⁰(u)
```

where `G_plus(u) = G(U⁺, 𝟙, U⁰)` (negative links set to 1).  This is false
because:

1. `G` depends on negative links through `f` and `S_OS_int`, while `G_plus`
   replaces negative links with 1.
2. `transferMatrix_positive` shows `(T ψ)(u) = ψ(u)·(positive kernel)` because
   `restrict_merge_id` makes `ψ(restrictPosInterface(merge(U⁻, u))) = ψ(u)`,
   independent of U⁻.  This means T is a **multiplication operator**, not a
   genuine transfer matrix that couples positive and negative configurations.

### Current status (2025-06-28, corrected)

The corrected transfer matrix has been implemented in `TransferMatrix.lean`:

- **`reflectToPosInterface`**: The map θ⁻⁰ from negative+interface to positive+interface.
  Uses the `onePosInterface` (identity on positive links) plus U_zero on interface links,
  then applies the full reflection and restricts to positive+interface sites.

- **`g_posInterface`**: The function g(u) = f(u)·exp(-β·S_OS⁺(u)/2) for u ∈ PosInterfaceConfig.
  Depends only on positive+interface links because f does (by `hf_supported`).

- **`osPositiveOfPosInterface`**: Extracts S_OS⁺(U⁺) from a positive+interface config.

- **`transferMatrixCorrect`**: The correct transfer matrix with kernel
  ```
  (T ψ)(u) = ∫ ψ(θ⁻⁰(U⁻, u⁰))
              · exp(-β·(S_OS⁺(u)/2 + S_OS⁻(U⁻)/2 + S_OS_int(u, U⁻)))
              dμ⁻(U⁻)
  ```

  The kernel is chosen so that the key identity holds:
  ```
  g(u)·(T g)(u) = ∫ G(U)·G(θU) dμ⁻(U⁻)    (for each fixed U⁺,U⁰)
  ```

### Remaining work

1. **`integral_G_thetaG_eq_inner_g_Tg`**: ✅ PROVEN (0 sorries). The measure-theoretic identity
   ∫ G(U)·G(θU) dμ₀(U) = ∫_{PosInt} g(u)·(T g)(u) dμ⁺⁰(u)
   is fully proven using `measure_factorization'`, the action reflection lemmas, and the
   definitions of `transferMatrixCorrect` and `g_posInterface`.

2. **`transferMatrixCorrect_positive`**: ❌ BLOCKED — requires Peter-Weyl theorem for SU(N).
   See §3 below for the precise mathematical obstruction.

   **Progress**: Both abstract sub-steps of the positivity chain are now proved
   in `PositiveDefiniteIntegral.lean` (0 sorries, 0 custom axioms):
   - `PositiveDefinite.integral` — an integral average of PD functions is PD
     (closes "integrate out interior links ⟹ PD kernel").
   - `PositiveDefinite.integralOperator_nonneg` — a PD kernel on a compact
     group defines a positive integral operator
     (`∫∫ f(x)·conj(f(y))·K(x⁻¹y) dμ dμ ≥ 0`).
   The **remaining** work is the concrete wiring: showing the transfer-matrix
   kernel is a PD function of the interface link variables (via
   `PositiveDefinite.integral` applied to the plaquette factors, themselves PD
   by `plaquetteBoltzmannPD` modulo the Peter–Weyl axiom), then applying
   `integralOperator_nonneg`.  **Key obstruction**: the TM kernel
   `(Tψ)(u) = ∫ ψ(θ⁻⁰(U⁻,u⁰))·exp(-β·(...)) dμ⁻(U⁻)` is NOT of the form
   `φ(u⁻¹·v)` for a PD function `φ` on a group — the reflection map `θ⁻⁰` is a
   geometric operation, not group multiplication.  While `PosInterfaceConfig`
   is a product of SU(N)'s (hence a group), the kernel does not factor through
   the group structure.  Closing the axiom requires either (a) a more general
   PD kernel theory (Mercer-type), (b) showing the TM kernel reduces to the
   group-theoretic form, or (c) applying the Peter–Weyl character expansion
   directly to the TM kernel.  This is a fundamental mathematical gap, not
   just formalization work.

3. **`gibbsExpectationPeriodic_reflection_positive`**: The final `sorry` in
   `ReflectionPositivity.lean` (line 1437) that depends on (2).

See `docs/gap_analysis.md` and `src/lean/YangMills/Proofs/TransferMatrix.lean` for details.

## 3. Tr(gh) is NOT positive-definite on SU(N) × SU(N) — fundamental obstruction

### The key question

The Osterwalder-Seiler proof requires showing that the plaquette Boltzmann factor
`exp(c · Re Tr(U₁U₂U₃U₄))` is a positive-definite function on `SU(N)^4` (the product
group of link variables around a plaquette). Since `exp(c · Re Tr(g))` is PD on `SU(N)`
(proven in `PositiveDefinite.lean`), the natural approach is to show that the composition
of a PD function with the multiplication map `m: SU(N)^4 → SU(N)` preserves PD-ness.

This reduces to: **is `(g,h) ↦ Tr(gh)` positive-definite on `SU(N) × SU(N)`?**

### Counterexample: Tr(gh) is NOT PD on SU(2) × SU(2)

Take three points in `SU(2) × SU(2)` with coefficients `c₁ = c₂ = c₃ = 1`:
- `(g₁, h₁) = (iσ₁, iσ₁)`
- `(g₂, h₂) = (iσ₂, iσ₂)`
- `(g₃, h₃) = (iσ₃, iσ₃)`

where `iσ_k` are the Pauli matrices (elements of SU(2) with trace 0 and square -I).

The kernel matrix `K_{ab} = Tr(g_a⁻¹ g_b h_a⁻¹ h_b)` is:

```
K = [[ 2, -2, -2],
     [-2,  2, -2],
     [-2, -2,  2]]
```

- Diagonal: `K_{aa} = Tr(I) = 2`.
- Off-diagonal: `K_{ab} = Tr((g_a⁻¹ g_b)²) = Tr(-I) = -2` (since `g_a⁻¹ g_b` is a
  Pauli matrix, whose square is `-I`).

Eigenvalues: **-2** (eigenvector [1,1,1]), 4, 4.

The quadratic form `∑ c_a conj(c_b) K_{ab} = c* K c = -6 < 0` for `c = [1,1,1]`.

### Why this matters

This counterexample proves that:
1. `(g,h) ↦ Tr(gh)` is **NOT** positive-definite on `SU(N) × SU(N)` for `N ≥ 2`.
2. The multiplication map `m: G^k → G` does **NOT** preserve positive-definiteness for
   non-abelian groups (it is not a group homomorphism).
3. The plaquette Boltzmann factor `exp(c · Re Tr(U₁U₂U₃U₄))` is **NOT** positive-definite
   on `SU(N)^4` as a function of the link variables.
4. The transfer matrix positivity **cannot** be proven by simply composing
   `exp_reTrace_positiveDefinite` with the plaquette product map.

### What IS true (and why Peter-Weyl is needed)

The function `(g,h) ↦ Tr(gh⁻¹)` **IS** positive-definite on `SU(N) × SU(N)` — it is the
matrix coefficient `⟨(g ⊗ h̄)Ω, Ω⟩` of the unitary representation `π(g,h) = g ⊗ h̄`
(the tensor product of the fundamental representation and its dual).

But `Tr(gh)` requires the "wrong" group action (multiplication instead of multiplication-by-
inverse), which is an **anti-representation**, not a representation. Matrix coefficients of
anti-representations are NOT positive-definite in general.

The character expansion resolves this by decomposing:
```
exp(c · Re Tr(g₁g₂g₃g₄)) = ∑_λ a_λ χ_λ(g₁g₂g₃g₄)
                         = ∑_λ a_λ ∑_{μ,ν,ρ,σ} C_{μνρσ}^λ χ_μ(g₁) χ_ν(g₂) χ_ρ(g₃) χ_σ(g₄)
```
where `a_λ ≥ 0`, `C_{μνρσ}^λ ≥ 0` (Littlewood-Richardson coefficients), and each
`χ_μ(g₁) χ_ν(g₂) χ_ρ(g₃) χ_σ(g₄)` is PD on `SU(N)^4` (product of PD functions on
different factors). The sum of PD functions with non-negative coefficients is PD.

**Progress (2025-06-29)**: The "product of PD on different factors" step has been
formalized as `PositiveDefinite.prod` in `PositiveDefinite.lean` (0 sorries).
This proves that if `φ : G → ℂ` is PD and `ψ : H → ℂ` is PD, then
`(g,h) ↦ φ(g)·ψ(h)` is PD on `G × H`. The proof uses the Schur product theorem
combined with a grouping argument (`PositiveDefinite.sum_nonneg_of_map`) that
handles non-injective index maps.

Additionally, `repCharacter_positiveDefinite` has been proven (0 sorries): the
character `χ(g) = Tr(ρ(g))` of any unitary representation `ρ: G →* U(n)` is
positive-definite. This generalizes `fundamentalCharacter_positiveDefinite` from
the fundamental representation of `SU(N)` to arbitrary unitary representations.
The proof uses the same technique: the PD sum equals `Tr(Bᴴ * B) ≥ 0` where
`B = ∑ conj(c_g) • ρ(g)`, using `ρ(g)ᴴ = ρ(g⁻¹)` (unitary + homomorphism).

The remaining ingredients (Peter-Weyl theorem and Clebsch-Gordan decomposition)
are still not available in Mathlib.

**This decomposition requires the Peter-Weyl theorem, which is not in Mathlib.**

### Conclusion

The sorry in `gibbsExpectationPeriodic_reflection_positive` (ReflectionPositivity.lean:1437)
**cannot be closed** without one of:
- **Peter-Weyl theorem** for SU(N) (character expansion with non-negative coefficients)
- **Heat kernel** on SU(N) (representing `exp(c · Re Tr(g))` as Fourier transform of a
  positive measure on the Lie algebra)
- **Clebsch-Gordan decomposition** for SU(N) (decomposing characters of products)

All of these require representation theory of compact Lie groups that goes beyond what
Mathlib currently provides. The `PositiveDefinite.lean` infrastructure (PD functions, Schur
product theorem, `exp_reTrace_positiveDefinite`) is necessary but **not sufficient** — the
missing ingredient is the decomposition of `exp(c · Re Tr(g₁...gₖ))` into a sum of products
of PD functions on individual factors.
