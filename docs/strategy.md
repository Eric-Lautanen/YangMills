# Strategy Selection: Yang-Mills Mass Gap Formalization

## Decision

**Primary approach**: Stochastic quantization via regularity structures (Chandra-Chevyrev-Hairer-Shen framework), supplemented by constructive QFT methods (cluster expansions, Balaban RG).

**Secondary approach**: Orbit space geometric analysis (Mondal-Douglas-Henry) as a complementary angle.

**Formalization target**: Lean 4 with Mathlib4.

---

## Rationale

### Why Stochastic Quantization?

1. **Most active and advancing program**: Hairer-Chandra-Shen have produced rigorous constructions in 2D (2022) and 3D YM-Higgs (2023). The program is actively pushing toward 3D pure YM and 4D.

2. **Unified framework**: Regularity structures provide a systematic way to handle singular SPDEs. Once the infrastructure is built, it can be applied at multiple dimensions.

3. **Natural for formalization**: The theory of regularity structures is algebraic (Hopf algebras of trees, renormalization as cohomology), which maps well to Lean's type theory.

4. **Connections to probability**: The probabilistic formulation gives access to tools like Gaussian analysis, stochastic calculus — many of which have existing formalization in Lean (measure theory, probability).

### Why Keep Balaban's RG as Backup?

1. **Most complete existing framework**: Balaban's construction of 4D YM-Higgs is a major rigorous achievement. The RG framework is systematic even if technically demanding.

2. **Lattice methods are combinatorial**: Lattice gauge theory (Wilson action, plaquette variables, gauge fixing) is algebraic and may be more amenable to formalization than continuum methods.

3. **Established results in 3D**: Balaban's construction of 3D YM could be formalized as a milestone.

### Why Orbit Space Methods as Secondary?

1. **Geometric/topological approach**: Connects to the well-developed theory of principal bundles, connections, and gauge transformations — already partially available in Mathlib4.

2. **Potential bypass of UV difficulties**: By working on the orbit space (connections modulo gauge), some UV issues may be more tractable.

3. **Early stage**: If the approach matures, it could be integrated.

---

## Formalization Roadmap

### Phase 3: Formal Problem Definition (Lean 4)

**Milestones in order of implementation:**

1. **Topological groups and Lie groups** — SU(N) as a Lie group, compactness, structure constants
   - Dependencies: Mathlib4 already has Lie groups, matrix groups
   
2. **Principal bundles and connections** — Gauge fields as connections on principal bundles
   - Dependencies: Mathlib4 has bundles, manifolds. Connections not yet formalized.

3. **Yang-Mills action** — Functional S(A) = ∫ Tr(F ∧ *F)
   - Need: Differential forms, Hodge star, integration on manifolds

4. **Lattice gauge theory** — Wilson action, plaquette variables, continuum limit
   - Need: Lattice discretization, gauge invariant observables

5. **Wightman axioms** — Hilbert space, vacuum vector, field operators, Poincaré covariance, spectral condition, locality
   - Need: Representation theory of Poincaré group, spectral theory

6. **Osterwalder-Schrader axioms** — Euclidean version, reflection positivity
   - Need: Euclidean Green's functions, analytic continuation

7. **Mass gap condition** — Exponential decay of truncated correlations. Gap in mass spectrum.
   - Need: Spectral theory, correlation functions

### Phase 4: Theorem Decomposition

Break the mass gap theorem into:

1. **YM01**: Existence of YM measure on ℝ⁴ (or lattice → continuum limit)
2. **YM02**: Osterwalder-Schrader positivity of the measure
3. **YM03**: OS axioms → Wightman axioms (reconstruction theorem)
4. **YM04**: Exponential decay of correlations → mass gap
5. **YM05**: Gauge invariance and observable algebra

### Phase 5: Proof Execution

Approach in stages of increasing dimensionality:
1. 2D YM (known) → formalize existing results
2. 3D YM (largely known) → formalize Balaban or Hairer-Chandra results
3. 4D YM-Higgs (known) → formalize Balaban's construction
4. 4D Pure YM (open) → develop new proof within the framework

### Phase 6: Verification

Full formal proof checked by Lean kernel.

---

## Technical Choices

| Decision | Choice | Rationale |
|----------|--------|-----------|
| Proof assistant | Lean 4 | Largest math library (Mathlib4), fast kernel, active community |
| Gauge group | SU(N) | Standard for YM theory, general N |
| Formulation | Euclidean (OS axioms) → Wightman via Osterwalder-Schrader reconstruction | Euclidean methods are better developed for constructive QFT |
| Lattice vs continuum | Both: lattice for discretization, continuum limit via RG | Lattice is more tractable for formalization initially |
| Regularity structures | Likely needed for continuum SPDE approach | Hairer's theory is the only systematic method for singular SPDEs |
