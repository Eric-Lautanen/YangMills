# Literature Survey: Yang-Mills Existence and Mass Gap

## Overview

The Yang-Mills Millennium Prize problem asks for a rigorous construction of
quantum Yang-Mills theory on ℝ⁴ satisfying the Wightman (or Osterwalder-Schrader)
axioms with a positive mass gap. This survey maps the current state of rigorous
results, active programs, and documented challenges.

---

## 1. Established Rigorous Results

### 1.1 Two-Dimensional Yang-Mills (Solved)
- **2D YM is exactly solvable**: The Migdal-Witten approach gives explicit formulas for Wilson loop expectations.
- **Stochastic quantization**: Chandra-Chevyrev-Hairer-Shen (2022) constructed the 2D Yang-Mills measure via stochastic Langevin dynamic, establishing a Markov process on a space of distributional connections.
  - *Key ref*: "Langevin dynamic for the 2D Yang-Mills measure" (arXiv, 2022)
- **Mass gap in 2D**: YM on ℝ² has no propagating degrees of freedom (topological theory), so mass gap is trivial.

### 1.2 Three-Dimensional Yang-Mills (Largely Solved)
- **Balaban's RG for 3D YM**: First rigorous construction using renormalization group methods on the lattice, taking the continuum limit.
- **Magnen-Seneor-Rivasseau**: Constructive approach using cluster expansions.
- **Chandra-Chevyrev-Hairer-Shen (2023)**: Extended stochastic quantization to Yang-Mills-Higgs in 3D, constructing a state space and Markov process for the stochastic quantisation equation.
  - *Key ref*: "Stochastic quantisation of Yang-Mills-Higgs in 3D" (arXiv, 2023)
- **Mass gap in 3D**: Established — exponential decay of correlations proven.

### 1.3 Four-Dimensional Yang-Mills (Open Problem)
- **Renormalizability**: Proven by 't Hooft, Veltman, and others (awarded Nobel Prize). Pure YM is renormalizable in 4D.
- **Perturbative asymptotic freedom**: Gross, Wilczek, Politzer (Nobel Prize) — the coupling constant decreases at high energies, implying UV completeness perturbatively.
- **No rigorous non-perturbative construction exists** for pure YM in 4D.

---

## 2. Active Research Programs

### 2.1 Balaban's Renormalization Group Program
- **Approach**: Lattice gauge theory + rigorous RG transformations. Block spin renormalization group on lattice YM.
- **Status**: Most developed rigorous framework for non-Abelian gauge theories.
  - ✓ 3D YM constructed
  - ✓ 4D YM-Higgs (with scalar field) constructed — the Higgs mechanism provides a mass scale
  - ✗ 4D pure YM — incomplete. The RG flow for pure YM in 4D hits the "strong coupling problem" in the infrared
- **Key challenge**: Controlling the IR behavior of the RG flow without a Higgs field or mass term.

### 2.2 Stochastic Quantization (Hairer-Chandra-Shen)
- **Approach**: Parisi-Wu stochastic quantization — study YM via an SPDE (Yang-Mills heat equation with noise). Use Hairer's regularity structures to handle the singular SPDE.
- **Status**:
  - ✓ 2D YM constructed via Langevin dynamic (Chandra-Chevyrev-Hairer-Shen, 2022)
  - ✓ 3D YM-Higgs constructed (Chandra-Chevyrev-Hairer-Shen, 2023)
  - ✗ 3D pure YM and 4D pure YM — open. The SPDE becomes more singular, requiring higher-order regularity structures.
- **Strengths**: Elegant probabilistic framework. Bypasses lattice discretization. Direct connection to Euclidean QFT.
- **Key challenge**: The YM SPDE in 4D has worse UV behavior. Need to handle non-linearities at higher regularity.

### 2.3 Probabilistic / Large-N (Chatterjee)
- **Approach**: Study lattice YM on finite graphs using probabilistic methods. Large-N limit where the theory simplifies (planar diagrams dominate).
- **Key result**: Chatterjee (2019+) proved that in the large-N limit, lattice YM converges to the "master field" describing a deterministic large-N theory.
- **Status**: Significant progress on large-N lattice YM, but the continuum limit and mass gap in 4D at finite N remain open.

### 2.4 Geometric Analysis (Douglas-Henry, Mondal)
- **Approach**: Study YM functional on the space of connections modulo gauge (orbit space). Equip orbit space with a natural Riemannian metric.
- **Mondal (2023)**: "A Geometric Approach to the Yang-Mills Mass Gap" — proposes using orbit space geometry to obtain a positive mass gap.
- **Status**: Early stage. Interesting geometric insights but no full construction yet.

### 2.5 Constructive QFT via Cluster Expansions (Magnen-Rivasseau-Seiler)
- **Approach**: Traditional Euclidean constructive QFT methods — correlation inequalities, cluster expansions, Mayer expansions.
- **Status**: Applied to YM in 3D, some work on 4D YM-Higgs. Pure 4D YM remains open.

---

## 3. Formalization Efforts (Proof Assistants)

### 3.1 QFT in Proof Assistants
- **No existing formalization** of Wightman or OS axioms found in Lean 4 or Coq.
- **Lean-Quantum** (Kasaura et al., 2024): Lean 4 library for quantum information theory (entropies, data processing inequality). Not QFT.
- **Related formalization work**:
  - Coq: Gödels incompleteness theorem (O'Connor), modal logics
  - Lean 4: Ramanujan-Nagell theorem, Nagata's factoriality theorem
  - Isabelle/HOL: Some analysis foundations

### 3.2 Analysis Foundations Available in Mathlib4
- Functional analysis (Hilbert spaces, bounded operators)
- Measure theory and probability
- Differential geometry (manifolds, connections, principal bundles)
- Lie groups and Lie algebras
- **Missing**: QFT-specific structures (Wightman fields, OS axioms, Feynman integrals, renormalization)

---

## 4. Documented Failure Modes

1. **Pure YM in 4D has no mass scale**: Unlike YM-Higgs, pure YM has no intrinsic mass parameter. The mass gap must emerge dynamically from dimensional transmutation (asymptotic freedom generates Λ_QCD). This makes rigorous RG control extremely difficult.

2. **Infrared problem**: Even if UV is controlled (asymptotic freedom), the IR behavior of 4D YM involves strong coupling and confinement, which is non-perturbative.

3. **Gauge redundancy**: All approaches must handle gauge-fixing modulo Gribov copies. The orbit space (connections modulo gauge) has a complicated topology.

4. **Singular SPDE**: In stochastic quantization, the 4D YM SPDE is critical/supercritical for regularity structures — the noise is too rough relative to the nonlinearity.

5. **Osterwalder-Schrader positivity**: Even if a candidate measure is constructed on the lattice, proving reflection positivity and taking the continuum limit while preserving OS axioms is highly non-trivial.

---

## 5. Summary and Implications for Strategy

| Dimension | Status | Assumed Difficulty |
|-----------|--------|-------------------|
| 2D YM | Solved (exactly, Migdal-Witten) | Easy |
| 2D YM (stochastic) | Solved (Chandra-Chevyrev-Hairer-Shen) | Medium |
| 3D YM | Largely solved (Balaban, Magnen-Seneor) | Hard |
| 3D YM (stochastic) | Solved with Higgs (Chandra-Chevyrev-Hairer-Shen) | Hard |
| 4D YM-Higgs | Constructed (Balaban, etc.) | Very Hard |
| **4D Pure YM** | **Open** | **Extremely Hard** |

### Most Promising Approaches (for 4D pure YM)

1. **Stochastic quantization + regularity structures**: The most active modern program. Already succeeded in 2D and 3D (with Higgs). May extend to 4D with higher-order regularity structures and renormalization.

2. **Balaban's RG on the lattice**: Deepest existing rigorous framework. Needs a breakthrough on the IR RG flow for pure YM.

3. **Geometric analysis (orbit space methods)**: Novel angle that may bypass some difficulties. Least developed.

### Recommendation for This Project

Given the extreme difficulty of the pure 4D YM problem, a pragmatic strategy is:
- **Primary**: Formalize the known 2D and 3D results in Lean 4 first, building the mathematical infrastructure (Wightman/OS axioms, gauge theory).
- **Secondary**: Investigate whether the stochastic quantization approach (Hairer-Chandra-Shen) can be advanced toward 4D, starting from their 2D/3D results.
- **Tertiary**: Explore whether orbit space geometric methods (Mondal) can be combined with the constructive QFT framework.
