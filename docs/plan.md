# Yang-Mills Mass Gap: Project Plan

## Overview

The Yang-Mills existence and mass gap problem asks for a rigorous
construction of quantum Yang-Mills theory on ℝ⁴ satisfying the
Wightman (or Osterwalder-Schrader) axioms, with a positive mass gap
— i.e., the lowest excited state above the vacuum has strictly positive
energy.

## Phase 1: Literature Survey

Map all existing rigorous results, active programs, and documented
failure modes. Key areas:

- **2D Yang-Mills**: exactly solvable (Gross, Taylor, Migdal, Witten)
- **3D Yang-Mills**: existence via Balaban's renormalization group
  and Magnen-Seneor-Rivasseau constructive approach
- **4D Yang-Mills**: open problem. Major programs:
  - Balaban's RG approach (lattice continuum limit)
  - Hairer's regularity structures (stochastic quantization)
  - Chatterjee's probabilistic YM on ℝ⁴ (large-N, master field)
  - Douglas-Henry-Unger geometric analysis
  - Lattice gauge theory numerical evidence (Monte Carlo)
- **Mass gap**: established in 2D/3D. Open in 4D.
- **Confinement**: related but distinct problem

## Phase 2: Strategy Selection

Choose primary approach based on survey results. Candidates:

1. **Constructive QFT via Balaban's RG** — most developed rigorous
   framework for non-Abelian gauge theories. Has worked for 3D YM
   and 4D YM-Higgs.
2. **Stochastic quantization + regularity structures** — Hairer's
   approach handles SPDEs far from equilibrium. Applied to YM by
   Hairer-Shen, Chandra-Hairer-Shen.
3. **Probabilistic approach** — Chatterjee's large-N framework,
   master field, lattice YM on arbitrary graphs.
4. **Geometric analysis** — Douglas-Henry approach via gauge theory
   and Yang-Mills flow.

## Phase 3: Formal Problem Definition

Encode in Lean 4:
- Wightman axioms (Hilbert space, vacuum, field operators, Poincaré
  covariance, spectral condition, locality)
- Osterwalder-Schrader axioms (Euclidean version)
- SU(N) Yang-Mills action
- Mass gap condition (exponential decay of truncated correlations)

## Phase 4: Proof Decomposition

Break mass gap theorem into lemmas using explore_theorem.

## Phase 5: Execute Proof

Rigorous construction following chosen strategy.

## Phase 6: Formal Verification

Complete Lean 4 proof checked by the kernel.
