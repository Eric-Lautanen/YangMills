# Project Goals

## The Millennium Prize Problem

The Clay Mathematics Institute Millennium Prize problem for Yang–Mills theory
asks two things:

1. **Existence:** Construct a 4D quantum Yang–Mills theory satisfying the
   Wightman axioms (equivalently, the Osterwalder–Schrader axioms for the
   Euclidean theory), as the continuum limit of a lattice gauge theory.
2. **Mass gap:** Show the theory has a mass gap — the spectrum above the
   vacuum is bounded away from zero by a positive constant `m > 0`.

Both are open mathematical problems. This project is a Lean 4 formalization
effort around the mathematical foundations of this problem.

## Current status (honest)

**The Millennium Prize theorem is NOT proved.** The top-level statement
depends on axioms that encode the open problems:

| Axiom | What it stands in for | Status |
|---|---|---|
| `continuum_limit_exists` | Existence of the 4D pure YM continuum limit | **Genuinely open** — the IR / strong-coupling control is unsolved math |
| `mass_gap_axiom` | Positivity of the continuum mass gap | **The conjecture itself** — circular if used in a "proof" |
| `transferMatrixPositivity_axiom` | Reflection positivity of the lattice transfer matrix | Closeable in principle (Lüscher decomposition in progress); see caveat below |
| `peterWeyl_clebschGordan_plaquette` | Peter–Weyl + Clebsch–Gordan + L² completeness + Schur for Λ | Standard theorems, not in Mathlib; has been strengthened 7× (see audit) |
| `characterOrthogonality` | Great Orthogonality Theorem for matrix elements | Standard theorem, not in Mathlib |
| `os_reconstruction_theorem` | Osterwalder–Schrader reconstruction | Established published math, not in Mathlib |

**Axiom count: 6.** See `docs/axiom_growth_audit.md` and
`docs/honest_frontier_audit.md` for the full audit of whether "6 → 5" would
be honest progress (short answer: partially — three of the seven
strengthenings of `peterWeyl_clebschGordan_plaquette` absorbed substantial
prerequisites comparably hard to the target).

## What IS done (proved, axiom-light)

- **Lattice gauge theory infrastructure** — Wilson action, plaquette product,
  periodic lattice, product Haar measure, gauge transformations. 0 sorries.
- **Reflection-positivity decomposition** — positive/negative/interface
  action split, reflection symmetries, transfer-matrix identity
  `integral_G_thetaG_eq_inner_g_Tg`. 0 sorries, standard axioms only.
- **Positive-definite kernel theory** — Mercer-type PD kernels, group-PD
  functions, integral averages, positive integral operators, Schur product,
  Lüscher cascade integrals, character-kernel non-negativity. 0 sorries,
  axiom-light. Packaged as Mathlib candidates (see `MATHLIB_SUBMISSION.md`).
- **Spatial/temporal plaquette decomposition** and **spatial Boltzmann PD**
  (sub-steps 1–2 of the Lüscher decomposition `T = V^{1/2}·U·V^{1/2}`).

## What is NOT done (and why)

- **`transferMatrixPositivity_axiom`** — the Lüscher decomposition sub-steps
  3–6 (U positive, factorization, `∫g·Tg≥0`, conclude) are in progress.
- **`continuum_limit_exists`** — the IR / strong-coupling control (Balaban
  RG step B5 / stochastic quantization step S3) is genuinely unsolved. Not a
  formalization gap — the frontier of the field.
- **`mass_gap_axiom`** — the conjecture itself. Every route hits an open wall
  (uniform gap, confinement, finite-N, orbit geometry).

See `docs/honest_frontier_audit.md` for the full sub-lemma breakdown of what
each axiom would require to close, classified as "known but unformalized"
vs "genuinely open."

## The honest path forward

Per `docs/honest_frontier_audit.md` Part 5, the most honest path is not
"drive the axiom count down" but:

1. **Package and submit** the genuinely-novel / unformalized infrastructure
   to Mathlib (the Mathlib candidates).
2. **Target known partial results** (2D/3D constructions, strong-coupling
   lattice gap, Källén–Lehmann spectral representation) as real theorems
   clearly distinguished from the open conjecture.
3. **Continue the Lüscher decomposition** to close
   `transferMatrixPositivity_axiom` (count 6 → 5), with the caveat that the
   "6 → 5" headline is partially misleading per the axiom-growth audit.
