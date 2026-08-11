# Honest Frontier Audit: Where This Project Actually Stands

**Date:** 2026-08-11 (session 85)
**Purpose:** An honest, no-softening assessment of (1) whether the axiom
strengthenings have relocated difficulty rather than removed it, (2) what a
genuine attack on `continuum_limit_exists` and `mass_gap_axiom` would require,
and (3) a running list of possibly-novel contributions (cross-referenced to
`docs/mathlib_candidates.md`).

This document is written to be read by a successor session that needs to know
the *actual* state of the project, not the headline.

---

## Part 1: Axiom Growth Audit — Has "6 → 5" Actually Reduced Anything?

### The question

`peterWeyl_clebschGordan_plaquette` has been strengthened seven times. Four of
those strengthenings immediately followed a session that hit a wall. The
existing audit (`docs/axiom_growth_audit.md`) flagged this pattern. This
section goes further: for *each* strengthening, it asks (a) original vs.
strengthened statement, (b) is the strengthened version a standard,
independently-known result or something introduced to unstick a proof, and (c)
is it logically close to / equivalent to what `transferMatrixPositivity_axiom`
was supposed to establish?

### Strengthening #1 — Char-level Clebsch–Gordan (2026-07-03)

**Original:** Peter–Weyl character expansion of the plaquette Boltzmann factor
`exp(c·Re Tr(g₁g₂g₃g₄)) = Σ coeff·χ_s(g₁)χ_t(g₂)χ_u(g₃)χ_v(g₄)` with
`coeff ≥ 0`.

**Strengthened:** Added the Clebsch–Gordan decomposition for products of
characters of the *same* group element: `χ_s(g)·χ_t(g) = Σ_w cg(s,t,w)·χ_w(g)`
with `cg(s,t,w) ≥ 0` (Littlewood–Richardson multiplicities).

**Standard or introduced?** **Standard.** This is the Clebsch–Gordan
decomposition for `SU(N)` — a major theorem (Fulton & Harris Ch. 13), and the
non-negativity of LR multiplicities is a known result. It is *not* something
introduced to unstick this proof; it is a real theorem that any
representation-theory formalization would need.

**Equivalent to the target axiom?** **No.** The target axiom
(`transferMatrixPositivity_axiom`) is a *positivity of an integral* statement.
CG decomposition is a *structural* statement about how character products
decompose. They live at different levels: CG is an input to the positivity
argument, not the positivity itself. You can have CG without reflection
positivity, and (in principle) reflection positivity without CG (via a
different mechanism).

**Verdict:** Legitimate strengthening — it adds a real, standard theorem that
was genuinely missing. The *timing* (added the session after a wall) is
suspicious, but the *content* is not equivalent to the target. This one does
not collapse "6 → 5."

### Strengthening #2 — Contragredient dual map (2026-07-30)

**Original:** (after #1) char-level CG present.

**Strengthened:** Added `dual : ι → ι` with
`χ_{dual(i)}(g) = conj(χ_i(g))` — the contragredient representation has
conjugate character.

**Standard or introduced?** **Standard, narrow.** One-line consequence of
unitarity: `ρ(g⁻¹) = ρ(g)*`, so `Tr(ρ(g⁻¹)) = conj(Tr(ρ(g)))`. Citable in one
line of any rep-theory textbook.

**Equivalent to the target?** **No.** This is a wiring ingredient (handles
inverted links in the plaquette product), not a positivity statement.

**Verdict:** Legitimate, narrow. Does not collapse "6 → 5."

### Strengthening #3 — hIrr / hDims hypotheses (2026-08-01)

**Strengthened:** Added `hIrr : ∀ i, IsIrreducible (ρ i)` and
`hDims : ∀ i, 0 < dims i`.

**Standard or introduced?** **Standard, narrow.** Definitional bookkeeping —
irreps are irreducible and have positive dimension by definition; these just
assert the chosen data has the expected properties. Needed to apply Schur
orthogonality.

**Equivalent to the target?** **No.** Pure bookkeeping.

**Verdict:** Legitimate, narrow. Does not collapse "6 → 5."

### Strengthening #4 — L² completeness / Peter–Weyl completeness (2026-08-02) ⚠️

**Original:** (after #3) finite `ι` of irreps with char expansion + CG + dual.

**Strengthened:** Added a *countable* index set `Λ` of *all* irreducible
unitary representations of `SU(N)`, an embedding `ι ↪ Λ`, the normalized Haar
measure `μ`, and the **L² completeness** (Peter–Weyl completeness theorem):
if `f ∈ L¹(G, μ)` and all Fourier coefficients `∫ f·conj((ρ_ℓ g)_{ij}) dμ = 0`
vanish, then `f = 0` a.e.

**Standard or introduced?** **Standard, but substantial.** This is the
Peter–Weyl *completeness* theorem — the culmination of the Peter–Weyl theorem
(matrix elements form an orthonormal *basis*, not just an orthogonal family,
of `L²(G, μ)`). Own chapter in harmonic-analysis textbooks (Folland Ch. 5,
Deitmar Ch. 7). It is a real theorem, not invented here.

**Equivalent to the target?** **This is the critical case.** The target axiom
asserts `∫ f(U)·f(θU)·exp(-β S_W) dμ ≥ 0`. The §8.11.55–56 analysis found that
closing this requires expanding an *arbitrary* function `A_w` (a Fourier
coefficient depending on the arbitrary test function `f`) in the full Peter–Weyl
basis `Λ` — which requires L² completeness. So L² completeness is a *prerequisite
ingredient* for the target, not the target itself. But: **it is a prerequisite
that is at least as hard to prove as the target is to use.** The target axiom
is a single positivity statement; L² completeness is a major theorem. By
absorbing L² completeness into `peterWeyl_clebschGordan_plaquette`, we have
*replaced* "assume the integral is non-negative" with "assume a major theorem
of harmonic analysis." The assumption burden has not decreased; it has
*increased* in substance even as the count stayed flat.

**Verdict:** ⚠️ **This strengthening partially collapses "6 → 5."** L²
completeness is not *logically equivalent* to the target (you can have
completeness without reflection positivity), but it is a *prerequisite that
is comparably hard*. If we count this axiom's content honestly, closing the
target does not reduce the project's assumption burden — it swaps one
hard-to-justify statement for a different, equally-hard-to-justify (but
standard) theorem. The "6 → 5" headline is misleading *for this
strengthening specifically*.

### Strengthening #5 — Matrix-element CG coefficients (2026-08-02 s3) ⚠️

**Strengthened:** Added `cgME : ∀ (s t ν : ι), Fin(dims s) → Fin(dims t) →
Fin(dims ν) → ℂ` — the unitary change-of-basis matrices implementing
`ρ_s ⊗ ρ_t → ⊕_ν ρ_ν` at the matrix-element level, with the decomposition
relation and unitarity (completeness) relation.

**Standard or introduced?** **Standard, substantial.** The unitary CG
decomposition at the matrix-element level is a major structural result
(strictly more detailed than char-level CG). Comparable in substance to Schur
orthogonality. Not invented here — it is the explicit CG coefficient machinery
from representation theory.

**Equivalent to the target?** **No, but same issue as #4.** It is a
prerequisite ingredient for evaluating the triple-product integrals that arise
in the reflection-positivity reorganization. Not equivalent to the positivity
statement, but a comparably-hard prerequisite that was added specifically
because the target could not be closed without it.

**Verdict:** ⚠️ **Same partial collapse as #4.** Not logically equivalent to
the target, but a substantial prerequisite absorbed to route around a wall.

### Strengthening #6 — Character measurability hMeas (2026-08-03)

**Strengthened:** Added `hMeas : ∀ i, Measurable (repCharacter (ρ i))`.

**Standard or introduced?** **Standard, narrow.** Characters of continuous
representations are continuous (trace of a continuous matrix-valued function),
hence measurable. One-line consequence of continuity.

**Equivalent to the target?** **No.** Wiring ingredient for integrability
discharge.

**Verdict:** Legitimate, narrow. Does not collapse "6 → 5."

### Strengthening #7 — Schur for Λ + CG for ι×Λ (2026-08-09 s70) ⚠️

**Strengthened:** Added (Part 3) Schur orthogonality for the *countable* set
`Λ` (the Great Orthogonality Theorem for all irreps, extending
`characterOrthogonality` which covers only finite `ι`), and (Part 4) the CG
decomposition for the mixed finite×countable pair `ι × Λ` with finite `Finset`
support and unitarity.

**Standard or introduced?** **Standard, substantial — both parts.** Part 3 is
the Great Orthogonality Theorem for all irreps of a compact group (own chapter
in Folland / Deitmar). Part 4 is the CG decomposition at the matrix-element
level for a mixed finite×countable pair — strictly more general than #5. Both
are real theorems, not invented here.

**Equivalent to the target?** **Same issue as #4, #5.** These are
prerequisites for the infinite Peter–Weyl expansion needed to handle the
arbitrary test function `f`. Not logically equivalent to the positivity
statement, but comparably-hard prerequisites added specifically to route around
the "fundamental mismatch" wall of §8.11.55–56.

**Verdict:** ⚠️ **Same partial collapse as #4, #5.**

### Overall verdict on "6 → 5"

**Is "6 → 5" still true after this audit?** **In count, yes. In substance, no
— for three of the seven strengthenings.**

- Strengthenings #1, #2, #3, #6 are legitimate: they add real (standard or
  narrow) ingredients that are *not* equivalent to the target. Closing the
  target with only these absorbed would be honest progress.
- Strengthenings **#4, #5, #7** are the problem. Each adds a *substantial,
  standard theorem* (L² completeness, matrix-element CG, Schur for Λ + CG for
  ι×Λ) that is a *prerequisite* for the target — added specifically because
  the target could not be closed without it. These are not logically equivalent
  to `transferMatrixPositivity_axiom`, but they are *comparably hard
  prerequisites*. Absorbing them means: "we replaced 'assume the integral is
  non-negative' with 'assume three major theorems of harmonic analysis that
  are collectively at least as hard to prove as the positivity statement
  itself.'"

**The honest statement is:** if `transferMatrixPositivity_axiom` is closed,
the *named* axiom count goes 6 → 5, but the *assumption burden* (measured by
"how much nontrivial math are we taking on faith") does not decrease — it
relocates from one axiom to the enriched `peterWeyl_clebschGordan_plaquette`.
A *genuine* reduction would require *proving* one of #4, #5, or #7 from more
primitive axioms (e.g., proving L² completeness from Haar measure +
irreducibility + Schur's lemma), not merely absorbing it.

**This does NOT mean the work is worthless.** The cascade lemmas, the
character-kernel non-negativity, and the spatial/temporal decomposition are
real, proved, axiom-light results (see `docs/mathlib_candidates.md`). It means
the *headline metric* (axiom count) is not measuring what it claims to
measure.

---

## Part 2: What It Would Take to Attack `continuum_limit_exists`

### The axiom

```lean
axiom continuum_limit_exists (a : ℝ) (ha : 0 < a) :
  ∃ S_cont : ∀ n, Temperedness n,
    (∀ n, EuclideanCovariance n (S_cont n)) ∧
    (∀ n, Symmetry n (S_cont n)) ∧
    ReflectionPositivity S_cont ∧
    Ergodicity S_cont
```

This asserts: as the lattice spacing `a → 0`, the lattice Schwinger functions
converge to continuum Schwinger functions satisfying the OS axioms
(Euclidean covariance, symmetry, reflection positivity, ergodicity). This is
the **existence** half of the Millennium Prize problem.

### The actual mathematical content

The axiom stands in for the **construction of the continuum limit of 4D pure
Yang-Mills theory**. There are two serious mathematical programs that have
attempted this, neither complete for 4D pure YM:

1. **Balaban's renormalization group** (lattice → continuum via rigorous RG).
2. **Stochastic quantization** (Hairer–Chandra–Chevyrev–Shen, via SPDE /
   regularity structures).

Per `literature/survey.md`: 3D YM is largely solved (Balaban); 4D YM-Higgs is
constructed (the Higgs provides a mass scale); **4D pure YM is open** — the RG
flow hits the "strong coupling problem" in the infrared, and there is no known
mass scale to control the flow.

### Sub-lemma breakdown (Balaban RG route — the most developed)

A genuine formalization of the Balaban-style continuum limit would need, at
minimum, the following chain. I classify each as **[OPEN]** (genuinely unsolved
math), **[KNOWN-UNFORMALIZED]** (established in the literature but not in
Lean/Mathlib), or **[FORMALIZED-HERE]** (already done in this project).

**B1. Lattice definition and Wilson action.** [FORMALIZED-HERE]
`wilsonActionFinite`, `plaquetteProduct`, the periodic lattice, product Haar
measure. Done, 0 sorries.

**B2. Reflection positivity of the lattice measure.** [PARTIALLY
FORMALIZED-HERE] `lattice_ym_reflection_positive_periodic` is proved but rests
on `transferMatrixPositivity_axiom`. Closing that axiom (the current Lüscher
work) would make this fully formalized. This is the *prerequisite* for the
continuum limit — you cannot take a limit of a measure that is not RP and
expect RP to survive.

**B3. RG block-spin transformation.** [KNOWN-UNFORMALIZED, partially OPEN]
Define the blocking map (coarse-graining: average link variables over blocks),
show it maps the lattice measure to a blocked measure, and derive the RG
recursion for the effective action. The *definition* of the blocking map is
known; the *control of the RG flow* (showing the blocked action stays in a
manageable class) is the hard part. For 4D pure YM, **the IR flow is not
controlled** — this is the core open problem. Classification: the *setup* is
[KNOWN-UNFORMALIZED]; the *IR control* is **[OPEN]**.

**B4. Ultraviolet (short-distance) control.** [KNOWN-UNFORMALIZED]
Asymptotic freedom (Gross–Wilczek–Politzer, Nobel Prize) says the coupling
→ 0 at high energies. This makes the UV *perturbatively* controllable. The
perturbative renormalizability of 4D YM is proven ('t Hooft, Veltman). This is
established mathematics, not in Mathlib. Classification: [KNOWN-UNFORMALIZED].

**B5. Infrared (long-distance) control — THE OPEN CORE.** [OPEN]
This is where every existing program stops. For 4D pure YM, there is no mass
scale (unlike YM-Higgs), so the IR RG flow enters a strong-coupling regime
where perturbation theory fails. No one has controlled this. Balaban's program
handles 3D and 4D-Higgs but **not 4D pure**. This is not "unformalized known
math" — it is **genuinely unsolved**. Any formalization that claims to close
`continuum_limit_exists` for 4D pure YM would be claiming to solve an open
problem.

**B6. Convergence of Schwinger functions as a → 0.** [OPEN, conditional on B5]
Even if the RG flow were controlled, proving that the lattice Schwinger
functions (correlation functions of gauge-invariant observables) converge to
continuum limits requires uniform bounds in `a`. This is a compactness /
tightness argument. The *framework* is standard (Prokhorov tightness), but the
*uniform bounds* depend on B5. Classification: the measure-theory machinery
is [KNOWN-UNFORMALIZED]; the bounds are [OPEN, conditional on B5].

**B7. OS axioms for the continuum limit.** [KNOWN-UNFORMALIZED, conditional]
Given convergence (B6), the continuum Schwinger functions inherit OS axioms
from the lattice (B2) by taking limits. Euclidean covariance, symmetry,
reflection positivity, ergodicity each pass to the limit under suitable
continuity. This is a standard "axioms are closed under limits" argument. The
*argument* is known; the *formalization* is not. Classification:
[KNOWN-UNFORMALIZED, conditional on B6].

### Sub-lemma breakdown (stochastic quantization route)

**S1. The Yang-Mills Langevin SPDE.** [KNOWN-UNFORMALIZED]
The Parisi-Wu stochastic quantization: YM measure = invariant measure of a
Langevin dynamics. The SPDE is the Yang-Mills heat equation with noise.
Definition is known; formalization would need SPDE infrastructure (regularity
structures / paracontrolled calculus). Classification: [KNOWN-UNFORMALIZED].

**S2. 2D and 3D constructions (done in the literature).** [KNOWN-UNFORMALIZED]
Chandra-Chevyrev-Hairer-Shen constructed 2D YM (2022) and 3D YM-Higgs (2023)
via stochastic quantization. These are *published, peer-reviewed results* that
are not in Lean. Classification: [KNOWN-UNFORMALIZED] — these are the natural
*first targets* for a stochastic-quantization formalization.

**S3. 4D pure YM SPDE — well-posedness.** [OPEN]
The 4D YM SPDE is critical/supercritical for regularity structures. No
well-posedness result exists. Classification: **[OPEN]** — this is the
stochastic-quantization version of the B5 wall.

### Honest assessment for `continuum_limit_exists`

| Sub-lemma | Status | Open or unformalized? |
|-----------|--------|-----------------------|
| B1 Lattice + action | Formalized here | Done |
| B2 Lattice RP | Partially here (needs axiom closure) | Unformalized (closeable) |
| B3 RG blocking setup | Known | Unformalized |
| B3' RG IR flow control | **Not known** | **OPEN** |
| B4 UV control (asymptotic freedom) | Known (Nobel) | Unformalized |
| B5 IR control (pure 4D) | **Not known** | **OPEN — the core** |
| B6 Convergence of Schwinger functions | Conditional on B5 | Open (conditional) |
| B7 OS axioms pass to limit | Known framework | Unformalized (conditional) |
| S1–S2 SPDE / 2D-3D | Known | Unformalized |
| S3 4D SPDE well-posedness | **Not known** | **OPEN** |

**Bottom line:** `continuum_limit_exists` for 4D pure YM is **not a
formalization problem — it is an open mathematical problem.** The sub-lemmas
split into "known but unformalized" (B1, B2, B3-setup, B4, B7, S1, S2) and
"genuinely open" (B3'-IR, B5, B6-conditional, S3). The open parts (B5 / S3)
are the **strong-coupling / infrared problem** — the thing nobody has solved.
A formalization cannot close this axiom without solving the open problem.

**What IS attackable from here:** the *known-unformalized* sub-lemmas. The most
tractable next formalization target is **S2 (2D YM stochastic construction)** —
it is a published, peer-reviewed result (Chandra-Chevyrev-Hairer-Shen 2022)
that is fully rigorous in the literature and would build the SPDE / regularity
structure infrastructure. This is honest, bounded work that does not claim to
solve the open problem. It would also let us honestly state "2D YM continuum
limit: formalized" as a real result, distinct from the 4D conjecture.

---

## Part 3: What It Would Take to Attack `mass_gap_axiom`

### The axiom

```lean
axiom mass_gap_axiom (a : ℝ) (ha : 0 < a) : YangMillsMassGap
```

`YangMillsMassGap` (in `MassGap.lean`) encodes the mass gap as: the
energy-momentum spectrum has a positive gap above the vacuum, equivalently
truncated correlation functions decay exponentially
`|⟨Ω, φ(x)φ(y)Ω⟩_T| ≤ C·e^{-m|x-y|}` with `m > 0`. These are equivalent by
the Källén-Lehmann spectral representation.

**This axiom IS the conjecture.** `yang_mills_mass_gap` pulls the gap directly
from it. Any theorem chain terminating here is circular. The README says this
explicitly and it must not be softened.

### The actual mathematical content

The mass gap for 4D pure YM is the **second half** of the Millennium Prize
problem. It is *harder* than the existence half in the sense that even the
*physics* is not fully understood: confinement (the mechanism believed to
produce the gap) is a non-perturbative phenomenon with no rigorous proof.

There are several routes people have tried. I break each into sub-lemmas.

### Route M1: Lattice mass gap + uniform bounds (the "constructive" route)

**M1a. Lattice mass gap (spectral gap of the lattice transfer matrix).**
[PARTIALLY ATTACKABLE]
The transfer matrix `T` (which this project formalizes as
`transferMatrixCorrect`) has a spectral gap if its spectrum above the ground
state is bounded away from zero. On the lattice, for large `β` (strong
coupling / coarse lattice), the gap can be shown by cluster expansion. This is
**known for strong coupling** (Osterwalder-Seiler, Seiler's book
*Gauge Theories as a Problem of Constructive QFT*, 1982). Classification:
[KNOWN-UNFORMALIZED] for the strong-coupling regime.

**M1b. Uniformity of the gap in the lattice spacing.** [OPEN]
The lattice gap from M1a depends on `a` (and `β`). To take the continuum
limit, the gap must be **uniform in `a`** as `a → 0`. This is where the
strong-coupling expansion breaks down: as `a → 0`, `β → ∞` (asymptotic
freedom), and the strong-coupling expansion (valid at small `β`) no longer
applies. **No one has uniform bounds on the mass gap across the continuum
limit.** Classification: **[OPEN — the core]**. This is the mass-gap analog of
the B5 IR-control wall.

**M1c. Gap survives the continuum limit.** [OPEN, conditional on M1b + B6]
If the lattice gap is uniform (M1b) and the continuum limit exists (B6), the
gap passes to the continuum by spectral convergence. Classification:
[KNOWN-FRAMEWORK, conditional] — the *argument* is standard spectral theory,
but it depends on the two open ingredients.

### Route M2: Spectral / operator-theoretic (the "Wightman" route)

**M2a. Spectral representation (Källén-Lehmann).** [KNOWN-UNFORMALIZED]
The two-point function is the Laplace transform of a positive spectral
measure; a spectral gap `m > 0` ⟺ exponential decay with rate `m`. This is
standard axiomatic QFT (Streater-Wightman, Jost). Classification:
[KNOWN-UNFORMALIZED] — a clean, bounded formalization target.

**M2b. Positivity of the spectral gap.** [OPEN]
Even given the spectral representation, proving the gap is *positive* (not
zero) requires showing the theory is *not* massless — i.e., there are no
massless excitations. For pure YM, this is confinement. **No rigorous proof.**
Classification: **[OPEN]**.

### Route M3: Large-N / probabilistic (Chatterjee)

**M3a. Large-N limit convergence.** [KNOWN-UNFORMALIZED]
Chatterjee (2019+) proved that lattice YM at large `N` converges to the
"master field" (deterministic large-N theory). This is a published result.
Classification: [KNOWN-UNFORMALIZED].

**M3b. Mass gap at finite N from large-N.** [OPEN]
The large-N limit has a gap (in some formulations), but **extending to finite
`N`** (the physical case) is open. The `1/N` expansion is not controlled.
Classification: **[OPEN]**.

### Route M4: Geometric / orbit-space (Mondal 2023)

**M4a. Orbit-space Riemannian structure.** [KNOWN-UNFORMALIZED, early stage]
Mondal proposes equipping the gauge-orbit space with a natural metric and
deriving the gap from the geometry. This is a *proposal*, not a complete
construction. Classification: [KNOWN-UNFORMALIZED] but **early-stage / not
fully rigorous in the literature**.

**M4b. Positive gap from orbit-space geometry.** [OPEN]
The derivation of a positive gap from the orbit-space geometry is not
complete. Classification: **[OPEN]**.

### Honest assessment for `mass_gap_axiom`

| Sub-lemma | Status | Open or unformalized? |
|-----------|--------|-----------------------|
| M1a Lattice gap (strong coupling) | Known (Seiler) | Unformalized |
| M1b Uniform gap in `a` | **Not known** | **OPEN — the core** |
| M1c Gap survives limit | Framework known | Open (conditional) |
| M2a Källén-Lehmann | Known | Unformalized |
| M2b Gap is positive (confinement) | **Not known** | **OPEN** |
| M3a Large-N convergence | Known (Chatterjee) | Unformalized |
| M3b Finite-N gap from large-N | **Not known** | **OPEN** |
| M4a Orbit-space structure | Early-stage proposal | Unformalized (not fully rigorous) |
| M4b Gap from orbit geometry | **Not known** | **OPEN** |

**Bottom line:** `mass_gap_axiom` is **the conjecture itself**, and the
conjecture is **open**. Every route hits a wall: M1b (uniform gap), M2b
(confinement / positivity), M3b (finite-N), M4b (orbit geometry). None of
these is "unformalized known math" — they are **genuinely unsolved**. A
formalization cannot close this axiom without solving the open problem.

**What IS attackable from here:** the *known-unformalized* sub-lemmas that do
not claim the gap is positive. The most honest targets are:
- **M1a (lattice mass gap at strong coupling)** — Seiler's result is rigorous
  and bounded. Formalizing it would give "lattice YM has a gap at strong
  coupling" as a real theorem, clearly labeled as *not* the continuum gap.
- **M2a (Källén-Lehmann spectral representation)** — standard axiomatic QFT,
  clean formalization target, builds the spectral-theory infrastructure.
- **M3a (large-N convergence)** — Chatterjee's result is published and
  rigorous; formalizing it is bounded work.

These would be *real theorems* about *partial results*, honestly distinguished
from the open conjecture. They would not close `mass_gap_axiom` but would
constitute genuine formalization of known mathematics.

---

## Part 4: Possibly-Novel Contributions (cross-reference)

See `docs/mathlib_candidates.md` for the full running list. Summary:

1. **Mercer-type `PositiveDefiniteKernel`** (priority, possibly-novel
   formulation) — packaged, axiom-light.
2. **Group-PD `PositiveDefinite` + integral** (standard, unformalized) —
   packaged.
3. **Lüscher cascade integrals** (standard, unformalized) — embedded, ready
   to package (needs Schur orthogonality).
4. **Character-kernel integral non-negativity** (standard, unformalized) —
   embedded, strong candidate (few deps).
5. **`addVectorPeriodic` whnf workaround** (technique) — documented.
6. **Schur orthogonality / GOT** (standard, currently an AXIOM) — high-impact
   *target*, not proved here.
7. **§8.11.67 RP obstruction clarification** (expository) — write-up
   candidate.

**Honest bottom line on novel contributions:** the genuinely *novel*
contribution (in formulation, not depth) is #1 (Mercer-type kernels). Items
#2–#4 are standard mathematics Mathlib happens to lack — valuable
infrastructure, not new theorems. #6 is the highest-impact *target* but is not
something this project has proved. None of these constitute progress on the
Millennium Prize problem; they are reusable infrastructure that fell out of
the attempt.

---

## Part 5: Overall Honest Verdict — Where This Project Truly Stands

### What is genuinely done (real, proved, axiom-light)

- The **lattice setup** (Wilson action, plaquette product, periodic lattice,
  product Haar measure, gauge transformations) is fully formalized, 0 sorries.
- The **OS decomposition** (positive/negative/interface action split,
  reflection symmetries) is proved.
- The **transfer-matrix identity** `integral_G_thetaG_eq_inner_g_Tg` is proved
  (0 sorries, standard axioms only) — this is the measure-theoretic reduction
  of the reflection integral to `⟨g, Tg⟩`.
- The **abstract PD infrastructure** (group-PD, Mercer-PD, integral averages,
  integral operators, Schur product, Lüscher cascades, character-kernel
  non-negativity) is proved, 0 sorries, axiom-light. This is the
  mathlib-candidate material.
- The **spatial/temporal plaquette decomposition** and **spatial Boltzmann PD**
  (sub-steps 1–2 of the Lüscher decomposition) are proved this session-series.

### What is NOT done (and why)

- **`transferMatrixPositivity_axiom` is still an axiom.** The Lüscher
  decomposition (sub-steps 3–6) is in progress. Even if it closes, per Part 1,
  the "6 → 5" headline is misleading because `peterWeyl_clebschGordan_plaquette`
  has absorbed ~3 substantial prerequisites comparably hard to the target.
- **`continuum_limit_exists` is an open mathematical problem** (Part 2). The
  IR / strong-coupling control (B5 / S3) is genuinely unsolved. This is not
  a formalization gap — it is the frontier of the field.
- **`mass_gap_axiom` is the conjecture itself** (Part 3). Every route hits an
  open wall (M1b / M2b / M3b / M4b). Not closeable without solving open math.

### The honest one-paragraph status

This project has formalized a substantial layer of **lattice gauge theory
infrastructure** and **positive-definite-kernel / Lüscher-cascade analysis**
that is genuinely useful and largely absent from Mathlib. It has *not* proved
the Yang-Mills existence or mass gap, and it cannot — both rest on axioms that
encode open mathematical problems (the continuum limit and the mass gap), and
one of the remaining "closeable" axioms (`transferMatrixPositivity_axiom`) has,
on honest audit, had its difficulty relocated into an enriched
`peterWeyl_clebschGordan_plaquette` axiom rather than removed. The most
honest path forward is not "drive the axiom count down" but **(a)** package and
submit the genuinely-novel / unformalized infrastructure to Mathlib (the
mathlib candidates), and **(b)** target *known* partial results (2D/3D
constructions, strong-coupling lattice gap, Källén-Lehmann) as real theorems
clearly distinguished from the open conjecture — rather than continuing to
absorb open-problem content into axioms while holding the count flat.
