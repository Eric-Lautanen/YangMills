# Axiom Growth Audit: Has `peterWeyl_clebschGordan_plaquette` Absorbed the Hard Part?

**Date of audit:** 2026-08-03 (final session; §6 dated 2026-08-03)
**Trigger:** A self-audit requested before any further wiring on step (c)/(d) of the
`transferMatrixPositivity_axiom` closure plan.
**Question:** Has the axiom `peterWeyl_clebschGordan_plaquette` quietly grown to swallow
the hard part of closing `transferMatrixPositivity_axiom`, while the headline "axiom
count stays at 6" framing hides that growth?

**Short answer: yes.** The axiom has been strengthened **six** times. At least **three**
of those strengthenings directly followed a session concluding that the target axiom
could *not* be closed with the current axioms. Unfolded into separately-named axioms,
`peterWeyl_clebschGordan_plaquette` would be **seven** axioms, **four** of them substantial
theorems, and **two** of them (L² completeness, matrix-element CG) individually as
substantial as `characterOrthogonality` already is. The "count 6 → 5" framing is therefore
misleading unless stated alongside this growth.

---

## 1. Chronological list of strengthenings

The chronology below is reconstructed from the project task log, `README.md`,
`docs/gap_analysis.md`, `docs/transfer_matrix_positivity_design.md`, and
`src/lean/YangMills/Overview.lean`. Session dates are the documented session
dates (the git history is a batched subset and does not capture every session).

### Original axiom (pre-2026-07-03)

**Content:** A finite index set `ι` of irreducible unitary representations of `SU(N)`,
with non-negative coefficients `coeff`, asserting the **character expansion of the
plaquette Boltzmann factor** `exp(c·Re Tr(g₁g₂g₃g₄)) = ∑ coeff · χ_s(g₁)χ_t(g₂)χ_u(g₃)χ_v(g₄)`.

**Classification:** (b) substantial — this is the Peter–Weyl theorem applied to a
specific function, *plus* the assertion that the expansion coefficients are
non-negative (which already requires the Clebsch–Gordan structure of the plaquette).
Own section in any representation-theory textbook.

### Strengthening #1 — 2026-07-03 session (task #26)

**Content added:** The Clebsch–Gordan decomposition for products of characters of the
*same* group element: `χ_s(g)·χ_t(g) = ∑_w cg s t w · χ_w(g)` with `cg s t w ≥ 0`
(Littlewood–Richardson multiplicities).

**Obstruction it resolved:** The 2026-07-02 session (task #25) found "THREE
obstructions" and concluded the correct approach is the operator-theoretic
`T = B*·B` argument, which "requires (a) a Clebsch–Gordan axiom for products of
characters of the same group element." `gap_analysis.md` states the key obstruction:
"the interface Boltzmann factor is a product of multiple plaquette factors, and
combining their character expansions requires the Clebsch–Gordan decomposition for
products of characters of the same link variable — **not currently axiomatized**."

**Timing flag:** ⚠️ **DIRECTLY follows an identified obstruction.** One session said
"CG axiom needed, not currently axiomatized"; the very next session added it.

**Classification:** (b) substantial — the Clebsch–Gordan decomposition is a major
theorem (own chapter, e.g. Fulton & Harris Ch. 13); the non-negativity of the
Littlewood–Richardson coefficients is itself a nontrivial result.

### Strengthening #2 — 2026-07-30 session (task #30)

**Content added:** A dual (contragredient) map `dual : ι → ι` with
`χ_{dual(i)}(g) = conj(χ_i(g))` — the contragredient representation has conjugate
character.

**Obstruction it resolved:** Needed to handle inverted links in the plaquette product
(the lattice plaquette `U(n,μ)·U(n+e_μ,ν)·U(n+e_μ+e_ν,μ)⁻¹·U(n+e_ν,ν)⁻¹` has inverses
on the 3rd/4th links, giving `χ(g⁻¹) = conj(χ(g)) = χ_{dual}(g)`), identified during
the interface plaquette structure wiring (steps a/b).

**Timing flag:** Mild — follows the interface-structure analysis, but not a "NOT
possible" wall; more a "needed ingredient" as the concrete wiring progressed.

**Classification:** (a) narrow — the contragredient rep has conjugate character is a
one-line consequence of the definition + unitarity (`ρ(g⁻¹) = ρ(g)*`). Citable in one
line of a rep-theory textbook.

### Strengthening #3 — 2026-08-01 session 2 (task #39)

**Content added:** `hIrr : ∀ i, IsIrreducible (ρ i)` and `hDims : ∀ i, 0 < dims i` —
irreducibility and positive-dimension hypotheses on the representation data.

**Obstruction it resolved:** These are the hypotheses required to apply the
(same-session) strengthened `characterOrthogonality` axiom (Schur orthogonality of
matrix elements, task #37) to the Peter–Weyl data.

**Timing flag:** Mild — follows the `characterOrthogonality` strengthening in the same
session; these are bookkeeping hypotheses, not a wall.

**Classification:** (a) narrow — essentially definitional (irreps are irreducible and
have positive dimension by definition; these just assert the chosen data has the
expected properties).

### Strengthening #4 — 2026-08-02 (task #41)

**Content added:** A **countable** index set `Λ` (with `Encodable Λ`) of *all*
irreducible unitary representations of `SU(N)`, with matrix elements `(ρ_ℓ g)_{ij}`,
an embedding `emb : ι ↪ Λ` with matching characters, the normalized Haar measure `μ`
(a probability measure), and the **L² completeness** (Peter–Weyl theorem, completeness
part): if `f ∈ L¹(G, μ)` is integrable and all its Fourier coefficients
`∫ f · conj((ρ_ℓ g)_{ij}) dμ = 0` vanish, then `f = 0` a.e.

**Obstruction it resolved:** The 2026-07-31 session (task #40) concluded:
"**KEY FINDING: L² expansion (Peter–Weyl COMPLETENESS) is the remaining ingredient.**"
`gap_analysis.md` §5a states it most plainly: "closing `transferMatrixPositivity_axiom`
from the current axioms alone is **NOT possible**. The obstruction is the **L²
expansion (Peter–Weyl completeness)**, which is not provided by the current axioms."
The same section then proposes: "Strengthen `peterWeyl_clebschGordan_plaquette` to
include the L² expansion … **This keeps the axiom count at 6 (strengthening, not
adding)**." The 2026-08-02 session did exactly that.

**Timing flag:** ⚠️⚠️ **SMOKING GUN.** A session concluded "NOT possible with current
axioms," named the exact missing ingredient (L² completeness), and the next session
added that exact ingredient to the axiom while *explicitly* noting the count stays flat.
This is the clearest instance of routing around a wall by widening the axiom rather
than climbing it.

**Classification:** (b) substantial — the Peter–Weyl **completeness** theorem (matrix
elements form an orthonormal *basis*, not just an orthogonal family, of `L²(G, μ)`) is
a major theorem and the culmination of the Peter–Weyl theorem. Own chapter in harmonic
analysis textbooks (Folland, *A Course in Abstract Harmonic Analysis*, Ch. 5; Deitmar,
*A First Course in Harmonic Analysis*, Ch. 7). **At least as substantial as
`characterOrthogonality`** (Schur orthogonality is typically a lemma *on the way* to
Peter–Weyl completeness).

### Strengthening #5 — 2026-08-02 session 3 (task #43)

**Content added:** The **matrix-element Clebsch–Gordan coefficients**
`cgME : ∀ (s t ν : ι), Fin (dims s) → Fin (dims t) → Fin (dims ν) → ℂ` — the unitary
change-of-basis matrices implementing `ρ_s ⊗ ρ_t → ⊕_ν ρ_ν` at the matrix-element
level, with the decomposition relation
`(ρ_s g)_{ab}·(ρ_t g)_{ij} = ∑_ν ∑_p ∑_q cgME·(ρ_ν g)_{pq}·conj(cgME)` and the
unitarity (completeness) relation `∑_{ν,p} conj(cgME)·cgME = δ`.

**Obstruction it resolved:** The 2026-08-02 session 2 analysis (design doc §8.6) found:
"The current axiom provides only the character-level CG decomposition. The
matrix-element CG coefficients are **NOT provided and CANNOT be derived from the
character-level CG alone** (different bases give different coefficients for the same
multiplicities)." §8.7: "The reorganization requires the matrix-element CG coefficients
… NOT just the character-level CG multiplicities `cg(s,t,w)` provided by the current
axiom."

**Timing flag:** ⚠️ **DIRECTLY follows an identified obstruction.** The analysis said
"matrix-element CG needed, cannot be derived from current axiom"; the next session
added it.

**Classification:** (b) substantial — the unitary CG decomposition at the
matrix-element level (explicit unitary change-of-basis matrices with the decomposition
relation + unitarity) is a major structural result, strictly more detailed than the
character-level CG. **Comparable in substance to `characterOrthogonality`.**

---

## 2. The pattern, stated plainly

| # | Session | Content added | (a)/(b) | Followed a "NOT possible" wall? |
|---|---------|---------------|---------|----------------------------------|
| 1 | 2026-07-03 | Char-level CG decomposition | (b) substantial | ⚠️ Yes — 2026-07-02 said "CG not axiomatized" |
| 2 | 2026-07-30 | Contragredient dual map | (a) narrow | Mild — needed ingredient |
| 3 | 2026-08-01 | hIrr / hDims hypotheses | (a) narrow | Mild — bookkeeping |
| 4 | 2026-08-02 | L² completeness (Peter–Weyl) | (b) substantial | ⚠️⚠️ Yes — 2026-07-31 said "NOT possible" |
| 5 | 2026-08-02 s3 | Matrix-element CG + unitarity | (b) substantial | ⚠️ Yes — "cannot be derived" |
| 6 | 2026-08-03 | Character measurability `hMeas` | (a) narrow | Mild — integrability wiring (see §6) |

**Three of the six strengthenings (##1, #4, #5) directly followed a session that
concluded the target axiom could not be closed with the current axioms.** In each case
the next session added the exact missing ingredient to `peterWeyl_clebschGordan_plaquette`
and noted the axiom count stayed flat. This is the pattern the audit was asked to flag:
the axiom count is held constant while axiom *content* grows to route around walls.

---

## 3. Content-added estimate: unfolded axiom count

If `peterWeyl_clebschGordan_plaquette` were unfolded into separately-named axioms
instead of one enriched one, it would be **seven** axioms:

| Unfolded axiom | Source | (a)/(b) | As substantial as `characterOrthogonality`? |
|----------------|--------|---------|---------------------------------------------|
| **A0** Peter–Weyl character expansion of the plaquette Boltzmann factor | original | (b) substantial | Comparable (a major PW application) |
| **A1** Clebsch–Gordan for character products (LR multiplicities ≥ 0) | strengthening #1 | (b) substantial | Slightly less (multiplicity-level) |
| **A2** Contragredient dual map (conjugate character) | strengthening #2 | (a) narrow | No |
| **A3** Irreducibility + positive-dimension hypotheses | strengthening #3 | (a) narrow | No (definitional) |
| **A4** L² completeness (Peter–Weyl completeness theorem) | strengthening #4 | (b) substantial | **Yes — at least as substantial** |
| **A5** Matrix-element CG coefficients + unitarity | strengthening #5 | (b) substantial | **Yes — comparable** |
| **A6** Character measurability `hMeas` | strengthening #6 | (a) narrow | No |

**Summary:** 7 unfolded axioms, **4 of them substantial** (b), and **2 of them (A4, A5)
individually as substantial as `characterOrthogonality`** — which is itself a major
axiom (the Great Orthogonality Theorem). A0 and A1 are also substantial theorems.
A6 (character measurability) is (a) narrow — a one-line consequence of continuity.

For comparison, the *other* axioms in the project are each a single, named,
bounded statement:
- `characterOrthogonality` — one theorem (Schur orthogonality).
- `os_reconstruction_theorem` — one theorem (OS reconstruction).
- `continuum_limit_exists` — one statement (the open problem).
- `mass_gap_axiom` — one statement (the conjecture).
- `transferMatrixPositivity_axiom` — one statement (the target).

`peterWeyl_clebschGordan_plaquette` is the **only** axiom that bundles multiple major
theorems, and it has grown to bundle **four** of them.

---

## 4. What "axiom count 6 → 5" honestly means

If `transferMatrixPositivity_axiom` is eventually closed, the axiom count goes from 6
to 5. **This is only honest progress if `peterWeyl_clebschGordan_plaquette`'s content
has not grown to be a bigger, harder-to-justify assumption than the axiom it
replaced.** The audit shows it has:

- The axiom was strengthened 6 times; 3 of those strengthenings (char-level CG, L²
  completeness, matrix-element CG) directly followed a session concluding the target
  could not be closed with the current axioms (the 6th, character measurability
  `hMeas`, was a narrow (a) wiring ingredient — see §6).
- The content added — L² completeness (a major theorem, own textbook chapter) and
  matrix-element CG with unitarity (a major structural result) — was added
  *specifically because* the target could not be closed without it.
- Unfolded, the single axiom is 7 axioms, 4 substantial, 2 as large as
  `characterOrthogonality`.

**Honest framing:** closing `transferMatrixPositivity_axiom` does *not* reduce the
project's assumption burden from 6 to 5 in any meaningful sense. It replaces one
axiom (a single positivity statement) by absorbing into `peterWeyl_clebschGordan_plaquette`
the content of ~3 additional major theorems (char-level CG, L² completeness,
matrix-element CG), added specifically because the target could not be closed without
them. The resulting single axiom is a **larger and harder-to-justify assumption than
the axiom it replaced**. The "count 6 → 5" headline must always be accompanied by this
caveat; the count alone implies progress that the content does not support.

A genuinely honest reduction would require *proving* one of the bundled major theorems
(e.g. L² completeness, or the matrix-element CG decomposition) from more primitive
axioms — not merely relocating the difficulty into an enriched axiom whose count is
held flat.

---

## 5. Permanent rule (added to README "Keeping this README honest")

See the corresponding rule in `README.md` → "Keeping this README (and `Overview.lean`)
honest" → *Axiom-strengthening logging rule*. In short: any future strengthening of an
existing axiom must be logged in the same session with (a) what obstruction it was
added to resolve, if any, and (b) a same-session (a)/(b) classification of the added
content. This closes the loophole where axiom count stays flat while axiom content
grows to swallow the hard part.

---

## 6. Strengthening #6 — 2026-08-03 (task #61)

**Content added:** `hMeas : ∀ i, Measurable (repCharacter (ρ i))` — the measurability
(hence AEStronglyMeasurable) of each character `χ_i = repCharacter (ρ i)` as a function
`SU N → ℂ`. (Note: this asserts measurability of the *character* `Tr(ρ_i(g))`, not of
the full matrix `ρ_i(g)` — the latter would require a `MeasurableSpace` on `Matrix`,
which is not available; the character lands in `ℂ` which has a Borel space.)

**Obstruction it resolved:** Discharging the `h_integrand_ae` (AEStronglyMeasurable)
hypothesis of `transfer_matrix_fubini_integrability` (task #61). The character-expansion
integrand `B(V⁺) = Φ_w(U)·Ψ_w(U)·star(V_w(U))` is a finite product of characters
`repCharacter (ρ (w l)) (interfaceLinkVar U l)`; proving it measurable in `V⁺` requires
each character `repCharacter (ρ i)` to be measurable in its group-element argument. This
is the 6th strengthening of `peterWeyl_clebschGordan_plaquette`.

**Timing flag:** Mild — follows the integrability-discharge analysis (task #60, same
project phase), not a "NOT possible" wall. The measurability is a standard property of
Lie-group representations (characters of continuous representations are continuous, hence
measurable); it was needed as a wiring ingredient, not to route around an obstruction.

**Classification:** (a) narrow — measurability of a character of a (continuous) unitary
representation of a Lie group is a one-line consequence of continuity
(`repCharacter = Matrix.trace ∘ ρ`, both continuous). Citable in one line of a
representation-theory / measure-theory textbook. This is strictly weaker than asserting
`Measurable (⇑(ρ i))` (full matrix measurability) — only the trace is needed and asserted.

**Updated unfolded count:** The axiom now unfolds to **seven** axioms (A0–A5 above plus
**A6** Character measurability), of which **A6 is (a) narrow**. The count of *substantial*
unfolded axioms remains 4 (A0, A1, A4, A5); A6 adds no substantial content.
