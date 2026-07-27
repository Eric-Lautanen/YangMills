# Implementation Plan: Periodic Boundary Conditions for Reflection Positivity

## Objective

Replace the current `Z4Site = ℤ⁴` lattice with a lattice that has periodic boundary
conditions in the time direction, making the `hadd` hypothesis satisfiable for finite
lattices. This enables a genuine proof of the Osterwalder-Seiler reflection positivity.

## Design

### Step 1: Define `TimeIndex` as a finite cyclic group

Add to `Lattice.lean`:

```lean
/-- Time index for a finite lattice with periodic boundary conditions.
    ℤ_T = ZMod T where T : ℕ is the number of time slices. -/
abbrev TimeIndex (T : ℕ) : Type := ZMod T
```

Or more generally, keep `Z4Site` as `ℤ⁴` but define `addVector` and `reflectSite`
to work modulo `T` for the time coordinate when the lattice is a product of intervals.

**Recommendation**: Define a structure `PeriodicLattice (T L : ℕ)` that represents
the product `(ZMod T) × (ZMod L)³` and provides `addVector` and `reflectSite` with
modular arithmetic.

### Step 2: Modify `addVector` for periodic BCs

```lean
def addVectorPeriodic (T : ℕ) (n : ZMod T × ZMod T × ZMod T × ZMod T) (μ : Fin 4) : ... :=
  match μ with
  | 0 => (n.1 + 1, n.2.1, n.2.2.1, n.2.2.2)  -- wraps in ZMod
  | 1 => (n.1, n.2.1 + 1, n.2.2.1, n.2.2.2)
  | 2 => (n.1, n.2.1, n.2.2.1 + 1, n.2.2.2)
  | 3 => (n.1, n.2.1, n.2.2.1, n.2.2.2 + 1)
```

The `ZMod` addition automatically wraps around modulo T/L.

### Step 3: Modify `reflectSite` for periodic BCs

```lean
def reflectSitePeriodic (T : ℕ) (n : ZMod T × ZMod T × ZMod T × ZMod T) :=
  (-n.1, n.2.1, n.2.2.1, n.2.2.2)
```

In `ZMod T`, `-k` is `T-k` (mod T), so `-(-k) = k`. This is involutive.

### Step 4: Update `Z4Site` or create a parallel type

Decision: Either:
- **A1**: Replace `Z4Site` everywhere. This is invasive.
- **A2**: Create `PeriodicZ4Site T L` as a separate type and dual-wire the
  definitions. This adds complexity but preserves backward compatibility.
- **A3**: Parameterize `Z4Site` by the time lattice type.

**Recommendation**: A1 is cleanest now that the project is still in early stages.
Replace `Z4Site : Type := ℤ × ℤ × ℤ × ℤ` with `PeriodicSite (T L : ℕ) : Type :=
ZMod T × ZMod L × ZMod L × ZMod L`.

### Step 5: Re-prove the basic lemmas

- `reflectSite_involution`: `reflectSite (reflectSite n) = n` with ZMod arithmetic.
- `reflection_involution_z4`: `reflectLinkVariableZ4 N (reflectLinkVariableZ4 N U) = U`.

### Step 6: Prove action invariance under reflection

```lean
lemma wilsonActionFinite_reflection_invariant (N T L : ℕ) (β : ℝ) 
    (U : LinkVariable (SU N) (PeriodicSite T L)) :
    wilsonActionFinite N β (Finset.univ : Finset (PeriodicSite T L)) (reflectLinkVariableZ4 N U) =
    wilsonActionFinite N β (Finset.univ : Finset (PeriodicSite T L)) U := ...
```

Proof: Each plaquette contribution at (n, μ, ν) maps to a contribution at (reflectSite n, μ', ν')
under reflection. The sum over all sites covers each plaquette exactly once because
reflection is a bijection on the finite lattice.

### Step 7: Action decomposition (Osterwalder-Seiler)

Define the positive-time, negative-time, and interface parts of the action:

```lean
def wilsonActionPositive (N T L : ℕ) (β : ℝ) (U : LinkVariable (SU N) (PeriodicSite T L)) : ℝ :=
  ∑ n ∈ sites_with_time_gt_0, ∑ μ ν, plaquetteContribution N β U n μ ν

def wilsonActionNegative (N T L : ℕ) (β : ℝ) (U : LinkVariable (SU N) (PeriodicSite T L)) : ℝ :=
  ∑ n ∈ sites_with_time_lt_0, ∑ μ ν, plaquetteContribution N β U n μ ν

def wilsonActionInterface (N T L : ℕ) (β : ℝ) (U : LinkVariable (SU N) (PeriodicSite T L)) : ℝ :=
  ∑ n ∈ sites_with_time_eq_0, ∑ μ ν, plaquetteContribution N β U n μ ν
```

Prove:
1. `total_decomposition`: `S_W = S⁺ + S⁻ + S_int`
2. `neg_reflection`: `S⁻[U] = S⁺[θU]`
3. `interface_symmetric`: `S_int[θU] = S_int[U]`

### Step 8: Complete the reflection positivity proof

Using the decomposition:

⟨f·θf⟩ = (1/Z) ∫ f(U) f(θU) exp(-β(S⁺+S⁻+S_int)) dU
       = (1/Z) ∫ f(U) exp(-βS⁺) · f(θU) exp(-βS⁺[θU]) · exp(-βS_int) dU
       = (1/Z) ∫ |f(U) exp(-βS⁺[U]) · sqrt(exp(-βS_int[U]))|² dU  [with change of variables]
       ≥ 0

The key change of variables: split the integration variables into U⁺ (positive time) and
U⁻ (negative time), and replace U⁻ by θU⁺.

### Step 9: Verify the Z4Expectation structure

Update `wilsonZ4Expectation` to work with the new lattice type. The `hadd` hypothesis
is no longer needed (or is trivially satisfied by the periodic structure).

## Dependencies between steps

```
Step 1 (type definition)
  → Step 2, 3 (basic operations)
    → Step 4 (integration into existing code)
      → Step 5 (basic lemmas)
        → Step 6 (action invariance)
          → Step 7 (decomposition)
            → Step 8 (final proof)
              → Step 9 (structure update)
```

## Estimated effort

- Steps 1-4: 1-2 sessions (type refactoring, updating dependent definitions)
- Step 5: 1 session (proving basic lemmas in the new setting)
- Steps 6-7: 2-3 sessions (combinatorial decomposition of the action)
- Steps 8-9: 1-2 sessions (final reflection positivity proof, structure cleanup)

Total: 5-8 sessions of focused work.

## Test: Build after each step

After each step, run `lake build` to ensure the project still compiles.
