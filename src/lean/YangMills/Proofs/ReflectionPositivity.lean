/-
# Reflection Positivity

This file is a re-export point for the `ReflectionPositivity/` subdirectory.
The actual content is split across the sub-files:
- `PeriodicLattice.lean`: Periodic lattice, reflection observable, site/link structures
- `OSDecomposition.lean`: Osterwalder-Seiler decomposition (plaquette-based)
- `PlaquetteStructure.lean`: Interface plaquette enumeration, character structures, full link partition
- `CharacterExpansion.lean`: Interface link integral, temporal/spatial split, character expansion
- `FullBoltzmannPD.lean`: Full Boltzmann positive-definiteness, Lüscher decomposition
- `GaugeInvariance.lean`: Condition equivalence, gauge-invariance lemma, transferMatrixPositivity_axiom
- `CleanFactorization.lean`: Clean factorization and PD-structure obstruction
-/

import YangMills.Proofs.ReflectionPositivity.CleanFactorization
