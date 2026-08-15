/-
# Transfer Matrix

This file is a re-export point for the `TransferMatrix/` subdirectory.
The actual content is split across the sub-files:
- `Basic.lean`: Basic definitions (PosInterfaceConfig, transferMatrixCorrect, G, g_posInterface, etc.)
- `Step5.lean`: Step 5 sub-lemmas (temporal/spatial decomposition)
- `Bridge.lean`: Bridge lemmas, character factors, transfer matrix change of variables
- `Integrability.lean`: Integrability discharge, norm bounds, measurability lemmas
- `Fubini.lean`: Fubini steps, Fourier coefficients
- `KeyIdentity.lean`: The key identity ∫ G·G(θU) = ∫ g·(Tg)
- `SigmaInversion.lean`: Lemma 3 σ-inversion (thetaReindex)
- `ThetaInvariance.lean`: Lemma 3 invariance lemmas under θ
- `FullReflect.lean`: Full reflection reindexing (fullReflectReindex)
- `FullLattice.lean`: Full-lattice character factor lemmas
- `LuscherDecomposition.lean`: Spatial/temporal split of OS action (Step A.4 of Lüscher decomposition)
-/

import YangMills.Proofs.TransferMatrix.FullLattice
import YangMills.Proofs.TransferMatrix.LuscherDecomposition
