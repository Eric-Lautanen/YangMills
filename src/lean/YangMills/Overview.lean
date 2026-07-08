/-
# Overview

Project structure, references, and current status for the Yang-Mills
formalization effort.

## Current Status (Phase 3: Formal Problem Definition)

Completed:
- OS Axioms skeleton (OSAxioms.lean)
- Gauge Theory foundations (GaugeTheory.lean)
- Lattice Gauge Theory (Lattice.lean)
- Mass Gap definition (MassGap.lean)

## References

- A. Jaffe, E. Witten, "Quantum Yang-Mills Theory" (Clay Millennium Problem)
- R. Streater, A. Wightman, "PCT, Spin and Statistics, and All That"
- J. Glimm, A. Jaffe, "Quantum Physics: A Functional Integral Point of View"
- K. Osterwalder, R. Schrader, "Axioms for Euclidean Green's Functions"
- T. Balaban, "Renormalization group approach to lattice gauge field theories"
- M. Hairer, "A theory of regularity structures"
- S. Chatterjee, "Yang-Mills for probabilists"
- K. Wilson, "Confinement of quarks"
-/
namespace YangMills

def description : String :=
  "Formalization of Yang-Mills existence and mass gap problem (Clay Millennium Prize)"

end YangMills
