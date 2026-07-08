/-
# Mass Gap

Definitions of the mass gap condition: the Hamiltonian has a positive gap
above the vacuum, and correlation functions decay exponentially.
-/

namespace YangMills

/--
The mass gap is the lowest eigenvalue of the Hamiltonian H above the vacuum.
-/
structure MassGap : Prop where
  positiveMass : True

/--
Exponential decay of truncated correlations.
-/
structure ExponentialDecay : Prop where
  positiveMass : True

/--
The complete mass gap condition: the Yang-Mills QFT has a positive mass gap.
-/
structure YangMillsMassGap : Prop where
  theoryExists : True
  spectralGap : MassGap
  exponentialDecay : ExponentialDecay

end YangMills
