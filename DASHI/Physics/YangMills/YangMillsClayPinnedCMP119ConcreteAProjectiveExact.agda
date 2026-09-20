{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteAProjectiveExact where

------------------------------------------------------------------------
-- A / ONE-FAMILY OS CONSTRUCTOR + SELECTED PROJECTIVE COMPACTNESS
--
-- The concrete A constructor produces the exact PinnedCMP119OSAxiomInputs used
-- by the selected projective compactness owner.  This adapter makes that
-- same-object relation definitional: the compactness sequence is literally the
-- finite normalized family used for OS1/OS2/OS3 and its target is literally the
-- same CMP119 limit expectation used by the continuum Schwinger family.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteAExact as A
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119SelectedProjectiveCompactnessExact as Compact
import DASHI.Physics.YangMills.BalabanClayT5SelectedSequentialConvergenceExact as Selected

record ConcreteAProjectiveInputs
    {G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Action Permutation
     sequenceLimit limitLaws quotient division S}
    (a :
      A.PinnedCMP119ConcreteAInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Action Permutation
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    (group : G) : Set₂ where
  field
    compactness :
      Compact.CMP119SelectedCompactnessInputs
        (A.asPinnedOSAxiomInputs a) group

open ConcreteAProjectiveInputs public

fullLiteralCMP119ExpectationSequenceConverges :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Action Permutation
      sequenceLimit limitLaws quotient division S}
    {a :
      A.PinnedCMP119ConcreteAInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Action Permutation
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S}
    {group : G} →
  ConcreteAProjectiveInputs a group →
  Selected.Converges
    (Compact.convergence (compactness _))
    (Compact.cmp119ExpectationSequence (A.asPinnedOSAxiomInputs a) group)
    (Compact.cmp119ExpectationTarget (A.asPinnedOSAxiomInputs a) group)
fullLiteralCMP119ExpectationSequenceConverges inputs =
  Compact.fullCMP119ExpectationSequenceConverges (compactness inputs)

concreteAProjectiveSameObjectCompilerLevel : ProofLevel
concreteAProjectiveSameObjectCompilerLevel = machineChecked

-- Remaining projective physics stays exactly where it belongs: tightness /
-- extraction and cylinder-determining cluster agreement on the literal family.
literalConcreteAProjectiveCompactnessLevel : ProofLevel
literalConcreteAProjectiveCompactnessLevel = conditional
