module DASHI.Physics.YangMills.BalabanClayGate4PreferredSelectedProbabilityExact where

------------------------------------------------------------------------
-- PREFERRED GATE4 REFERENCE -> SELECTED T5 FINITE PROBABILITY PRESENTATION
--
-- The preferred rational reference constructor has already fixed all scalar
-- algebra and cone semantics.  Therefore the only remaining probability-side
-- physical weld at each cutoff is same-object representation:
--
--   reopening fineStates = selected Gate4 fast fibre
--   reopening fineWeight = normalized Gate4 reference weight.
--
-- From those equalities the normalized/nonnegative finite probability law and
-- the all-cutoff T5 probability presentation are compiler output.
------------------------------------------------------------------------

open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4PreferredRationalReferenceNormalizationExact as Preferred
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceToFiniteRGProbabilityExact as Gate4
import DASHI.Physics.YangMills.BalabanFiniteRGProbabilityExpectationSemanticsExact as Probability
import DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanFiniteVolumeReopeningPresentationRound283Exact as R283
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5

record PreferredSelectedProbabilityInputs
    {Scale Fine SlowField Component Functional Coarse Measure : Set}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    (referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction})
    (thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ)
    (presentation :
      R283.FiniteVolumeReopeningPresentation
        Measure Fine Coarse thermodynamic) : Set₁ where
  field
    normalizedReferenceWeldAt : ∀ cutoff →
      Gate4.NormalizedReferenceReopeningWeld
        (Preferred.preferredRationalReferenceFoldSemantics referenceInputs)
        (R283.stepAt presentation cutoff)

open PreferredSelectedProbabilityInputs public

compilePreferredSelectedT5ProbabilityPresentation :
  ∀ {Scale Fine SlowField Component Functional Coarse Measure}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction}}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData
        Measure (Reopen.Observable Fine) ℚ}
    {presentation :
      R283.FiniteVolumeReopeningPresentation
        Measure Fine Coarse thermodynamic} →
  PreferredSelectedProbabilityInputs
    referenceInputs thermodynamic presentation →
  Probability.SelectedT5FiniteProbabilityPresentation
    Measure Fine Coarse thermodynamic
compilePreferredSelectedT5ProbabilityPresentation
  {referenceInputs = referenceInputs}
  {thermodynamic = thermodynamic}
  {presentation = presentation} inputs =
  Gate4.compileGate4SelectedT5FiniteProbabilityPresentation
    {semantics =
      Preferred.preferredRationalReferenceFoldSemantics referenceInputs}
    {thermodynamic = thermodynamic}
    {presentation = presentation}
    record
      { normalizedReferenceWeldAt =
          normalizedReferenceWeldAt inputs
      }

preferredSelectedProbabilityCompilerLevel : ProofLevel
preferredSelectedProbabilityCompilerLevel = machineChecked

-- This is now the sole probability-law representation payment on this route.
preferredReferenceReopeningSameObjectLevel : ProofLevel
preferredReferenceReopeningSameObjectLevel = conditional
