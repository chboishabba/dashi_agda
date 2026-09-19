module DASHI.Physics.YangMills.BalabanClayGate4RawSlowDensityToProbabilityExact where

------------------------------------------------------------------------
-- RAW FINITE SLOW-FIELD DENSITY -> NORMALIZED GATE4 COARSE LAW
--
-- The source-facing finite object is now unnormalized density data.  Exact
-- finite rational normalization constructs the coarse probability law consumed
-- by the corrected Gate4 conditional-mixture reopening.
------------------------------------------------------------------------

open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFinitePositiveWeightNormalizationExact as Normalize
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4PreferredRationalReferenceNormalizationExact as Preferred
import DASHI.Physics.YangMills.BalabanClayGate4ConstrainedReferenceKernelExact as Kernel
import DASHI.Physics.YangMills.BalabanClayGate4ConditionalMixtureReopeningExact as Mixture

record Gate4RawSlowFieldDensity
    {Scale Fine SlowField Component Functional : Set}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    (referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction})
    (typed :
      Kernel.TypedReferenceCoarseConstraint referenceInputs) : Set₁ where
  field
    scale : Scale
    component : Component

    rawSlowWeights :
      Normalize.FinitePositiveWeightFamily SlowField

open Gate4RawSlowFieldDensity public

compileGate4SlowFieldProbabilityLaw :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction}}
    {typed :
      Kernel.TypedReferenceCoarseConstraint referenceInputs} →
  Gate4RawSlowFieldDensity referenceInputs typed →
  Mixture.Gate4SlowFieldProbabilityLaw referenceInputs typed
compileGate4SlowFieldProbabilityLaw dataSet = record
  { scale = scale dataSet
  ; component = component dataSet
  ; slowStates =
      Normalize.states (rawSlowWeights dataSet)
  ; slowWeight =
      Normalize.normalizedWeight (rawSlowWeights dataSet)
  ; slowWeightNonnegative =
      Normalize.normalizedWeightNonnegative (rawSlowWeights dataSet)
  ; slowWeightNormalized =
      Normalize.normalizedWeightMassOne (rawSlowWeights dataSet)
  }

compileRawSlowDensityReopeningStep :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction}}
    {typed :
      Kernel.TypedReferenceCoarseConstraint referenceInputs} →
  Gate4RawSlowFieldDensity referenceInputs typed →
  DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact.FiniteRGReopeningStep
    Fine SlowField
compileRawSlowDensityReopeningStep dataSet =
  Mixture.gate4ConditionalMixtureReopeningStep
    (compileGate4SlowFieldProbabilityLaw dataSet)

rawSlowDensityNormalizationCompilerLevel : ProofLevel
rawSlowDensityNormalizationCompilerLevel = machineChecked

rawSlowDensityToReopeningCompilerLevel : ProofLevel
rawSlowDensityToReopeningCompilerLevel = machineChecked

-- Actual source payment: construct these raw finite slow-field weights from the
-- selected CMP119/CMP122 complete density on the same cutoff/state carrier.
literalCMP119RawSlowFieldDensityLevel : ProofLevel
literalCMP119RawSlowFieldDensityLevel = conditional
