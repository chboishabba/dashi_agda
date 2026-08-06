module DASHI.Physics.Foundations.FiniteStatisticalFiltrationExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Physical states, probability laws, and coordinates on a statistical model
-- are distinct finite carriers.

data PhysicalState : Set where
  physicalLeft : PhysicalState
  physicalRight : PhysicalState

data ProbabilityLaw : Set where
  balancedLaw : ProbabilityLaw
  leftBiasedLaw : ProbabilityLaw
  rightBiasedLaw : ProbabilityLaw

data ModelParameter : Set where
  parameterZero : ModelParameter
  parameterLeft : ModelParameter
  parameterRight : ModelParameter

parameterisedLaw : ModelParameter → ProbabilityLaw
parameterisedLaw parameterZero = balancedLaw
parameterisedLaw parameterLeft = leftBiasedLaw
parameterisedLaw parameterRight = rightBiasedLaw

-- A tagged coproduct makes the three levels disjoint by construction.  The
-- distinction is therefore an actual no-confusion theorem, not a proposition
-- inhabited trivially by unit.
data StatisticalObject : Set where
  physicalObject : PhysicalState → StatisticalObject
  lawObject : ProbabilityLaw → StatisticalObject
  parameterObject : ModelParameter → StatisticalObject

physicalObjectCannotEqualLawObject :
  (state : PhysicalState) →
  (law : ProbabilityLaw) →
  physicalObject state ≡ lawObject law → ⊥
physicalObjectCannotEqualLawObject state law ()

lawObjectCannotEqualParameterObject :
  (law : ProbabilityLaw) →
  (parameter : ModelParameter) →
  lawObject law ≡ parameterObject parameter → ⊥
lawObjectCannotEqualParameterObject law parameter ()

------------------------------------------------------------------------
-- Finite Fisher-like distinguishability table on the parameter carrier.  It
-- is a declared statistical metric witness, not physical spacetime curvature.

parameterDistance : ModelParameter → ModelParameter → Nat
parameterDistance parameterZero parameterZero = 0
parameterDistance parameterZero parameterLeft = 1
parameterDistance parameterZero parameterRight = 1
parameterDistance parameterLeft parameterZero = 1
parameterDistance parameterLeft parameterLeft = 0
parameterDistance parameterLeft parameterRight = 2
parameterDistance parameterRight parameterZero = 1
parameterDistance parameterRight parameterLeft = 2
parameterDistance parameterRight parameterRight = 0

parameterDistanceSymmetric :
  (a b : ModelParameter) →
  parameterDistance a b ≡ parameterDistance b a
parameterDistanceSymmetric parameterZero parameterZero = refl
parameterDistanceSymmetric parameterZero parameterLeft = refl
parameterDistanceSymmetric parameterZero parameterRight = refl
parameterDistanceSymmetric parameterLeft parameterZero = refl
parameterDistanceSymmetric parameterLeft parameterLeft = refl
parameterDistanceSymmetric parameterLeft parameterRight = refl
parameterDistanceSymmetric parameterRight parameterZero = refl
parameterDistanceSymmetric parameterRight parameterLeft = refl
parameterDistanceSymmetric parameterRight parameterRight = refl

------------------------------------------------------------------------
-- Nested state spaces and coarse projections.

data FineState : Set where
  fineLeftLow : FineState
  fineLeftHigh : FineState
  fineRightLow : FineState
  fineRightHigh : FineState

data CoarseState : Set where
  coarseLeft : CoarseState
  coarseRight : CoarseState

coarseProjection : FineState → CoarseState
coarseProjection fineLeftLow = coarseLeft
coarseProjection fineLeftHigh = coarseLeft
coarseProjection fineRightLow = coarseRight
coarseProjection fineRightHigh = coarseRight

coarseProjectionIsNonInjective :
  coarseProjection fineLeftLow ≡ coarseProjection fineLeftHigh
coarseProjectionIsNonInjective = refl

fineStatesRemainDistinct : fineLeftLow ≡ fineLeftHigh → ⊥
fineStatesRemainDistinct ()

------------------------------------------------------------------------
-- Finite persistence interval: a topological feature is absent, then present
-- across two scales, then absent after final coarse collapse.

data FiltrationScale : Set where
  scaleZero : FiltrationScale
  scaleOne : FiltrationScale
  scaleTwo : FiltrationScale
  scaleThree : FiltrationScale

data FeatureStatus : Set where
  featureAbsent : FeatureStatus
  featurePresent : FeatureStatus

persistentFeature : FiltrationScale → FeatureStatus
persistentFeature scaleZero = featureAbsent
persistentFeature scaleOne = featurePresent
persistentFeature scaleTwo = featurePresent
persistentFeature scaleThree = featureAbsent

featurePersistsAcrossMiddleScales :
  persistentFeature scaleOne ≡ featurePresent
  ×
  persistentFeature scaleTwo ≡ featurePresent
featurePersistsAcrossMiddleScales = refl , refl

featureDiesAfterFinalCoarsening :
  persistentFeature scaleThree ≡ featureAbsent
featureDiesAfterFinalCoarsening = refl

record FiniteStatisticalFiltrationBoundary : Set where
  constructor finiteStatisticalFiltrationBoundary
  field
    physicalStateIsProbabilityDistribution : Bool
    physicalStateIsProbabilityDistributionIsFalse :
      physicalStateIsProbabilityDistribution ≡ false

    statisticalMetricIsPhysicalSpacetimeCurvature : Bool
    statisticalMetricIsPhysicalSpacetimeCurvatureIsFalse :
      statisticalMetricIsPhysicalSpacetimeCurvature ≡ false

    coarseProjectionPreservesEveryFineDistinction : Bool
    coarseProjectionPreservesEveryFineDistinctionIsFalse :
      coarseProjectionPreservesEveryFineDistinction ≡ false

    onePersistentFeatureProvesUniversalTopology : Bool
    onePersistentFeatureProvesUniversalTopologyIsFalse :
      onePersistentFeatureProvesUniversalTopology ≡ false

open FiniteStatisticalFiltrationBoundary public

canonicalFiniteStatisticalFiltrationBoundary :
  FiniteStatisticalFiltrationBoundary
canonicalFiniteStatisticalFiltrationBoundary =
  finiteStatisticalFiltrationBoundary false refl false refl false refl false refl
