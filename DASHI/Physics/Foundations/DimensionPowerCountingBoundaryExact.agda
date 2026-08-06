module DASHI.Physics.Foundations.DimensionPowerCountingBoundaryExact where

open import DASHI.Core.Prelude

import DASHI.Algebra.Quantum.DimensionFixedPoint as ExistingDimension
import DASHI.Algebra.Quantum.SignatureDerivation as ExistingSignature

------------------------------------------------------------------------
-- Causal order, local finiteness, holographic scaling, and Lorentz structure
-- are recorded separately from any theorem selecting four dimensions.

data CandidateDimension : Set where
  dimension2 : CandidateDimension
  dimension3 : CandidateDimension
  dimension4 : CandidateDimension
  dimension5 : CandidateDimension
  dimension6 : CandidateDimension

dimensionNumber : CandidateDimension → Nat
dimensionNumber dimension2 = 2
dimensionNumber dimension3 = 3
dimensionNumber dimension4 = 4
dimensionNumber dimension5 = 5
dimensionNumber dimension6 = 6

record CausalOrderProfile : Set where
  constructor causalOrderProfile
  field
    candidateDimension : CandidateDimension
    locallyFinite : Bool
    lorentzianCandidate : Bool
    boundaryScalingRelativeToDimension : Bool

open CausalOrderProfile public

causalProfile2 : CausalOrderProfile
causalProfile2 = causalOrderProfile dimension2 true true true

causalProfile4 : CausalOrderProfile
causalProfile4 = causalOrderProfile dimension4 true true true

sameQualitativePremisesDifferentDimensions :
  locallyFinite causalProfile2 ≡ locallyFinite causalProfile4
  ×
  lorentzianCandidate causalProfile2 ≡ lorentzianCandidate causalProfile4
  ×
  boundaryScalingRelativeToDimension causalProfile2
  ≡
  boundaryScalingRelativeToDimension causalProfile4
sameQualitativePremisesDifferentDimensions = refl , (refl , refl)

------------------------------------------------------------------------
-- Dimension may be estimated from order statistics, but estimation is not a
-- uniqueness theorem.

data OrderingFractionBand : Set where
  sparseOrderingBand : OrderingFractionBand
  mediumOrderingBand : OrderingFractionBand
  denseOrderingBand : OrderingFractionBand

dimensionEstimate : OrderingFractionBand → CandidateDimension
dimensionEstimate sparseOrderingBand = dimension5
dimensionEstimate mediumOrderingBand = dimension4
dimensionEstimate denseOrderingBand = dimension2

mediumOrderingEstimatesFour :
  dimensionEstimate mediumOrderingBand ≡ dimension4
mediumOrderingEstimatesFour = refl

existingDimensionAxiomCarrier : Set₁
existingDimensionAxiomCarrier = ExistingDimension.DimensionFixedPointAxioms

existingSignatureAxiomCarrier : Set₁
existingSignatureAxiomCarrier = ExistingSignature.SignatureDerivationAxioms

------------------------------------------------------------------------
-- Interaction-specific power counting.

data InteractionKind : Set where
  scalarQuarticInteraction : InteractionKind
  scalarCubicInteraction : InteractionKind
  ordinaryYangMillsInteraction : InteractionKind

data PowerCountingClass : Set where
  superRenormalisableClass : PowerCountingClass
  marginalClass : PowerCountingClass
  powerCountingNonrenormalisableClass : PowerCountingClass

quarticClass : CandidateDimension → PowerCountingClass
quarticClass dimension2 = superRenormalisableClass
quarticClass dimension3 = superRenormalisableClass
quarticClass dimension4 = marginalClass
quarticClass dimension5 = powerCountingNonrenormalisableClass
quarticClass dimension6 = powerCountingNonrenormalisableClass

cubicClass : CandidateDimension → PowerCountingClass
cubicClass dimension2 = superRenormalisableClass
cubicClass dimension3 = superRenormalisableClass
cubicClass dimension4 = superRenormalisableClass
cubicClass dimension5 = superRenormalisableClass
cubicClass dimension6 = marginalClass

yangMillsClass : CandidateDimension → PowerCountingClass
yangMillsClass dimension2 = superRenormalisableClass
yangMillsClass dimension3 = superRenormalisableClass
yangMillsClass dimension4 = marginalClass
yangMillsClass dimension5 = powerCountingNonrenormalisableClass
yangMillsClass dimension6 = powerCountingNonrenormalisableClass

quarticIsMarginalInFour : quarticClass dimension4 ≡ marginalClass
quarticIsMarginalInFour = refl

cubicIsMarginalInSix : cubicClass dimension6 ≡ marginalClass
cubicIsMarginalInSix = refl

yangMillsIsMarginalInFour :
  yangMillsClass dimension4 ≡ marginalClass
yangMillsIsMarginalInFour = refl

criticalDimensionDependsOnInteraction :
  quarticClass dimension4 ≡ marginalClass
  ×
  cubicClass dimension4 ≡ superRenormalisableClass
criticalDimensionDependsOnInteraction = refl , refl

------------------------------------------------------------------------
-- Four-volume is admitted only after a four-dimensional completion witness.

data SignatureClass : Set where
  oneTimeOneSpace : SignatureClass
  oneTimeThreeSpace : SignatureClass
  oneTimeFourSpace : SignatureClass

record LorentzianCompletion : Set where
  constructor lorentzianCompletion
  field
    completedDimension : CandidateDimension
    completedSignature : SignatureClass
    globallyHyperbolicCandidate : Bool

open LorentzianCompletion public

data InvariantVolumeKind : Set where
  twoVolume : InvariantVolumeKind
  threeVolume : InvariantVolumeKind
  fourVolume : InvariantVolumeKind
  fiveVolume : InvariantVolumeKind
  sixVolume : InvariantVolumeKind

invariantVolumeFor : LorentzianCompletion → InvariantVolumeKind
invariantVolumeFor completion with completedDimension completion
... | dimension2 = twoVolume
... | dimension3 = threeVolume
... | dimension4 = fourVolume
... | dimension5 = fiveVolume
... | dimension6 = sixVolume

canonicalFourCompletion : LorentzianCompletion
canonicalFourCompletion =
  lorentzianCompletion dimension4 oneTimeThreeSpace true

fourVolumeFollowsFromFourCompletion :
  invariantVolumeFor canonicalFourCompletion ≡ fourVolume
fourVolumeFollowsFromFourCompletion = refl

------------------------------------------------------------------------
-- A dimension-selection programme may define a feasible set or objective, but
-- a unique minimiser at D=4 is an additional theorem.

data DimensionViability : Set where
  dimensionExcluded : DimensionViability
  dimensionAdmissible : DimensionViability
  dimensionPreferredByAdditionalAxiom : DimensionViability

dimensionViability : CandidateDimension → DimensionViability
dimensionViability dimension2 = dimensionAdmissible
dimensionViability dimension3 = dimensionAdmissible
dimensionViability dimension4 = dimensionPreferredByAdditionalAxiom
dimensionViability dimension5 = dimensionAdmissible
dimensionViability dimension6 = dimensionAdmissible

record DimensionSelectionBoundary : Set where
  constructor dimensionSelectionBoundary
  field
    causalOrderAndLocalFinitenessForceFour : Bool
    causalOrderAndLocalFinitenessForceFourIsFalse :
      causalOrderAndLocalFinitenessForceFour ≡ false

    holographicScalingForcesFour : Bool
    holographicScalingForcesFourIsFalse :
      holographicScalingForcesFour ≡ false

    lorentzInvarianceForcesThreeSpatialDimensions : Bool
    lorentzInvarianceForcesThreeSpatialDimensionsIsFalse :
      lorentzInvarianceForcesThreeSpatialDimensions ≡ false

    allInteractingFieldTheoriesOutsideFourFail : Bool
    allInteractingFieldTheoriesOutsideFourFailIsFalse :
      allInteractingFieldTheoriesOutsideFourFail ≡ false

    yangMillsMarginalityAloneProvesPhysicalDimension : Bool
    yangMillsMarginalityAloneProvesPhysicalDimensionIsFalse :
      yangMillsMarginalityAloneProvesPhysicalDimension ≡ false

    existingStableFixedPointAxiomIsAnIndependentDerivation : Bool
    existingStableFixedPointAxiomIsAnIndependentDerivationIsFalse :
      existingStableFixedPointAxiomIsAnIndependentDerivation ≡ false

open DimensionSelectionBoundary public

canonicalDimensionSelectionBoundary : DimensionSelectionBoundary
canonicalDimensionSelectionBoundary =
  dimensionSelectionBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
