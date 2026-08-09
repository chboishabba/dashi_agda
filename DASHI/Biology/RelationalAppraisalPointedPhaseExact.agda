module DASHI.Biology.RelationalAppraisalPointedPhaseExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- Formalize the exact cardinality ladder from a ternary A-B-outcome event to
-- bilateral appraisal, synthesis re-entry, and the pointed phase expansion
--
--   729 = (8 * 10 + 1) * 9 = 8 * 90 + 9.
--
-- The arithmetic and finite coordinate architecture are exact.  No claim is
-- made that these relational coordinates are an actual Monster module, that
-- they derive the coefficient ten, or that the twelve axes are the Monster's
-- twelve-dimensional symplectic quotient.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.TernaryHypercubeHyperfabricExact as Hyper

------------------------------------------------------------------------
-- Axis counts.
------------------------------------------------------------------------

data InteractionAxis : Set where
  participantAPosition : InteractionAxis
  participantBPosition : InteractionAxis
  immediateOutcome : InteractionAxis

data AppraisalAxis : Set where
  feelingAboutOutcome : AppraisalAxis
  preferredOutcome : AppraisalAxis
  synthesisPosition : AppraisalAxis

data Participant : Set where
  participantA : Participant
  participantB : Participant

interactionAxisCount : Nat
interactionAxisCount = 3

appraisalAxesPerParticipant : Nat
appraisalAxesPerParticipant = 3

participantCount : Nat
participantCount = 2

bilateralAppraisalAxisCount : Nat
bilateralAppraisalAxisCount =
  participantCount * appraisalAxesPerParticipant

oneRoundAxisCount : Nat
oneRoundAxisCount =
  interactionAxisCount + bilateralAppraisalAxisCount

synthesisReentryAxisCount : Nat
synthesisReentryAxisCount = 3

completeCycleAxisCount : Nat
completeCycleAxisCount =
  oneRoundAxisCount + synthesisReentryAxisCount

bilateralAppraisalAxisCountIsSix : bilateralAppraisalAxisCount ≡ 6
bilateralAppraisalAxisCountIsSix = refl

oneRoundAxisCountIsNine : oneRoundAxisCount ≡ 9
oneRoundAxisCountIsNine = refl

completeCycleAxisCountIsTwelve : completeCycleAxisCount ≡ 12
completeCycleAxisCountIsTwelve = refl

------------------------------------------------------------------------
-- Ternary cardinality ladder.
------------------------------------------------------------------------

initialInteractionStateCount : Nat
initialInteractionStateCount =
  Hyper.ternaryLatticeCount interactionAxisCount

appraisalFibreStateCount : Nat
appraisalFibreStateCount =
  Hyper.ternaryLatticeCount bilateralAppraisalAxisCount

oneRoundStateCount : Nat
oneRoundStateCount =
  Hyper.ternaryLatticeCount oneRoundAxisCount

completeCycleStateCount : Nat
completeCycleStateCount =
  Hyper.ternaryLatticeCount completeCycleAxisCount

centralCompletionGroupOrderPattern : Nat
centralCompletionGroupOrderPattern =
  3 * completeCycleStateCount

initialInteractionStateCountIs27 : initialInteractionStateCount ≡ 27
initialInteractionStateCountIs27 = refl

appraisalFibreStateCountIs729 : appraisalFibreStateCount ≡ 729
appraisalFibreStateCountIs729 = refl

oneRoundStateCountIs19683 : oneRoundStateCount ≡ 19683
oneRoundStateCountIs19683 = refl

completeCycleStateCountIs531441 : completeCycleStateCount ≡ 531441
completeCycleStateCountIs531441 = refl

centralCompletionGroupOrderPatternIs1594323 :
  centralCompletionGroupOrderPattern ≡ 1594323
centralCompletionGroupOrderPatternIs1594323 = refl

oneRoundFactorsAsBaseTimesFibre :
  oneRoundStateCount
  ≡ initialInteractionStateCount * appraisalFibreStateCount
oneRoundFactorsAsBaseTimesFibre = refl

appraisalFibreFactorsByParticipant :
  appraisalFibreStateCount ≡ 27 * 27
appraisalFibreFactorsByParticipant = refl

oneRoundFactorsAsThreeCubes :
  oneRoundStateCount ≡ 27 * 27 * 27
oneRoundFactorsAsThreeCubes = refl

------------------------------------------------------------------------
-- Pointed phase expansion.
------------------------------------------------------------------------

record PointedPhaseParameters : Set where
  constructor pointedPhaseParameters
  field
    noncentralStateCount : Nat
    phasesPerNoncentralState : Nat
    attachedFibreSize : Nat

open PointedPhaseParameters public

phaseExpandedCarrierSize : PointedPhaseParameters → Nat
phaseExpandedCarrierSize parameters =
  noncentralStateCount parameters
  * phasesPerNoncentralState parameters
  + 1

pointedPhaseTotalSize : PointedPhaseParameters → Nat
pointedPhaseTotalSize parameters =
  phaseExpandedCarrierSize parameters * attachedFibreSize parameters

canonicalAppraisalPointedPhase : PointedPhaseParameters
canonicalAppraisalPointedPhase =
  pointedPhaseParameters 8 10 9

canonicalExpandedCarrierIs81 :
  phaseExpandedCarrierSize canonicalAppraisalPointedPhase ≡ 81
canonicalExpandedCarrierIs81 = refl

canonicalPointedPhaseTotalIs729 :
  pointedPhaseTotalSize canonicalAppraisalPointedPhase ≡ 729
canonicalPointedPhaseTotalIs729 = refl

fineSheetFamilySize : Nat
fineSheetFamilySize = 10 * 9

fineSheetFamilySizeIs90 : fineSheetFamilySize ≡ 90
fineSheetFamilySizeIs90 = refl

appraisalFibreAsEightFineFamiliesPlusCore :
  appraisalFibreStateCount ≡ 8 * fineSheetFamilySize + 9
appraisalFibreAsEightFineFamiliesPlusCore = refl

appraisalFibreAsTenEnrichedBlocksPlusCore :
  appraisalFibreStateCount ≡ 10 * (8 * 9) + 9
appraisalFibreAsTenEnrichedBlocksPlusCore = refl

appraisalFibreAsPointedExpansion :
  appraisalFibreStateCount ≡ (8 * 10 + 1) * 9
appraisalFibreAsPointedExpansion = refl

------------------------------------------------------------------------
-- Recursive relation to the C3 regular multiplicity.
------------------------------------------------------------------------

outerFineSurfaceSize : Nat
outerFineSurfaceSize = fineSheetFamilySize

recursiveFineCarrierSize : Nat
recursiveFineCarrierSize =
  outerFineSurfaceSize * appraisalFibreStateCount

recursiveFineCarrierSizeIs65610 : recursiveFineCarrierSize ≡ 65610
recursiveFineCarrierSizeIs65610 = refl

recursiveFineCarrierExpandedForm :
  recursiveFineCarrierSize
  ≡ (10 * 9) * (8 * (10 * 9) + 9)
recursiveFineCarrierExpandedForm = refl

------------------------------------------------------------------------
-- Explicit epistemic boundary.
------------------------------------------------------------------------

record RelationalPointedPhaseBoundary : Set where
  constructor relationalPointedPhaseBoundary
  field
    cardinalityArchitectureExact : Bool
    cardinalityArchitectureExactIsTrue :
      cardinalityArchitectureExact ≡ true

    pointedPartitionCanonicalForAllSixTritFibres : Bool
    pointedPartitionCanonicalForAllSixTritFibresIsFalse :
      pointedPartitionCanonicalForAllSixTritFibres ≡ false

    relationalConstructionDerivesTen : Bool
    relationalConstructionDerivesTenIsFalse :
      relationalConstructionDerivesTen ≡ false

    relationalCoordinatesConstructMonsterModule : Bool
    relationalCoordinatesConstructMonsterModuleIsFalse :
      relationalCoordinatesConstructMonsterModule ≡ false

    twelveRelationalAxesAreMonsterSymplecticQuotient : Bool
    twelveRelationalAxesAreMonsterSymplecticQuotientIsFalse :
      twelveRelationalAxesAreMonsterSymplecticQuotient ≡ false

    threePowerOnePlusTwelveIsOnlyGroupOrderPattern : Bool
    threePowerOnePlusTwelveIsOnlyGroupOrderPatternIsTrue :
      threePowerOnePlusTwelveIsOnlyGroupOrderPattern ≡ true

open RelationalPointedPhaseBoundary public

canonicalRelationalPointedPhaseBoundary : RelationalPointedPhaseBoundary
canonicalRelationalPointedPhaseBoundary =
  relationalPointedPhaseBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
    true refl
