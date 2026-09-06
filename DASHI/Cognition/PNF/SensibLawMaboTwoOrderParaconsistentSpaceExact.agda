module DASHI.Cognition.PNF.SensibLawMaboTwoOrderParaconsistentSpaceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.RequiredAxisSupportSquareExact as Square
import DASHI.Algebra.ClaimIndexedEvidencePolarityExact as ClaimPolarity
import DASHI.Cognition.PNF.SensibLawMaboDawsonCrownDerivationHingeClosureExact as Dawson
import DASHI.Cognition.PNF.SensibLawMaboTwoLegalOrderFibreExact as TwoOrder

------------------------------------------------------------------------
-- Paraconsistent cross-order state.
--
-- Consumer-relative closure of Dawson's internal reasoning is only one axis.
-- It coexists with support for an opposing cross-order account and with axes
-- whose evidence remains missing.  Conflict is retained; it is not explosion,
-- ignorance, or automatic logical negation.
------------------------------------------------------------------------

data MaboParaconsistentAxis : Set where
  dawsonInternalReconstructionAxis
  crownExhaustiveSourceAxis
  indigenousOrderIndependenceAxis
  colonialLegitimacyAxis
  indigenousCessionAxis
  materialLandRepairAxis
  : MaboParaconsistentAxis

axisSupport : MaboParaconsistentAxis → Square.SupportSquare
axisSupport dawsonInternalReconstructionAxis = Square.supportSquare true false
axisSupport crownExhaustiveSourceAxis = Square.supportSquare true true
axisSupport indigenousOrderIndependenceAxis = Square.supportSquare true false
axisSupport colonialLegitimacyAxis = Square.supportSquare false false
axisSupport indigenousCessionAxis = Square.supportSquare false false
axisSupport materialLandRepairAxis = Square.supportSquare false true

axisState : MaboParaconsistentAxis → Square.SupportState
axisState axis = Square.supportState (axisSupport axis)

dawsonInternalStatePositiveOnly :
  axisState dawsonInternalReconstructionAxis ≡ Square.positiveOnly
dawsonInternalStatePositiveOnly = refl

crownExhaustiveSourceStateConflicting :
  axisState crownExhaustiveSourceAxis ≡ Square.conflictingState
crownExhaustiveSourceStateConflicting = refl

indigenousOrderIndependencePositiveOnly :
  axisState indigenousOrderIndependenceAxis ≡ Square.positiveOnly
indigenousOrderIndependencePositiveOnly = refl

colonialLegitimacyStillMissing :
  axisState colonialLegitimacyAxis ≡ Square.missingState
colonialLegitimacyStillMissing = refl

indigenousCessionStillMissing :
  axisState indigenousCessionAxis ≡ Square.missingState
indigenousCessionStillMissing = refl

materialRepairNotPaidByNativeTitleRecognition :
  axisState materialLandRepairAxis ≡ Square.negativeOnly
materialRepairNotPaidByNativeTitleRecognition = refl

------------------------------------------------------------------------
-- Provenance stays attached to each polarity coordinate.
------------------------------------------------------------------------

record AxisPolarityProvenance : Set where
  constructor axisPolarityProvenance
  field
    axis : MaboParaconsistentAxis
    baseClaim : String
    baseSupportProvenance : String
    opposingPosition : String
    opposingSupportProvenance : String
    opposingPositionIsAutomaticallyLogicalNegation : Bool
    opposingPositionIsAutomaticallyLogicalNegationIsFalse :
      opposingPositionIsAutomaticallyLogicalNegation ≡ false
    worldTruthAdjudicatedBySupportSquare : Bool
    worldTruthAdjudicatedBySupportSquareIsFalse :
      worldTruthAdjudicatedBySupportSquare ≡ false
open AxisPolarityProvenance public

dawsonInternalProvenance : AxisPolarityProvenance
dawsonInternalProvenance = axisPolarityProvenance
  dawsonInternalReconstructionAxis
  "Dawson's court-internal Crown-derivation reasoning can be reconstructed from the reviewed primary-judgment reproduction"
  "SensibLawMaboDawsonCrownDerivationHingeClosureExact: Crown sovereignty -> ultimate/radical title -> derivative rights -> Crown recognition choice"
  "Dawson's internal reconstruction cannot be reconstructed"
  "no opposing support entered on this narrow reconstruction consumer"
  false refl false refl

crownExhaustiveSourceProvenance : AxisPolarityProvenance
crownExhaustiveSourceProvenance = axisPolarityProvenance
  crownExhaustiveSourceAxis
  "Crown-derived municipal recognition exhausts the legally relevant source of continuing land rights"
  "Dawson court-internal derivation: land rights are mediated through Crown title/recognition within his municipal-law model"
  "antecedent Indigenous law/Country/community authority is not created or exhausted by Crown recognition"
  "SensibLawMaboTwoLegalOrderFibreExact independent Indigenous-order carrier and non-creation boundary"
  false refl false refl

indigenousOrderIndependenceProvenance : AxisPolarityProvenance
indigenousOrderIndependenceProvenance = axisPolarityProvenance
  indigenousOrderIndependenceAxis
  "the representation admits antecedent Indigenous law/Country/community authority independently of Crown recognition"
  "SensibLawMaboTwoLegalOrderFibreExact: courtDeterminesOrderExistence=false and externalRecognitionCreatesOrder=false"
  "the Crown court's recognition status is the originating source of Indigenous law/authority"
  "no support entered for this opposing representation proposition"
  false refl false refl

colonialLegitimacyProvenance : AxisPolarityProvenance
colonialLegitimacyProvenance = axisPolarityProvenance
  colonialLegitimacyAxis
  "colonial acquisition of sovereignty was legitimate"
  "no source-backed closure entered on this axis"
  "colonial acquisition of sovereignty was illegitimate"
  "critical/decolonial claims may be represented separately, but this support square does not silently convert them into an adjudicated historical/world-truth receipt"
  false refl false refl

indigenousCessionProvenance : AxisPolarityProvenance
indigenousCessionProvenance = axisPolarityProvenance
  indigenousCessionAxis
  "Indigenous sovereignty was ceded"
  "no source-backed closure entered on this axis"
  "Indigenous sovereignty was never ceded"
  "affected-community/decolonial proposition remains separately attributable; this owner does not manufacture source evidence from the formal model"
  false refl false refl

materialRepairProvenance : AxisPolarityProvenance
materialRepairProvenance = axisPolarityProvenance
  materialLandRepairAxis
  "native-title recognition by itself completes material land repair"
  "no positive support entered"
  "native-title recognition does not by itself complete land restitution/material repair"
  "existing SensibLaw repair-axis no-collapse theorems and contemporary material-efficacy receipts"
  false refl false refl

------------------------------------------------------------------------
-- Whole-space receipt: local closure and cross-order conflict coexist.
------------------------------------------------------------------------

record MaboParaconsistentSpace : Set where
  constructor maboParaconsistentSpace
  field
    dawsonInternal : Square.SupportState
    crownSourceExhaustiveness : Square.SupportState
    indigenousOrderIndependence : Square.SupportState
    colonialLegitimacy : Square.SupportState
    indigenousCession : Square.SupportState
    materialRepair : Square.SupportState
    internalClosureImpliesGlobalResolution : Bool
    internalClosureImpliesGlobalResolutionIsFalse : internalClosureImpliesGlobalResolution ≡ false
    conflictExplodesEveryAxis : Bool
    conflictExplodesEveryAxisIsFalse : conflictExplodesEveryAxis ≡ false
    spaceAdjudicatesWorldTruth : Bool
    spaceAdjudicatesWorldTruthIsFalse : spaceAdjudicatesWorldTruth ≡ false
open MaboParaconsistentSpace public

currentMaboParaconsistentSpace : MaboParaconsistentSpace
currentMaboParaconsistentSpace = maboParaconsistentSpace
  (axisState dawsonInternalReconstructionAxis)
  (axisState crownExhaustiveSourceAxis)
  (axisState indigenousOrderIndependenceAxis)
  (axisState colonialLegitimacyAxis)
  (axisState indigenousCessionAxis)
  (axisState materialLandRepairAxis)
  false refl false refl false refl

internalClosureCoexistsWithCrossOrderConflict :
  dawsonInternal currentMaboParaconsistentSpace ≡ Square.positiveOnly
  × crownSourceExhaustiveness currentMaboParaconsistentSpace ≡ Square.conflictingState
internalClosureCoexistsWithCrossOrderConflict = refl , refl

conflictCoexistsWithMissingLegitimacy :
  crownSourceExhaustiveness currentMaboParaconsistentSpace ≡ Square.conflictingState
  × colonialLegitimacy currentMaboParaconsistentSpace ≡ Square.missingState
conflictCoexistsWithMissingLegitimacy = refl , refl

------------------------------------------------------------------------
-- Cross-checks with source owners.
------------------------------------------------------------------------

dawsonNarrowConsumerReallyClosed :
  Dawson.consumerClosure Dawson.reconstructDawsonInternalLogic ≡ Dawson.consumerClosed
dawsonNarrowConsumerReallyClosed = refl

indigenousOrderNotCreatedByExternalRecognition :
  TwoOrder.externalRecognitionCreatesOrder TwoOrder.indigenousOrderFibre ≡ false
indigenousOrderNotCreatedByExternalRecognition = refl

opposingSupportNotAutomaticallyLogicalNegation :
  ClaimPolarity.opposingSupportAutomaticallyMeansLogicalNegation
    ClaimPolarity.canonicalClaimIndexedEvidencePolarityBoundary ≡ false
opposingSupportNotAutomaticallyLogicalNegation = refl

------------------------------------------------------------------------
-- No-collapse / non-explosion laws.
------------------------------------------------------------------------

data DawsonInternalClosureResolvesCrownSupremacyConflict : Set where
data CrownSupremacyConflictResolvesColonialLegitimacy : Set where
data ConflictingStateEqualsMissingState : Set where
data CrossOrderOppositionAutomaticallyClassicalNegation : Set where
data ParaconsistentSupportSquareAdjudicatesWorldTruth : Set where

dawsonInternalClosureDoesNotResolveSupremacyConflict :
  DawsonInternalClosureResolvesCrownSupremacyConflict → ⊥
dawsonInternalClosureDoesNotResolveSupremacyConflict ()

supremacyConflictDoesNotResolveColonialLegitimacy :
  CrownSupremacyConflictResolvesColonialLegitimacy → ⊥
supremacyConflictDoesNotResolveColonialLegitimacy ()

conflictIsNotMissing : ConflictingStateEqualsMissingState → ⊥
conflictIsNotMissing ()

crossOrderOppositionIsNotAutomaticallyNegation :
  CrossOrderOppositionAutomaticallyClassicalNegation → ⊥
crossOrderOppositionIsNotAutomaticallyNegation ()

supportSquareDoesNotAdjudicateWorldTruth :
  ParaconsistentSupportSquareAdjudicatesWorldTruth → ⊥
supportSquareDoesNotAdjudicateWorldTruth ()
