module DASHI.Cognition.PNF.SensibLawMaboTwoLegalOrderFibreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMaboCriticalTheoryMaterialJusticeExact as Material
import DASHI.Cognition.PNF.SensibLawMaboColonialSovereigntyCriticalResidualExact as Critical
import DASHI.Cognition.PNF.SensibLawMaboMinimalDoctrinalDiscriminatorExact as Minimal

------------------------------------------------------------------------
-- Two-legal-order fibre.
--
-- This owner prevents Indigenous law/authority from being represented merely as
-- evidence fed into a Crown-owned legal universe.  The two orders have distinct
-- carriers, internal relations and cross-order interfaces.
------------------------------------------------------------------------

data LegalOrderKind : Set where
  crownMunicipalLegalOrder : LegalOrderKind
  indigenousNormativeLegalOrder : LegalOrderKind


data CrownOrderNode : Set where
  crownSovereigntyPremise : CrownOrderNode
  crownSovereigntyNonJusticiability : CrownOrderNode
  crownRadicalTitle : CrownOrderNode
  crownRecognitionCondition : CrownOrderNode
  crownExtinguishmentPower : CrownOrderNode
  crownRemedyPower : CrownOrderNode


data IndigenousOrderNode : Set where
  antecedentIndigenousLaw : IndigenousOrderNode
  indigenousSovereignty : IndigenousOrderNode
  countryLandRelation : IndigenousOrderNode
  communityAuthority : IndigenousOrderNode
  reciprocalCountryObligations : IndigenousOrderNode
  intergenerationalContinuity : IndigenousOrderNode


data CrossOrderRelation : Set where
  crownRecognitionOfIndigenousInterest : CrossOrderRelation
  crownNonRecognition : CrossOrderRelation
  partialAccommodation : CrossOrderRelation
  translationAcrossOrders : CrossOrderRelation
  conflictAcrossOrders : CrossOrderRelation
  externalisationByCourt : CrossOrderRelation
  coexistenceWithoutCollapse : CrossOrderRelation


record LegalOrderFibre : Set where
  constructor legalOrderFibre
  field
    order : LegalOrderKind
    orderReference : String
    selfSourceReference : String
    courtDeterminesOrderExistence : Bool
    courtDeterminesOrderExistenceIsFalse : courtDeterminesOrderExistence ≡ false
    externalRecognitionCreatesOrder : Bool
    externalRecognitionCreatesOrderIsFalse : externalRecognitionCreatesOrder ≡ false
open LegalOrderFibre public

crownOrderFibre : LegalOrderFibre
crownOrderFibre = legalOrderFibre
  crownMunicipalLegalOrder
  "Australian Crown municipal legal order"
  "Australian-law constitutional/common-law source structure"
  false refl
  false refl

indigenousOrderFibre : LegalOrderFibre
indigenousOrderFibre = legalOrderFibre
  indigenousNormativeLegalOrder
  "antecedent Indigenous law / sovereignty / Country relation"
  "affected-community law, custom, authority and Country source receipts; not created by Crown recognition"
  false refl
  false refl

------------------------------------------------------------------------
-- Court-internal chain.  This is a representation of the court's own legal
-- architecture, not a cross-frame theorem of legitimacy.
------------------------------------------------------------------------

data CrownInternalBridgeStatus : Set where
  reviewedCourtInternalBridge : CrownInternalBridgeStatus
  contestedCourtInternalBridge : CrownInternalBridgeStatus
  unresolvedCourtInternalBridge : CrownInternalBridgeStatus


record CrownInternalMediation : Set where
  constructor crownInternalMediation
  field
    source : CrownOrderNode
    target : CrownOrderNode
    status : CrownInternalBridgeStatus
    sourceReference : String
    courtInternalOnly : Bool
    courtInternalOnlyIsTrue : courtInternalOnly ≡ true
    provesColonialLegitimacy : Bool
    provesColonialLegitimacyIsFalse : provesColonialLegitimacy ≡ false
open CrownInternalMediation public

sovereigntyToRadicalTitle : CrownInternalMediation
sovereigntyToRadicalTitle = crownInternalMediation
  crownSovereigntyPremise
  crownRadicalTitle
  reviewedCourtInternalBridge
  "Mabo Crown-sovereignty premise -> radical-title consequences inside Australian municipal law"
  true refl false refl

radicalTitleToRecognitionCondition : CrownInternalMediation
radicalTitleToRecognitionCondition = crownInternalMediation
  crownRadicalTitle
  crownRecognitionCondition
  contestedCourtInternalBridge
  "live Dawson/Brennan discriminator: whether Crown radical title mediates continuing Indigenous interests through Crown recognition/acceptance"
  true refl false refl

radicalTitleToExtinguishmentPower : CrownInternalMediation
radicalTitleToExtinguishmentPower = crownInternalMediation
  crownRadicalTitle
  crownExtinguishmentPower
  reviewedCourtInternalBridge
  "court-internal extinguishment architecture downstream of radical title; scope and conditions remain issue-specific"
  true refl false refl

------------------------------------------------------------------------
-- Indigenous-order chain remains independently typed.
------------------------------------------------------------------------

record IndigenousOrderRelation : Set where
  constructor indigenousOrderRelation
  field
    source : IndigenousOrderNode
    target : IndigenousOrderNode
    sourceReference : String
    crownRecognitionRequiredForRelationToExist : Bool
    crownRecognitionRequiredForRelationToExistIsFalse : crownRecognitionRequiredForRelationToExist ≡ false
    courtHoldingAutomaticallyDeterminesRelation : Bool
    courtHoldingAutomaticallyDeterminesRelationIsFalse : courtHoldingAutomaticallyDeterminesRelation ≡ false
open IndigenousOrderRelation public

lawToCountryRelation : IndigenousOrderRelation
lawToCountryRelation = indigenousOrderRelation
  antecedentIndigenousLaw
  countryLandRelation
  "Indigenous law/custom -> Country/land relation; affected-community source receipt required"
  false refl false refl

countryToCommunityAuthority : IndigenousOrderRelation
countryToCommunityAuthority = indigenousOrderRelation
  countryLandRelation
  communityAuthority
  "Country/land relation -> community authority/obligation; not generated by Crown recognition"
  false refl false refl

sovereigntyToIntergenerationalContinuity : IndigenousOrderRelation
sovereigntyToIntergenerationalContinuity = indigenousOrderRelation
  indigenousSovereignty
  intergenerationalContinuity
  "Indigenous sovereignty/authority continuity claim remains independently sourced and contestable across frames"
  false refl false refl

------------------------------------------------------------------------
-- Cross-order interfaces are relations, not hierarchy declarations.
------------------------------------------------------------------------

record CrossOrderInterface : Set where
  constructor crossOrderInterface
  field
    crownNode : CrownOrderNode
    indigenousNode : IndigenousOrderNode
    relation : CrossOrderRelation
    interfaceReference : String
    crownOrderGloballySupreme : Bool
    crownOrderGloballySupremeIsFalse : crownOrderGloballySupreme ≡ false
    indigenousOrderReducedToFactInput : Bool
    indigenousOrderReducedToFactInputIsFalse : indigenousOrderReducedToFactInput ≡ false
    crossOrderTranslationExhaustive : Bool
    crossOrderTranslationExhaustiveIsFalse : crossOrderTranslationExhaustive ≡ false
open CrossOrderInterface public

nativeTitleRecognitionInterface : CrossOrderInterface
nativeTitleRecognitionInterface = crossOrderInterface
  crownRecognitionCondition
  countryLandRelation
  crownRecognitionOfIndigenousInterest
  "Native Title recognition interface: Crown law may recognise/protect an Indigenous land relation without creating or exhausting the antecedent Indigenous legal order"
  false refl false refl false refl

sovereigntyExternalisationInterface : CrossOrderInterface
sovereigntyExternalisationInterface = crossOrderInterface
  crownSovereigntyNonJusticiability
  indigenousSovereignty
  externalisationByCourt
  "municipal court treats acquisition of Crown sovereignty as non-justiciable while Indigenous sovereignty/cession remains outside that adjudicated merits fibre"
  false refl false refl false refl

------------------------------------------------------------------------
-- Two-order consumer state.
------------------------------------------------------------------------

data TwoOrderQuestion : Set where
  explainCourtInternalRecognition : TwoOrderQuestion
  explainIndigenousSourceOfRight : TwoOrderQuestion
  compareSovereigntyClaims : TwoOrderQuestion
  assessMaterialLandRepair : TwoOrderQuestion
  reconcileOrdersWithoutCollapse : TwoOrderQuestion


data TwoOrderResidual : Set where
  crownRecognitionMediationResidual : TwoOrderResidual
  indigenousSourceResidual : TwoOrderResidual
  sovereigntyCrossFrameResidual : TwoOrderResidual
  materialLandRepairResidual : TwoOrderResidual
  crossOrderReconciliationResidual : TwoOrderResidual
  twoOrderClosed : TwoOrderResidual


firstResidual : TwoOrderQuestion → TwoOrderResidual
firstResidual explainCourtInternalRecognition = crownRecognitionMediationResidual
firstResidual explainIndigenousSourceOfRight = indigenousSourceResidual
firstResidual compareSovereigntyClaims = sovereigntyCrossFrameResidual
firstResidual assessMaterialLandRepair = materialLandRepairResidual
firstResidual reconcileOrdersWithoutCollapse = sovereigntyCrossFrameResidual

courtRecognitionQueryDoesNotBecomeSovereigntyQuery :
  firstResidual explainCourtInternalRecognition ≡ crownRecognitionMediationResidual
courtRecognitionQueryDoesNotBecomeSovereigntyQuery = refl

indigenousSourceQueryRemainsIndependent :
  firstResidual explainIndigenousSourceOfRight ≡ indigenousSourceResidual
indigenousSourceQueryRemainsIndependent = refl

------------------------------------------------------------------------
-- Cross-pollination with the existing critical/material layers.
------------------------------------------------------------------------

maboCourtSovereigntyStillNonJusticiable :
  Material.acquisitionOfCrownSovereigntyJusticiable Material.maboSovereigntyJusticiability ≡ false
maboCourtSovereigntyStillNonJusticiable = refl

municipalConsequencesRemainJusticiable :
  Material.municipalConsequencesJusticiable Material.maboSovereigntyJusticiability ≡ true
municipalConsequencesRemainJusticiable = refl

nativeTitleStillDoesNotCloseSovereigntyRecognition :
  Critical.NativeTitleRecognitionProvesSovereigntyRecognition → ⊥
nativeTitleStillDoesNotCloseSovereigntyRecognition = Critical.nativeTitleDoesNotProveSovereigntyRecognition

recognitionConditionStillDistinctFromContinuity :
  Minimal.axis Minimal.dawsonRecognitionConditionReceipt ≡ Minimal.recognitionConditionAxis
recognitionConditionStillDistinctFromContinuity = refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data CrownOrderContainsIndigenousOrder : Set where
data CrownRecognitionCreatesIndigenousLaw : Set where
data CrownNonJusticiabilitySettlesIndigenousSovereignty : Set where
data RadicalTitleProvesRecognitionCondition : Set where
data CrossOrderTranslationMeansSemanticIdentity : Set where
data MunicipalLegalEffectProvesLegitimateSovereigntyTransfer : Set where

aCrownOrderDoesNotContainIndigenousOrder : CrownOrderContainsIndigenousOrder → ⊥
aCrownOrderDoesNotContainIndigenousOrder ()
recognitionDoesNotCreateIndigenousLaw : CrownRecognitionCreatesIndigenousLaw → ⊥
recognitionDoesNotCreateIndigenousLaw ()
nonJusticiabilityDoesNotSettleIndigenousSovereignty : CrownNonJusticiabilitySettlesIndigenousSovereignty → ⊥
nonJusticiabilityDoesNotSettleIndigenousSovereignty ()
radicalTitleDoesNotByItselfProveDawsonCondition : RadicalTitleProvesRecognitionCondition → ⊥
radicalTitleDoesNotByItselfProveDawsonCondition ()
translationDoesNotMeanIdentity : CrossOrderTranslationMeansSemanticIdentity → ⊥
translationDoesNotMeanIdentity ()
municipalEffectDoesNotProveLegitimateTransfer : MunicipalLegalEffectProvesLegitimateSovereigntyTransfer → ⊥
municipalEffectDoesNotProveLegitimateTransfer ()
