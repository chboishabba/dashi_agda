module DASHI.Cognition.PNF.SensibLawMaboDawsonCrownDerivationHingeClosureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMaboDawsonRadicalTitleRecognitionHingeExact as Hinge
import DASHI.Cognition.PNF.SensibLawMaboTwoLegalOrderFibreExact as TwoOrder

------------------------------------------------------------------------
-- Dawson Crown-derivation hinge closure.
--
-- Source: reviewed primary-judgment reproduction of Mabo (No 2), Dawson J.
-- The recovered passages state the court-internal sequence that ultimate/radical
-- title vested in the Crown on annexation; rights asserted by the plaintiffs
-- must, in Dawson's model, be held under the Crown; and pre-existing interests
-- continue municipally only insofar as the Crown chose to recognise them.
--
-- This is Dawson's derivation model. It is NOT promoted to Brennan's holding,
-- the majority rule, legitimate sovereignty, Indigenous cession or world truth.
------------------------------------------------------------------------

data PrimaryReproductionQuality : Set where
  reviewedPrimaryJudgmentReproduction : PrimaryReproductionQuality
  officialCourtTranscriptionNotYetWelded : PrimaryReproductionQuality


data DawsonDerivationPremiseKind : Set where
  annexationVestsUltimateTitleInCrown : DawsonDerivationPremiseKind
  radicalTitleMakesCrownParamountMunicipalSource : DawsonDerivationPremiseKind
  plaintiffsRightsMustBeHeldUnderCrown : DawsonDerivationPremiseKind
  preExistingInterestsRetainedOnlyIfCrownRecognises : DawsonDerivationPremiseKind
  recognitionMediatesContinuingMunicipalEffect : DawsonDerivationPremiseKind


record DawsonPrimaryDerivationPremise : Set where
  constructor dawsonPrimaryDerivationPremise
  field
    premise : DawsonDerivationPremiseKind
    sourceReference : String
    sourceQuality : PrimaryReproductionQuality
    reviewedSummary : String
    attributedToDawson : Bool
    attributedToDawsonIsTrue : attributedToDawson ≡ true
    majorityHoldingClaimed : Bool
    majorityHoldingClaimedIsFalse : majorityHoldingClaimed ≡ false
    legitimateSovereigntyClaimed : Bool
    legitimateSovereigntyClaimedIsFalse : legitimateSovereigntyClaimed ≡ false
open DawsonPrimaryDerivationPremise public

annexationUltimateTitlePremise : DawsonPrimaryDerivationPremise
annexationUltimateTitlePremise = dawsonPrimaryDerivationPremise
  annexationVestsUltimateTitleInCrown
  "Mabo v Queensland [No 2] (1992) 175 CLR 1, Dawson J, reviewed ALOR judgment reproduction; ultimate/radical-title discussion"
  reviewedPrimaryJudgmentReproduction
  "Dawson treats vesting of ultimate/radical title in the Crown on annexation as a necessary consequence of Crown sovereignty under the common-law land system he applies"
  true refl false refl false refl

heldUnderCrownPremise : DawsonPrimaryDerivationPremise
heldUnderCrownPremise = dawsonPrimaryDerivationPremise
  plaintiffsRightsMustBeHeldUnderCrown
  "Mabo v Queensland [No 2] (1992) 175 CLR 1, Dawson J, reviewed ALOR judgment reproduction; radical-title discussion"
  reviewedPrimaryJudgmentReproduction
  "Dawson's court-internal model states that, once annexed land became Crown property, rights asserted by the plaintiffs in that land must be held under the Crown and be less than absolute ownership"
  true refl false refl false refl

crownChoiceRecognitionPremise : DawsonPrimaryDerivationPremise
crownChoiceRecognitionPremise = dawsonPrimaryDerivationPremise
  preExistingInterestsRetainedOnlyIfCrownRecognises
  "Mabo v Queensland [No 2] (1992) 175 CLR 1, Dawson J, reviewed ALOR judgment reproduction; possessory-title discussion"
  reviewedPrimaryJudgmentReproduction
  "Dawson states, in rejecting the possessory-title route, that after Crown sovereignty the plaintiffs could retain only such interests as the Crown chose to recognise by one means or another"
  true refl false refl false refl

recognitionMediationPremise : DawsonPrimaryDerivationPremise
recognitionMediationPremise = dawsonPrimaryDerivationPremise
  recognitionMediatesContinuingMunicipalEffect
  "Dawson derivation synthesis over the two reviewed primary passages; synthesis is DASHI/SensibLaw, not a new quotation"
  reviewedPrimaryJudgmentReproduction
  "reviewed synthesis: Crown radical/ultimate title plus the proposition that rights must be held under the Crown supplies Dawson's missing mediation premise linking antecedent interests to Crown recognition for municipal legal effect"
  true refl false refl false refl

------------------------------------------------------------------------
-- The formerly unresolved hinge can now close FOR THE DAWSON-MODEL CONSUMER.
-- This does not close broader doctrine or validate the premise outside that model.
------------------------------------------------------------------------

data DawsonHingeConsumer : Set where
  reconstructDawsonInternalLogic : DawsonHingeConsumer
  determineMajorityNativeTitleRule : DawsonHingeConsumer
  evaluateColonialLegitimacy : DawsonHingeConsumer
  compareIndependentIndigenousLegalOrder : DawsonHingeConsumer


data ConsumerClosure : Set where
  consumerClosed : ConsumerClosure
  consumerOpen : ConsumerClosure
  consumerCriticalConflictLocated : ConsumerClosure


consumerClosure : DawsonHingeConsumer → ConsumerClosure
consumerClosure reconstructDawsonInternalLogic = consumerClosed
consumerClosure determineMajorityNativeTitleRule = consumerOpen
consumerClosure evaluateColonialLegitimacy = consumerOpen
consumerClosure compareIndependentIndigenousLegalOrder = consumerCriticalConflictLocated

dawsonInternalHingeNowClosed :
  consumerClosure reconstructDawsonInternalLogic ≡ consumerClosed
dawsonInternalHingeNowClosed = refl

majorityRuleStillNotClosedByDawson :
  consumerClosure determineMajorityNativeTitleRule ≡ consumerOpen
majorityRuleStillNotClosedByDawson = refl

------------------------------------------------------------------------
-- Exact recovered chain.
------------------------------------------------------------------------

data DawsonCrownDerivationNode : Set where
  crownSovereigntyNode : DawsonCrownDerivationNode
  crownUltimateRadicalTitleNode : DawsonCrownDerivationNode
  crownDerivativeRightsNode : DawsonCrownDerivationNode
  crownRecognitionChoiceNode : DawsonCrownDerivationNode
  continuingMunicipalEffectNode : DawsonCrownDerivationNode


nextNode : DawsonCrownDerivationNode → DawsonCrownDerivationNode
nextNode crownSovereigntyNode = crownUltimateRadicalTitleNode
nextNode crownUltimateRadicalTitleNode = crownDerivativeRightsNode
nextNode crownDerivativeRightsNode = crownRecognitionChoiceNode
nextNode crownRecognitionChoiceNode = continuingMunicipalEffectNode
nextNode continuingMunicipalEffectNode = continuingMunicipalEffectNode

radicalTitleNowHasDawsonIntermediateNode :
  nextNode crownUltimateRadicalTitleNode ≡ crownDerivativeRightsNode
radicalTitleNowHasDawsonIntermediateNode = refl

derivativeRightsLeadToRecognitionChoice :
  nextNode crownDerivativeRightsNode ≡ crownRecognitionChoiceNode
derivativeRightsLeadToRecognitionChoice = refl

------------------------------------------------------------------------
-- Cross-pollination with two-order architecture.
------------------------------------------------------------------------

data DerivationModelConflictKind : Set where
  crownDerivativeSourceModel : DerivationModelConflictKind
  antecedentIndependentIndigenousSourceModel : DerivationModelConflictKind


record TwoOrderDerivationConflict : Set where
  constructor twoOrderDerivationConflict
  field
    dawsonModel : DerivationModelConflictKind
    indigenousOrderModel : DerivationModelConflictKind
    crownRecognitionCreatesIndigenousOrder : Bool
    crownRecognitionCreatesIndigenousOrderIsFalse : crownRecognitionCreatesIndigenousOrder ≡ false
    municipalEffectProvesGlobalSourceSupremacy : Bool
    municipalEffectProvesGlobalSourceSupremacyIsFalse : municipalEffectProvesGlobalSourceSupremacy ≡ false
    conflictReference : String
open TwoOrderDerivationConflict public

canonicalDerivationConflict : TwoOrderDerivationConflict
canonicalDerivationConflict = twoOrderDerivationConflict
  crownDerivativeSourceModel
  antecedentIndependentIndigenousSourceModel
  false refl
  false refl
  "Dawson's municipal derivation model makes continuing legal effect depend on Crown recognition; the two-order carrier independently represents Indigenous law/Country relation as antecedent and not created by Crown recognition"

indigenousOrderStillNotCreatedByRecognition :
  TwoOrder.externalRecognitionCreatesOrder TwoOrder.indigenousOrderFibre ≡ false
indigenousOrderStillNotCreatedByRecognition = refl

------------------------------------------------------------------------
-- Historical hinge object remains an audit artefact: its unresolved status was
-- correct before these additional primary passages were recovered.
------------------------------------------------------------------------

historicalHingeWasUnresolved :
  Hinge.sourceStatus Hinge.radicalTitleRecognitionMediationCandidate ≡ Hinge.unresolvedBridge
historicalHingeWasUnresolved = refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data DawsonInternalClosureEqualsMajorityHolding : Set where
data DawsonPremiseProvesCrownSovereigntyLegitimate : Set where
data MunicipalDerivationErasesIndigenousSourceOrder : Set where
data PrimaryReproductionEqualsOfficialCourtTranscription : Set where

dawsonClosureDoesNotBecomeMajorityHolding : DawsonInternalClosureEqualsMajorityHolding → ⊥
dawsonClosureDoesNotBecomeMajorityHolding ()
dawsonPremiseDoesNotProveLegitimacy : DawsonPremiseProvesCrownSovereigntyLegitimate → ⊥
dawsonPremiseDoesNotProveLegitimacy ()
municipalDerivationDoesNotEraseIndigenousOrder : MunicipalDerivationErasesIndigenousSourceOrder → ⊥
municipalDerivationDoesNotEraseIndigenousOrder ()
reproductionDoesNotBecomeOfficialTranscription : PrimaryReproductionEqualsOfficialCourtTranscription → ⊥
reproductionDoesNotBecomeOfficialTranscription ()
