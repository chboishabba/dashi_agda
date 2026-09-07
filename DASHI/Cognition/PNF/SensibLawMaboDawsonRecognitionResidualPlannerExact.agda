module DASHI.Cognition.PNF.SensibLawMaboDawsonRecognitionResidualPlannerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMaboMinimalDoctrinalDiscriminatorExact as Minimal
import DASHI.Cognition.PNF.SensibLawMaboMinimalDoctrinalCutsetExact as Cutset
import DASHI.Cognition.PNF.SensibLawMaboDawsonRecognitionConditionRefinementExact as Dawson
import DASHI.Cognition.PNF.SensibLawMaboMinimalDoctrinalHyperfabricBridgeExact as Hyper
import DASHI.Cognition.PNF.SensibLawIssueIndexedAdjudicativeHyperfabricExact as Issue

------------------------------------------------------------------------
-- The current first live residual for unified recognition theory is the
-- recognition-condition fibre.  This planner decomposes that residual into
-- targeted proposition-level probes rather than asking for more generic
-- recognition evidence.
------------------------------------------------------------------------

data DawsonRecognitionProbe : Set where
  inspectDawsonCrownDerivationPremise : DawsonRecognitionProbe
  inspectDawsonRecognitionAcceptanceRule : DawsonRecognitionProbe
  inspectDawsonNoPresumptionRule : DawsonRecognitionProbe
  inspectDawsonFactSpecificRecognitionRule : DawsonRecognitionProbe
  inspectDawsonAcquiescenceEvidence : DawsonRecognitionProbe
  compareDawsonWithVerifiedHallRecognitionIndependence : DawsonRecognitionProbe
  compareDawsonWithAmoduContinuity : DawsonRecognitionProbe
  inspectCalderJudsonOnlyIfStillNeeded : DawsonRecognitionProbe


data ProbeRole : Set where
  conditionRuleProbe : ProbeRole
  evidenceProbe : ProbeRole
  crossAuthorityComparisonProbe : ProbeRole
  contingentAuthorityInterpretationProbe : ProbeRole


probeRole : DawsonRecognitionProbe → ProbeRole
probeRole inspectDawsonCrownDerivationPremise = conditionRuleProbe
probeRole inspectDawsonRecognitionAcceptanceRule = conditionRuleProbe
probeRole inspectDawsonNoPresumptionRule = conditionRuleProbe
probeRole inspectDawsonFactSpecificRecognitionRule = conditionRuleProbe
probeRole inspectDawsonAcquiescenceEvidence = evidenceProbe
probeRole compareDawsonWithVerifiedHallRecognitionIndependence = crossAuthorityComparisonProbe
probeRole compareDawsonWithAmoduContinuity = crossAuthorityComparisonProbe
probeRole inspectCalderJudsonOnlyIfStillNeeded = contingentAuthorityInterpretationProbe

record DawsonRecognitionResidualPlan : Set where
  constructor dawsonRecognitionResidualPlan
  field
    query : Minimal.MinimalDoctrinalQuery
    firstResidual : Cutset.MinimalDoctrinalResidual
    firstResidualExact : firstResidual ≡ Cutset.recognitionConditionResidual
    hyperfabricObligation : Hyper.MinimalProofObligation
    hyperfabricObligationExact : hyperfabricObligation ≡ Hyper.establishRecognitionConditionRule
    primaryProbes : List DawsonRecognitionProbe
    excludedAsPrimaryProbe : DawsonRecognitionProbe
    parserRerunRequired : Bool
    parserRerunRequiredIsFalse : parserRerunRequired ≡ false
    judsonRequiredNow : Bool
    judsonRequiredNowIsFalse : judsonRequiredNow ≡ false
    workKind : Issue.EpistemicWorkKind
    workKindExact : workKind ≡ Issue.lookWork
    planReference : String
open DawsonRecognitionResidualPlan public

currentDawsonRecognitionPlan : DawsonRecognitionResidualPlan
currentDawsonRecognitionPlan = dawsonRecognitionResidualPlan
  Minimal.identifyUnifiedRecognitionTheory
  (Cutset.firstResidual Minimal.identifyUnifiedRecognitionTheory Cutset.postHallVerificationCutset)
  refl
  (Hyper.obligation Hyper.recognitionConditionHyperfabric)
  refl
  (inspectDawsonCrownDerivationPremise
    ∷ inspectDawsonRecognitionAcceptanceRule
    ∷ inspectDawsonNoPresumptionRule
    ∷ inspectDawsonFactSpecificRecognitionRule
    ∷ compareDawsonWithVerifiedHallRecognitionIndependence
    ∷ compareDawsonWithAmoduContinuity
    ∷ [])
  inspectDawsonAcquiescenceEvidence
  false refl
  false refl
  Issue.lookWork refl
  "unified Mabo theory currently stops at recognition-condition; inspect Dawson's juridical rule and cross-authority contrasts before spending more work on recognition evidence or Judson"

------------------------------------------------------------------------
-- Why acquiescence is deliberately excluded from the primary condition probe.
------------------------------------------------------------------------

acquiescenceRoleIsEvidence :
  Dawson.componentRole Dawson.acquiescenceAsRecognitionEvidence ≡ Dawson.evidenceModeRole
acquiescenceRoleIsEvidence = refl

recognitionConditionRoleIsJuridical :
  Dawson.componentRole Dawson.newSovereignRecognitionOrAcceptanceCondition ≡ Dawson.juridicalConditionRole
recognitionConditionRoleIsJuridical = refl

currentUnifiedResidualIsRecognitionCondition :
  Cutset.firstResidual Minimal.identifyUnifiedRecognitionTheory Cutset.postHallVerificationCutset
  ≡ Cutset.recognitionConditionResidual
currentUnifiedResidualIsRecognitionCondition = refl

currentRecognitionConditionUsesAuthorityWork :
  Hyper.workKind Hyper.recognitionConditionHyperfabric ≡ Issue.lookWork
currentRecognitionConditionUsesAuthorityWork = refl

------------------------------------------------------------------------
-- Judson is now a contingent probe rather than an automatic blocker.
------------------------------------------------------------------------

record JudsonContingencyBoundary : Set where
  constructor judsonContingencyBoundary
  field
    hallAuthoritativeVerificationAvailable : Bool
    hallAuthoritativeVerificationAvailableIsTrue : hallAuthoritativeVerificationAvailable ≡ true
    dawsonConditionStillOpen : Bool
    dawsonConditionStillOpenIsTrue : dawsonConditionStillOpen ≡ true
    judsonRequiredBeforeDawsonRuleInspection : Bool
    judsonRequiredBeforeDawsonRuleInspectionIsFalse : judsonRequiredBeforeDawsonRuleInspection ≡ false
    judsonMayBecomeRelevantToAuthorityInterpretation : Bool
    judsonMayBecomeRelevantToAuthorityInterpretationIsTrue : judsonMayBecomeRelevantToAuthorityInterpretation ≡ true
open JudsonContingencyBoundary public

canonicalJudsonContingency : JudsonContingencyBoundary
canonicalJudsonContingency = judsonContingencyBoundary
  true refl true refl false refl true refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data MoreRecognitionEvidenceClosesRecognitionCondition : Set where
data JudsonMustBeResolvedBeforeInspectingDawsonRule : Set where
data NoGeneralPresumptionMeansNoLegalCondition : Set where
data ConditionRuleMeansRecognitionCreatedAntecedentRight : Set where

evidenceDoesNotCloseConditionByItself : MoreRecognitionEvidenceClosesRecognitionCondition → ⊥
evidenceDoesNotCloseConditionByItself ()
judsonIsNotCurrentPrecondition : JudsonMustBeResolvedBeforeInspectingDawsonRule → ⊥
judsonIsNotCurrentPrecondition ()
noPresumptionDoesNotEraseCondition : NoGeneralPresumptionMeansNoLegalCondition → ⊥
noPresumptionDoesNotEraseCondition ()
conditionRuleDoesNotMeanRightCreation : ConditionRuleMeansRecognitionCreatedAntecedentRight → ⊥
conditionRuleDoesNotMeanRightCreation ()
