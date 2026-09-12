module DASHI.Governance.AustralianSenateAutismIntersectionalityRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Governance.AustralianSenateAutismIntersectionalityExact as AutismI
import DASHI.Governance.AustralianSenateAutismIntersectionalActionEvidenceExact as Action

------------------------------------------------------------------------
-- Regression surface: the autism inquiry intersectionality weld must reuse
-- existing situated/longitudinal/representation machinery without promoting
-- a finite cohort list into an exhaustive account of autistic people.
------------------------------------------------------------------------

cohortListNotExhaustive : AutismI.committeeCohortListExhaustive ≡ false
cohortListNotExhaustive = refl

singleAxisNotAdequate : AutismI.singleAxisAutomaticallyAdequate ≡ false
singleAxisNotAdequate = refl

strategyTextNotImplementation : AutismI.strategyIntersectionalityTextPaysImplementation ≡ false
strategyTextNotImplementation = refl

affectedPeopleRetainArticulation : AutismI.affectedConstituencyMayArticulateFurtherAxes ≡ true
affectedPeopleRetainArticulation = refl

recognitionNotDistribution : AutismI.recognitionAlonePaysDistribution ≡ false
recognitionNotDistribution = refl

representationNotDistribution : AutismI.representationAlonePaysDistribution ≡ false
representationNotDistribution = refl

longitudinalCarrierPresent : AutismI.autismIntersectionalLongitudinalCarrierExists ≡ true
longitudinalCarrierPresent = refl

consultationNotOutcome : Action.targetedConsultationPaysOutcome ≡ false
consultationNotOutcome = refl

peerSupportNotFullR18 : Action.peerSupportActionPaysAllRecommendation18 ≡ false
peerSupportNotFullR18 = refl

partialActionEvidencePaid : Action.someCohortSpecificActionEvidencePaid ≡ true
partialActionEvidencePaid = refl

lowerSESStillOpen : Action.lowerSocioeconomicActionPaymentOpen ≡ true
lowerSESStillOpen = refl

regionalServiceAccessStillOpen : Action.regionalRemoteServiceAccessPaymentOpen ≡ true
regionalServiceAccessStillOpen = refl

complexNeedsIntegratedSupportStillOpen : Action.complexNeedsIntegratedSupportPaymentOpen ≡ true
complexNeedsIntegratedSupportStillOpen = refl
