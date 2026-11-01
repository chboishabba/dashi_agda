module DASHI.Biology.AliceBrownDissentGovernanceCrossPollinationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.AliceBrownCorpusLoom as Alice
import DASHI.Biology.StudentVoiceEpistemicAgencyBridge as Voice
import DASHI.Governance.SituatedDissentDeceptionAssayExact as Dissent
import DASHI.Governance.OppositionInterfaceAntiDomesticationExact as Opposition

------------------------------------------------------------------------
-- ALICE BROWN -> DISSENT / GOVERNANCE CROSS-POLLINATION
--
-- Source attribution remains strict:
--
--   Brown/Kimber source-bound student-voice propositions
--   != generic DASHI dissent theorem
--   != empirical claim that every institution is coercive
--   != automatic authority for students over every downstream consumer.
--
-- The bridge consumes the existing voice/agency gate and the new governance
-- assay together: a feedback/consultation surface is insufficient when the
-- subject cannot contest framing, interpretation or downstream use; conversely,
-- participation does not automatically settle substantive justice.
------------------------------------------------------------------------

aliceCorpus : Alice.AliceBrownCorpusLoom
aliceCorpus = Alice.canonicalAliceBrownCorpusLoom

voiceBridge : Voice.StudentVoiceEpistemicAgencyBridge
voiceBridge = Voice.canonicalStudentVoiceEpistemicAgencyBridge

situatedDissentBoundary : Dissent.SituatedDissentDeceptionBoundary
situatedDissentBoundary = Dissent.canonicalSituatedDissentDeceptionBoundary

oppositionBoundary : Opposition.OppositionInterfaceAntiDomesticationBoundary
oppositionBoundary = Opposition.canonicalOppositionInterfaceAntiDomesticationBoundary

surveyStillDoesNotPromoteToVoice : Voice.SurveyNotVoice
surveyStillDoesNotPromoteToVoice = Voice.surveyNotVoiceProof

record AliceBrownDissentGovernanceBoundary : Set where
  constructor alice-brown-dissent-governance-boundary
  field
    feedbackSurfaceEqualsEpistemicAgency : Bool
    feedbackSurfaceEqualsEpistemicAgencyIsFalse :
      feedbackSurfaceEqualsEpistemicAgency ≡ false
    admittedVoiceEqualsMetaRulePower : Bool
    admittedVoiceEqualsMetaRulePowerIsFalse :
      admittedVoiceEqualsMetaRulePower ≡ false
    participationAutomaticallySettlesJustice : Bool
    participationAutomaticallySettlesJusticeIsFalse :
      participationAutomaticallySettlesJustice ≡ false
    aliceSourcePaperProvesGenericDissentTheorem : Bool
    aliceSourcePaperProvesGenericDissentTheoremIsFalse :
      aliceSourcePaperProvesGenericDissentTheorem ≡ false
    crossPollinationPreservesSourceFibres : Bool
    crossPollinationPreservesSourceFibresIsTrue :
      crossPollinationPreservesSourceFibres ≡ true

canonicalAliceBrownDissentGovernanceBoundary :
  AliceBrownDissentGovernanceBoundary
canonicalAliceBrownDissentGovernanceBoundary =
  alice-brown-dissent-governance-boundary
    false refl
    false refl
    false refl
    false refl
    true refl

reading : String
reading =
  "Student feedback, consultation and invitation remain distinct from epistemic agency. The governance cross-pollination adds a second distinction: even real admitted opposition does not automatically control the rule of admission. A strong dissent channel therefore requires both situated epistemic agency and materially effective contestability, while neither source paper nor finite DASHI witness settles substantive justice by itself."
