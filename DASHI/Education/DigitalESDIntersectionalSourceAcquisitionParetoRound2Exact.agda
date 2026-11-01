module DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound2Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoExact as Round1

------------------------------------------------------------------------
-- ROUND 2: TARGET RESIDUALS LEFT WEAK AFTER THE FIRST INTERSECTIONAL FRONT.
--
-- Round 1 prioritised disabled/student situated voice, affordability/context,
-- co-design/support, stakeholder absence/incentives and school-meal continuity.
-- This round targets four remaining fibres:
--   * environmental lifecycle x global inequity;
--   * surveillance/security x poor/minoritized student incidence;
--   * remote delivery x disabled-child household care burden;
--   * vendor/accountability power x privacy/security governance.
--
-- These remain candidate acquisition sources, not the included review corpus.
------------------------------------------------------------------------

data Round2Residual : Set where
  lifecycleByGlobalInequity : Round2Residual
  surveillanceByMarginalizedIncidence : Round2Residual
  deliveryModeByDisabledHouseholdCareBurden : Round2Residual
  vendorPowerByPrivacyAccountability : Round2Residual

record Round2Candidate : Set where
  constructor round2-candidate
  field
    source : Attr.AttributedSource
    sourceRoleReceipt : Snowball.SourceRoleSnowballReceipt source
    qidDemand : Identity.ExternalIdentityDemand
    deweyState : String
    targetResidual : Round2Residual
    sourceBoundedReading : String
    limitation : String
    includedInFinalCorpus : Bool
    includedInFinalCorpusIsFalse : includedInFinalCorpus ≡ false

open Round2Candidate public

mkRound2Candidate :
  (source : Attr.AttributedSource) →
  Round2Residual →
  String →
  String →
  Round2Candidate
mkRound2Candidate source residual reading limitation =
  round2-candidate
    source
    (Snowball.canonicalSourceRoleSnowballReceipt source)
    (Identity.mkOptionalIdentityDemand
      "DigitalESDIntersectionalSourceAcquisitionParetoRound2Exact"
      (Attr.sourceTitle source)
      (Attr.sourceTitle source)
      Identity.wikidataQid
      (Identity.unresolved "no independently verified same-object article QID recorded by round 2"))
    "Dewey classification unresolved; no nearest-label substitution"
    residual
    reading
    limitation
    false refl

------------------------------------------------------------------------
-- Environmental lifecycle x global inequity.
------------------------------------------------------------------------

werseEcocriticalEdTechSource : Attr.AttributedSource
werseEcocriticalEdTechSource = Attr.mkDOISource
  "Nicholas Werse"
  "The quest to cultivate an ecocritical awareness in educational technology scholarship: A question of disciplinary focus in the age of environmental crisis"
  "British Journal of Educational Technology"
  "2023"
  "10.1111/bjet.13327"
  "https://doi.org/10.1111/bjet.13327"
  Attr.academicArticleSource
  "Conceptual ecocritical/ecojustice intervention arguing that educational-technology scholarship should attend to full device lifespans and global inequities in production and disposal, rather than environmental impact only at the point of educational use."
  Attr.publicAttribution

werseCandidate : Round2Candidate
werseCandidate = mkRound2Candidate
  werseEcocriticalEdTechSource
  lifecycleByGlobalInequity
  "High-alpha conceptual donor for environmental-material lifecycle x global-inequity questions that are weak in the current Digital-ESD candidate corpus."
  "Conceptual scholarship, not a same-object lifecycle inventory, worker/community study, or deployment measurement."

------------------------------------------------------------------------
-- Surveillance x poor/minoritized student incidence.
------------------------------------------------------------------------

sheikhStolbergGilmourSource : Attr.AttributedSource
sheikhStolbergGilmourSource = Attr.mkDOISource
  "Sidra Sheikh; Alexis Stolberg; Allison F. Gilmour"
  "Investigating Advanced School Surveillance Practices and Disproportionality: A Systematic Review"
  "Urban Education 60(9)"
  "2025"
  "10.1177/00420859241279446"
  "https://doi.org/10.1177/00420859241279446"
  Attr.academicArticleSource
  "Systematic review of 31 studies on advanced school surveillance, reporting concentrated surveillance-technology presence in schools serving predominantly poor and minoritized students and mixed perceived-safety effects."
  Attr.publicAttribution

sheikhCandidate : Round2Candidate
sheikhCandidate = mkRound2Candidate
  sheikhStolbergGilmourSource
  surveillanceByMarginalizedIncidence
  "Direct source candidate for privacy/security/surveillance x socioeconomic/racialized incidence, where aggregate security benefits cannot stand in for distributional effects."
  "Review scope and underlying study heterogeneity remain; does not establish a universal causal effect of any specific surveillance technology."

------------------------------------------------------------------------
-- Remote delivery x disabled-child household care burden.
------------------------------------------------------------------------

sankohEtAlSource : Attr.AttributedSource
sankohEtAlSource = Attr.mkDOISource
  "Alfred Sankoh; Jared Hogle; Melinda Payton; Karen Ledbetter"
  "Evaluating parental experiences in using technology for remote learning to teach students with special needs during the COVID-19 pandemic"
  "Frontiers in Education 8"
  "2023"
  "10.3389/feduc.2023.1053590"
  "https://doi.org/10.3389/feduc.2023.1053590"
  Attr.academicArticleSource
  "Phenomenological study of nine parents in two Manitoba school divisions describing parent-teacher burden, routines, behavioural/mental-health changes, insufficient home support and unmet desire for involvement in remote-learning planning for children with special needs."
  Attr.publicAttribution

sankohCandidate : Round2Candidate
sankohCandidate = mkRound2Candidate
  sankohEtAlSource
  deliveryModeByDisabledHouseholdCareBurden
  "Direct household-observer source for the audit fibre delivery mode x disability/support x shifted care/teaching burden."
  "Small parent sample and pandemic context; parent experience does not substitute for disabled students' own situated authority or establish universal remote-learning ineffectiveness."

------------------------------------------------------------------------
-- Vendor/accountability power x privacy/security governance.
------------------------------------------------------------------------

kelsoEtAlSource : Attr.AttributedSource
kelsoEtAlSource = Attr.mkDOISource
  "Easton Kelso; Ananta Soneji; Sazzadur Rahaman; Yan Shoshitaishvili; Rakibul Hasan"
  "Trust, Because You Can't Verify: Privacy and Security Hurdles in Education Technology Acquisition Practices"
  "Proceedings of the 2024 ACM SIGSAC Conference on Computer and Communications Security"
  "2024"
  "10.1145/3658644.3690353"
  "https://doi.org/10.1145/3658644.3690353"
  Attr.academicArticleSource
  "Semi-structured interviews with 13 EdTech leaders at seven higher-education institutions examining privacy/security acquisition practices, contract limitations, vendor visibility and power asymmetry."
  Attr.publicAttribution

kelsoCandidate : Round2Candidate
kelsoCandidate = mkRound2Candidate
  kelsoEtAlSource
  vendorPowerByPrivacyAccountability
  "Direct institutional-observer source for procurement/vendor-power x privacy/security/accountability, complementing participant-facing surveillance sources without collapsing the observer positions."
  "Leadership/procurement perspective; cannot create student consent, lived privacy impact, disability incidence or vendor misconduct findings not measured in the study."

canonicalRound2Frontier : List Round2Candidate
canonicalRound2Frontier =
  werseCandidate
  ∷ sheikhCandidate
  ∷ sankohCandidate
  ∷ kelsoCandidate
  ∷ []

------------------------------------------------------------------------
-- Cross-round discipline.
------------------------------------------------------------------------

round1RemainsIndependent : String
round1RemainsIndependent =
  "Round 2 extends the residual frontier exposed by Round 1; it does not replace Round 1 candidate identities, priorities, source roles or limitations."

data Round2CandidateCreatesIncludedStudy : Set where
data EcocriticalSourceCreatesDeploymentMeasurement : Set where
data SurveillanceReviewCreatesUniversalStudentEffect : Set where
data InstitutionalObserverCreatesParticipantAuthority : Set where
data ParentObserverCreatesDisabledStudentVoice : Set where

round2CandidateDoesNotCreateIncludedStudy : Round2CandidateCreatesIncludedStudy → ⊥
round2CandidateDoesNotCreateIncludedStudy ()

ecocriticalSourceDoesNotCreateDeploymentMeasurement :
  EcocriticalSourceCreatesDeploymentMeasurement → ⊥
ecocriticalSourceDoesNotCreateDeploymentMeasurement ()

surveillanceReviewDoesNotCreateUniversalStudentEffect :
  SurveillanceReviewCreatesUniversalStudentEffect → ⊥
surveillanceReviewDoesNotCreateUniversalStudentEffect ()

institutionalObserverDoesNotCreateParticipantAuthority :
  InstitutionalObserverCreatesParticipantAuthority → ⊥
institutionalObserverDoesNotCreateParticipantAuthority ()

parentObserverDoesNotCreateDisabledStudentVoice :
  ParentObserverCreatesDisabledStudentVoice → ⊥
parentObserverDoesNotCreateDisabledStudentVoice ()
