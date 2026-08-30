module DASHI.Governance.WitchTrialEvidenceSubjectAttributionExact where

------------------------------------------------------------------------
-- WITCH-TRIAL EVIDENCE / SUBJECT-ATTRIBUTION NONCOLLAPSE
--
-- Historical calibration:
-- Massachusetts Archives, Salem Witch Trials digital collection: spectral
-- evidence was vision/apparition testimony, difficult to rebut, and conviction
-- rates fell sharply after it was excluded from the later trials.
--
-- Source role: evidentiary-history calibration only.  The finite witnesses below
-- are DASHI constructions and do not reconstruct any individual Salem case.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.RepresentationSubjectPositionNonfactorabilityExact as Subject

record WitchTrialSourceReceipt : Set where
  constructor witch-trial-source-receipt
  field
    institutionAuthor : String
    title : String
    identifier : String
    boundedRole : String

massachusettsArchiveReceipt : WitchTrialSourceReceipt
massachusettsArchiveReceipt =
  witch-trial-source-receipt
    "Massachusetts Archives / Secretary of the Commonwealth"
    "The Trials - Salem Witch Trials digital collection"
    "official digital archive; no DOI asserted"
    "supports the historical role and controversy of spectral evidence; does not prove any accused person practised witchcraft"

------------------------------------------------------------------------
-- Report surface != mechanism != agent identity.
------------------------------------------------------------------------

data FineSpectralState : Set where
  endogenousExperience externallyCausedExperience : FineSpectralState

data SpectralReportSurface : Set where
  sameApparitionReport : SpectralReportSurface

data CausalMechanismClass : Set where
  internalOrUnresolvedMechanism identifiedExternalMechanism : CausalMechanismClass

spectralReport : FineSpectralState → SpectralReportSurface
spectralReport endogenousExperience = sameApparitionReport
spectralReport externallyCausedExperience = sameApparitionReport

causalMechanism : FineSpectralState → CausalMechanismClass
causalMechanism endogenousExperience = internalOrUnresolvedMechanism
causalMechanism externallyCausedExperience = identifiedExternalMechanism

mechanismsDistinct :
  causalMechanism endogenousExperience
  ≡ causalMechanism externallyCausedExperience → ⊥
mechanismsDistinct ()

spectralReportCannotRecoverMechanism :
  INF.FactorsThrough spectralReport causalMechanism → ⊥
spectralReportCannotRecoverMechanism =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      endogenousExperience externallyCausedExperience refl mechanismsDistinct)

------------------------------------------------------------------------
-- Evidentiary ladder.  Constructor disjointness prevents adjacent sentences or
-- legal stages from silently inheriting one another's status.
------------------------------------------------------------------------

data WitchEvidenceStage : Set where
  reportedExperience
  testimonyAdmitted
  mechanismAttributed
  agentAttributed
  witchCategoryImposed
  culpabilityAttributed
  convictionEntered
  historicalReconstruction
  : WitchEvidenceStage

report≠mechanism : reportedExperience ≡ mechanismAttributed → ⊥
report≠mechanism ()

mechanism≠agent : mechanismAttributed ≡ agentAttributed → ⊥
mechanism≠agent ()

agent≠culpability : agentAttributed ≡ culpabilityAttributed → ⊥
agent≠culpability ()

conviction≠historicalReconstruction :
  convictionEntered ≡ historicalReconstruction → ⊥
conviction≠historicalReconstruction ()

------------------------------------------------------------------------
-- Identity-source separation: an imposed accusation, a self-identification,
-- and a later symbolic reclamation are different historical relations.
------------------------------------------------------------------------

data WitchIdentitySource : Set where
  externallyAccusedWitch
  selfIdentifiedWitch
  laterReclaimedWitchSymbol
  : WitchIdentitySource

accusation≠selfIdentification :
  externallyAccusedWitch ≡ selfIdentifiedWitch → ⊥
accusation≠selfIdentification ()

selfIdentification≠laterReclamation :
  selfIdentifiedWitch ≡ laterReclaimedWitchSymbol → ⊥
selfIdentification≠laterReclamation ()

------------------------------------------------------------------------
-- Endogenous evidentiary production.  Interrogation-generated testimony is a
-- source-provenance class, not automatically independent corroboration.
------------------------------------------------------------------------

data TestimonyProvenance : Set where
  independentTestimony
  interrogationGeneratedTestimony
  confessionNamingGeneratedTestimony
  repeatedCommunityNarrative
  : TestimonyProvenance

interrogationGenerated≠independent :
  interrogationGeneratedTestimony ≡ independentTestimony → ⊥
interrogationGenerated≠independent ()

confessionGenerated≠independent :
  confessionNamingGeneratedTestimony ≡ independentTestimony → ⊥
confessionGenerated≠independent ()

record AccusationFeedbackStep : Set where
  constructor accusation-feedback-step
  field
    priorAccusationPresent : Bool
    coerciveOrDirectedInterrogationPresent : Bool
    generatedTestimonyPresent : Bool
    generatedTestimonyTreatedAsIndependent : Bool

canonicalFeedbackWarning : AccusationFeedbackStep
canonicalFeedbackWarning =
  accusation-feedback-step true true true false

------------------------------------------------------------------------
-- Existing subject-position nonfactorability remains the generic identity gate.
------------------------------------------------------------------------

representabilityStillDoesNotRecoverOriginatingSubject :
  INF.FactorsThrough Subject.categoryVisibility Subject.subjectPosition → ⊥
representabilityStillDoesNotRecoverOriginatingSubject =
  Subject.categoryVisibilityCannotRecoverSubjectPosition

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

record WitchTrialEvidenceBoundary : Set where
  constructor witch-trial-evidence-boundary
  field
    reportedExperienceEqualsExternalMechanism : Bool
    admittedTestimonyEqualsAgentIdentification : Bool
    accusationEqualsSelfIdentification : Bool
    courtConvictionEqualsHistoricalTruth : Bool
    multipleGeneratedTestimoniesAreAutomaticallyIndependent : Bool
    unjustProsecutionProvesNoHistoricalMagicPracticeExisted : Bool
    historicalMagicPracticeProvesDemonologicalMechanism : Bool
    earlyModernAccusedWitchEqualsModernWiccan : Bool

canonicalWitchTrialEvidenceBoundary : WitchTrialEvidenceBoundary
canonicalWitchTrialEvidenceBoundary =
  witch-trial-evidence-boundary
    false false false false false false false false
