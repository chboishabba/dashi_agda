module DASHI.Governance.BoloBoloOccupyTranscriptSourceBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Source boundary for the attached 2026-10-05 transcript.
--
-- The clip runs from the opening "end of capitalism" framing through the
-- beginning of the author's discussion of the IPCC 2018 SR1.5 report.
-- It contains autobiographical reports and author interpretations, but does
-- not yet state a detailed Bolo Bolo institutional design or climate pathway.
------------------------------------------------------------------------

data TranscriptClaimStatus : Set where
  authorReportedExperience : TranscriptClaimStatus
  authorInterpretation : TranscriptClaimStatus
  namedReferenceOnly : TranscriptClaimStatus

record TranscriptClaim : Set where
  constructor transcriptClaim
  field
    claimLabel : String
    status : TranscriptClaimStatus
    assertedInAttachedClip : Bool
    independentlyVerifiedByThisModule : Bool

open TranscriptClaim public

occupyParticipationClaim : TranscriptClaim
occupyParticipationClaim =
  transcriptClaim
    "author reports joining Occupy Wall Street in New York in 2011 and participating for six weeks"
    authorReportedExperience
    true
    false

occupyProcessClaim : TranscriptClaim
occupyProcessClaim =
  transcriptClaim
    "author reports working groups and daily general assemblies using horizontal direct-democracy and consensus-building techniques"
    authorReportedExperience
    true
    false

consensusDifficultyClaim : TranscriptClaim
consensusDifficultyClaim =
  transcriptClaim
    "author says true consensus was excruciatingly difficult to reach"
    authorInterpretation
    true
    false

growthDeteriorationClaim : TranscriptClaim
growthDeteriorationClaim =
  transcriptClaim
    "author says that as Occupy grew, its world became more complicated and internal organisation and morale deteriorated"
    authorInterpretation
    true
    false

socialEcologyEncounterClaim : TranscriptClaim
socialEcologyEncounterClaim =
  transcriptClaim
    "author reports meeting social ecologists associated with Murray Bookchin and later attending seminars"
    authorReportedExperience
    true
    false

socialEcologyAssessmentClaim : TranscriptClaim
socialEcologyAssessmentClaim =
  transcriptClaim
    "author assesses social ecology as having many good ideas but lacking a coherent plan, and says its theoretical dialectics did not resonate"
    authorInterpretation
    true
    false

boloBoloEncounterClaim : TranscriptClaim
boloBoloEncounterClaim =
  transcriptClaim
    "author reports encountering the 30th-anniversary edition of Bolo Bolo at Monkey Wrench Books in Austin"
    authorReportedExperience
    true
    false

sr15ReadingClaim : TranscriptClaim
sr15ReadingClaim =
  transcriptClaim
    "author reports a team reading the IPCC 2018 Special Report on Global Warming of 1.5 C and rejecting doom-oriented headlines as the most cynical interpretation"
    authorInterpretation
    true
    false

canonicalTranscriptClaims : List TranscriptClaim
canonicalTranscriptClaims =
  occupyParticipationClaim
  ∷ occupyProcessClaim
  ∷ consensusDifficultyClaim
  ∷ growthDeteriorationClaim
  ∷ socialEcologyEncounterClaim
  ∷ socialEcologyAssessmentClaim
  ∷ boloBoloEncounterClaim
  ∷ sr15ReadingClaim
  ∷ []

record BoloBoloOccupyTranscriptBoundary : Set where
  constructor boloBoloOccupyTranscriptBoundary
  field
    occupyParticipationReported : Bool
    horizontalConsensusProcessReported : Bool
    consensusDifficultyIsAuthorInterpretation : Bool
    growthComplexityDeteriorationIsAuthorInterpretation : Bool
    socialEcologyEncounterReported : Bool
    boloBoloEncounterReported : Bool
    sr15ReadingReported : Bool
    boloBoloInstitutionalSpecificationPresent : Bool
    sr15DetailedPathwaySpecificationPresent : Bool
    transcriptProvesQuantitativeCoordinationScalingLaw : Bool
    transcriptProvesFederationEmpiricallySuperior : Bool
    transcriptCreatesPoliticalAuthority : Bool

open BoloBoloOccupyTranscriptBoundary public

canonicalBoloBoloOccupyTranscriptBoundary :
  BoloBoloOccupyTranscriptBoundary
canonicalBoloBoloOccupyTranscriptBoundary =
  boloBoloOccupyTranscriptBoundary
    true
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false

canonicalBoloBoloOccupyTranscriptReceipt :
  GenericReceipt.GenericReceipt
canonicalBoloBoloOccupyTranscriptReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "Bolo Bolo / Occupy transcript source boundary"
    "DASHI.Governance.BoloBoloOccupyTranscriptSourceBoundaryExact"
    "canonicalBoloBoloOccupyTranscriptBoundary"
    "records only the autobiographical reports, author interpretations and named-reference surface actually present in the attached clip"
    "the clip does not yet supply a Bolo Bolo institutional specification, detailed SR1.5 pathway, quantitative coordination-scaling law, empirical federation-superiority theorem or political authority"
    "agda -i . DASHI/Governance/BoloBoloOccupyTranscriptRegression.agda"
