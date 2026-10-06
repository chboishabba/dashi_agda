module DASHI.Governance.OccupyConsensusEvidenceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- OCCUPY CONSENSUS EVIDENCE ATLAS.
--
-- Provenance class: SECONDARY / EMPIRICAL SCHOLARSHIP.
-- This atlas is deliberately plural.  It does not treat the attached speaker's
-- retrospective interpretation as independently verified merely because some
-- studies document burdens, nor does positive deliberative evidence erase the
-- documented burdens.
------------------------------------------------------------------------

data EvidenceRole : Set where
  burdenObservation : EvidenceRole
  deliberativeBenefitObservation : EvidenceRole
  coordinationMechanismObservation : EvidenceRole
  adaptivePracticeObservation : EvidenceRole

record OccupyEvidenceSource : Set where
  constructor occupyEvidenceSource
  field
    author : String
    title : String
    venue : String
    year : Nat
    identifier : String
    role : EvidenceRole
    sourceSupports : String
    sourceDoesNotByItselfSupport : String

open OccupyEvidenceSource public

min2015Deliberation : OccupyEvidenceSource
min2015Deliberation =
  occupyEvidenceSource
    "Seong-Jae Min"
    "Occupy Wall Street and Deliberative Decision-Making: Translating Theory to Practice"
    "Communication, Culture & Critique 8(1):73-89"
    2015
    "doi:10.1111/cccr.12074"
    deliberativeBenefitObservation
    "participant-observer evidence that OWS General Assembly practice approximated deliberative-democratic procedural ideals to a meaningful extent and supported citizenship/deliberative practice"
    "a claim that consensus was costless, universally scalable, or empirically optimal"

savio2015Coordination : OccupyEvidenceSource
savio2015Coordination =
  occupyEvidenceSource
    "Gianmarco Savio"
    "Coordination outside formal organization: consensus-based decision-making and occupation in the Occupy Wall Street movement"
    "Contemporary Justice Review 18(1):42-54"
    2015
    "doi:10.1080/10282580.2015.1005509"
    coordinationMechanismObservation
    "ethnographic evidence that mass assemblies and the occupation itself could function as mechanisms of coordination despite decentralized organization"
    "a proof that decentralized coordination always succeeds or outperforms formal organization"

hammond2013Burden : OccupyEvidenceSource
hammond2013Burden =
  occupyEvidenceSource
    "John L. Hammond"
    "The significance of space in Occupy Wall Street"
    "Interface: a journal for and about social movements 5(2):499-524"
    2013
    "peer-reviewed article; Interface 5(2)"
    burdenObservation
    "participant/interview/documentary evidence that consensus and openness could be cumbersome and that large-assembly participation imposed practical burdens"
    "a quantitative causal law from group size to organizational failure"

pollettaHoban2016Adaptation : OccupyEvidenceSource
pollettaHoban2016Adaptation =
  occupyEvidenceSource
    "Francesca Polletta and Katt Hoban"
    "Why Consensus?"
    "Journal of Social and Political Psychology 4(1)"
    2016
    "doi:10.5964/jspp.v4i1.524"
    adaptivePracticeObservation
    "interview evidence that contemporary activists treated consensus pragmatically, adjusted procedures, and in some Occupy settings devolved authority to committees or used voting"
    "a single uniform description of every Occupy camp or an experimental causal estimate"

canonicalOccupyEvidenceSources : List OccupyEvidenceSource
canonicalOccupyEvidenceSources =
  min2015Deliberation
  ∷ savio2015Coordination
  ∷ hammond2013Burden
  ∷ pollettaHoban2016Adaptation
  ∷ []

record OccupyConsensusEvidenceBoundary : Set where
  constructor occupyConsensusEvidenceBoundary
  field
    documentedBurdenEvidencePresent : Bool
    documentedDeliberativeBenefitEvidencePresent : Bool
    documentedCoordinationMechanismEvidencePresent : Bool
    documentedAdaptivePracticeEvidencePresent : Bool

    evidenceProvesUniversalConsensusFailure : Bool
    evidenceProvesConsensusUniversallySuperior : Bool
    evidenceProvesQuantitativeGroupSizeScalingLaw : Bool
    evidenceIndependentlyVerifiesEveryTranscriptClaim : Bool
    evidenceSupportsPluralNonCherryPickedReading : Bool

open OccupyConsensusEvidenceBoundary public

canonicalOccupyConsensusEvidenceBoundary : OccupyConsensusEvidenceBoundary
canonicalOccupyConsensusEvidenceBoundary =
  occupyConsensusEvidenceBoundary
    true
    true
    true
    true
    false
    false
    false
    false
    true

record OccupyEvidenceSynthesis : Set where
  constructor occupyEvidenceSynthesis
  field
    burden : OccupyEvidenceSource
    benefit : OccupyEvidenceSource
    coordination : OccupyEvidenceSource
    adaptation : OccupyEvidenceSource

    burdenRole : role burden ≡ burdenObservation
    benefitRole : role benefit ≡ deliberativeBenefitObservation
    coordinationRole : role coordination ≡ coordinationMechanismObservation
    adaptationRole : role adaptation ≡ adaptivePracticeObservation

open OccupyEvidenceSynthesis public

canonicalOccupyEvidenceSynthesis : OccupyEvidenceSynthesis
canonicalOccupyEvidenceSynthesis =
  occupyEvidenceSynthesis
    hammond2013Burden
    min2015Deliberation
    savio2015Coordination
    pollettaHoban2016Adaptation
    refl
    refl
    refl
    refl

canonicalOccupyConsensusEvidenceReceipt : GenericReceipt.GenericReceipt
canonicalOccupyConsensusEvidenceReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "plural Occupy consensus evidence atlas"
    "DASHI.Governance.OccupyConsensusEvidenceAtlasExact"
    "canonicalOccupyConsensusEvidenceSynthesis"
    "retains separately typed evidence for deliberative benefits, coordination mechanisms, practical burdens, and adaptive procedural responses in Occupy-related scholarship"
    "the evidence does not establish universal consensus failure or superiority, a quantitative size-to-burden scaling law, or wholesale independent verification of the attached speaker's retrospective account"
    "agda -i . DASHI/Governance/OccupyConsensusEvidenceAtlasRegression.agda"
