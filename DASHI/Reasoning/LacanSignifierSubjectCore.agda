module DASHI.Reasoning.LacanSignifierSubjectCore where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.EventAlgebra as PNF
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Interop.SensibLawResidualLattice as Residual

------------------------------------------------------------------------
-- Lacanian structural vocabulary over PNF.
------------------------------------------------------------------------

data LacanianTerm : Set where
  masterSignifier knowledgeNetwork barredSubjectTerm objetATerm : LacanianTerm

data LacanianRegister : Set where
  imaginaryRegister symbolicRegister realRegister : LacanianRegister

record SignifierLink : Set₁ where
  field
    source target : PNF.EventPNF
    differentialRelation : String
    revisionReceipt : String
    residual : Residual.ResidualLevel
    intrinsicMeaningClaimed : Bool

record BarredSubject : Set₁ where
  field
    synthesisIndex : String
    selfDescriptions : List PNF.EventPNF
    enunciationPosition : String
    omittedSelfPosition : String
    totalSelfRepresentationClaimed : Bool
    substantialSubjectObjectClaimed : Bool

record CandidateObjetA : Set where
  field
    sourceResidual : Residual.ResidualLevel
    causePositionLabel : String
    causeProjectionReceipt : String
    ordinaryDesiredObjectClaimed : Bool
    rawResidualIdentifiedWithObjetA : Bool
    empiricalObjectLocated : Bool

record BigOtherPresentation : Set₁ where
  field
    boundedCommonBelief : Memory.BoundedCommonBelief
    symbolicRules : List String
    presumedConsistency : Bool
    actualOmniscientAgentExistsClaimed : Bool
    otherOfOtherExistsClaimed : Bool
    presentationReceipt : String


data KnowledgeAuthorityKind : Set where
  supposedAuthority verifiedAuthority : KnowledgeAuthorityKind

supposedAuthorityIsNotVerified :
  supposedAuthority ≡ verifiedAuthority → ⊥
supposedAuthorityIsNotVerified ()

record SupposedKnowledge : Set₁ where
  field
    supposedKnower : String
    attributedKnowledge : List PNF.EventPNF
    verificationReceiptAvailable : Bool
    verificationReceiptReference : String
    suppositionEqualsVerificationClaimed : Bool
    authorityReceipt : String

record RegisterProjection : Set₁ where
  field
    event : PNF.EventPNF
    projectedRegister : LacanianRegister
    projectionReceipt : String
    symbolicPNFCarrier : Bool
    imaginaryMeansFalseClaimed : Bool
    realEqualsNoTypedMeetClaimed : Bool
    realEqualsStage8Claimed : Bool

record LacanSignifierSubjectAuthorityBoundary : Set where
  field
    pnfMayCarrySymbolicRelations : Bool
    barredSubjectIsOrdinaryObject : Bool
    objetAIsOrdinaryDesiredObject : Bool
    objetAIsRawResidual : Bool
    bigOtherIsOmniscientPerson : Bool
    supposedKnowledgeEqualsVerifiedKnowledge : Bool
    realEqualsAnySingleResidualCode : Bool
    registerProjectionDiagnosesPerson : Bool
    boundaryNote : String

canonicalLacanSignifierSubjectAuthorityBoundary :
  LacanSignifierSubjectAuthorityBoundary
canonicalLacanSignifierSubjectAuthorityBoundary = record
  { pnfMayCarrySymbolicRelations = true
  ; barredSubjectIsOrdinaryObject = false
  ; objetAIsOrdinaryDesiredObject = false
  ; objetAIsRawResidual = false
  ; bigOtherIsOmniscientPerson = false
  ; supposedKnowledgeEqualsVerifiedKnowledge = false
  ; realEqualsAnySingleResidualCode = false
  ; registerProjectionDiagnosesPerson = false
  ; boundaryNote =
      "PNF provides a Symbolic carrier; barred subject, objet a, Big Other and RSI remain structural positions rather than ordinary objects or diagnoses."
  }
