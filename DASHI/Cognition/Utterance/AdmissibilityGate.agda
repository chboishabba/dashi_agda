module DASHI.Cognition.Utterance.AdmissibilityGate where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

open import DASHI.Cognition.Utterance.LayeredMeaningCore

------------------------------------------------------------------------
-- Literal and symbolic interpretation are distinct paths.
------------------------------------------------------------------------

data LiteralSourceShape : Set where
  itemwiseAssertion frameLabelOnly ambiguousSourceShape : LiteralSourceShape

data MoralAgency : AgentClass → Set where
  liveHumanMoralAgency : MoralAgency liveHuman
  historicalHumanMoralAgency : MoralAgency historicalPersonDeceased

data PresentAgency : AgentClass → Set where
  liveHumanPresentAgency : PresentAgency liveHuman
  minorHumanPresentAgency : PresentAgency minorHuman
  institutionPresentAgency : PresentAgency institution

data NonEmptyEvidence : EvidenceStatus → Set where
  supportedEvidenceIsNonEmpty : NonEmptyEvidence supportedEvidenceChain

record LiteralPromotionProof
    (shape : LiteralSourceShape)
    (agent : AgentClass)
    (evidence : EvidenceStatus) : Set where
  constructor literalPromotionProof
  field
    sourceIsItemwise : shape ≡ itemwiseAssertion
    moralAgency : MoralAgency agent
    presentAgency : PresentAgency agent
    evidenceIsNonEmpty : NonEmptyEvidence evidence

open LiteralPromotionProof public

frameLabelBlocksItemwisePromotion :
  LiteralPromotionProof frameLabelOnly liveHuman supportedEvidenceChain →
  ⊥
frameLabelBlocksItemwisePromotion proof with sourceIsItemwise proof
... | ()

fictionalCharacterBlocksLiteralPromotion :
  {shape : LiteralSourceShape} →
  {evidence : EvidenceStatus} →
  LiteralPromotionProof shape fictionalCharacter evidence →
  ⊥
fictionalCharacterBlocksLiteralPromotion proof with moralAgency proof
... | ()

deceasedPresentTenseBlocksLiteralPromotion :
  {shape : LiteralSourceShape} →
  {evidence : EvidenceStatus} →
  LiteralPromotionProof shape historicalPersonDeceased evidence →
  ⊥
deceasedPresentTenseBlocksLiteralPromotion proof with presentAgency proof
... | ()

emptyEvidenceBlocksLiteralPromotion :
  {shape : LiteralSourceShape} →
  {agent : AgentClass} →
  LiteralPromotionProof shape agent emptyEvidenceChain →
  ⊥
emptyEvidenceBlocksLiteralPromotion proof with evidenceIsNonEmpty proof
... | ()

record SymbolicAdmissionProof (r : TypedReferent) : Set where
  constructor symbolicAdmissionProof
  field
    selectedDomain : RuptureDomain
    selectedAffect : Affect
    relationBasis : String

open SymbolicAdmissionProof public

admitSymbolicAnchor :
  (r : TypedReferent) →
  SymbolicAdmissionProof r →
  SymbolicAnchor
admitSymbolicAnchor r proof =
  symbolicAnchor
    r
    (selectedDomain proof)
    (selectedAffect proof)
    symbolicAdmissible
    refl

canonicalLiteralBlockingGrounds : List BlockingGround
canonicalLiteralBlockingGrounds =
  sourceTextViolation
  ∷ agentClassViolation
  ∷ evidenceChainViolation
  ∷ []
