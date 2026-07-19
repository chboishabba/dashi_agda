module DASHI.Cognition.Utterance.LayeredMeaningCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Level; Set; Setω; lsuc; _⊔_)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- Layered DASHI/PNF utterance derivation.
--
-- The construction order is part of the type discipline:
-- surface -> text atoms -> typed referents -> candidates -> gate -> PNF
-- -> invariant.  No constructor below turns a surface string directly into a
-- promoted world fact.
------------------------------------------------------------------------

data Layer : Set where
  surfaceLayer textAtomLayer entityTypingLayer candidateLayer : Layer
  admissibilityLayer pnfLayer invariantLayer : Layer

data EvidenceStatus : Set where
  observedSurface emptyEvidenceChain supportedEvidenceChain : EvidenceStatus

data AgentClass : Set where
  liveHuman minorHuman historicalPersonDeceased fictionalCharacter : AgentClass
  institution artefact unknownAgentClass : AgentClass

data RuptureDomain : Set where
  familyRupture collaboratorRupture peerRupture industryRupture : RuptureDomain
  politicalSymbolicRupture racialHistoricalRupture : RuptureDomain
  childhoodSymbolRupture memeRupture absurdityRupture unknownRupture : RuptureDomain

data Affect : Set where
  pain betrayal grief anger alienation unknownAffect : Affect

data PromotionDisposition : Set where
  literalBlocked symbolicAdmissible candidateDemoted factPromoted : PromotionDisposition

data BlockingGround : Set where
  sourceTextViolation agentClassViolation evidenceChainViolation : BlockingGround

data ScopeBasis : Set where
  layoutAdjacency explicitGrammar explicitReference externalEvidence : ScopeBasis

record SourceSurface : Set where
  constructor sourceSurface
  field
    medium : String
    authorSurface : String
    visibleTextBlocks : List String
    evidenceStatus : EvidenceStatus

open SourceSurface public

record TextAtom (S : SourceSurface) : Set where
  constructor textAtom
  field
    textBasis : String

open TextAtom public

record EnumerationAtom (S : SourceSurface) : Set where
  constructor enumerationAtom
  field
    itemStrings : List String

open EnumerationAtom public

record TypedReferent : Set where
  constructor typedReferent
  field
    surfaceName : String
    wikidataIdentifier : String
    wikidataType : String
    agentClass : AgentClass
    relationToSubject : String
    domains : List RuptureDomain

open TypedReferent public

record DerivedCandidate
    (S : SourceSurface) : Set where
  constructor derivedCandidate
  field
    candidateLabel : String
    sourceAtoms : List (TextAtom S)
    scopeBasis : ScopeBasis
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

open DerivedCandidate public

record LiteralPromotionAttempt : Set where
  constructor literalPromotionAttempt
  field
    attemptedPredicate : String
    subject : TypedReferent
    object : TypedReferent
    blockingGrounds : List BlockingGround
    disposition : PromotionDisposition
    dispositionIsBlocked : disposition ≡ literalBlocked

open LiteralPromotionAttempt public

record SymbolicAnchor : Set where
  constructor symbolicAnchor
  field
    anchor : TypedReferent
    ruptureDomain : RuptureDomain
    affect : Affect
    disposition : PromotionDisposition
    dispositionIsAdmissible : disposition ≡ symbolicAdmissible

open SymbolicAnchor public

record QualifierState : Set where
  constructor qualifierState
  field
    modality : String
    certainty : String
    tense : String
    polarity : String

open QualifierState public

record WrapperState : Set where
  constructor wrapperState
  field
    evidence : EvidenceStatus
    literalFactPromotion : PromotionDisposition
    symbolicInterpretation : PromotionDisposition
    carriesRuntimeAuthority : Bool
    carriesRuntimeAuthorityIsFalse : carriesRuntimeAuthority ≡ false

open WrapperState public

record PredicatePNF (S : SourceSurface) : Set where
  constructor predicatePNF
  field
    predicateLabel : String
    speaker : TypedReferent
    content : SourceSurface
    frame : DerivedCandidate S
    enumeration : List TypedReferent
    qualifiers : QualifierState
    wrapper : WrapperState

open PredicatePNF public

record RuptureAnchor : Set where
  constructor ruptureAnchor
  field
    ruptureSubject : TypedReferent
    ruptureReferent : TypedReferent
    ruptureRelation : String
    ruptureDomain : RuptureDomain
    ruptureAffect : Affect

open RuptureAnchor public

record InvariantExtraction (S : SourceSurface) : Set where
  constructor invariantExtraction
  field
    pnf : PredicatePNF S
    anchors : List RuptureAnchor
    invariantLabel : String
    constructiveDirection : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    carriesClinicalAuthority : Bool
    carriesClinicalAuthorityIsFalse : carriesClinicalAuthority ≡ false

open InvariantExtraction public

------------------------------------------------------------------------
-- Structural impossibility: a blocked literal attempt cannot simultaneously
-- carry a proof that its disposition is factPromoted.
------------------------------------------------------------------------

literalBlockedNotFactPromoted :
  (a : LiteralPromotionAttempt) →
  disposition a ≡ factPromoted →
  ⊥
literalBlockedNotFactPromoted a promoted with dispositionIsBlocked a
... | refl with promoted
... | ()
