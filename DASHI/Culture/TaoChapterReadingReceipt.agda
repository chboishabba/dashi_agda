module DASHI.Culture.TaoChapterReadingReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Tao / Dao candidate reading receipts.
--
-- This module records chapters 1-37 from the uploaded Lean-style Book One
-- formalization as candidate interpretive payload only.  The rows are
-- source-dependent and fail closed on empirical, spiritual, mystical,
-- clinical, political, metaphysical, philological, canonical-text, and
-- doctrine authority.

data TaoChapterId : Set where
  chapter1 : TaoChapterId
  chapter2 : TaoChapterId
  chapter3 : TaoChapterId
  chapter4 : TaoChapterId
  chapter5 : TaoChapterId
  chapter6 : TaoChapterId
  chapter7 : TaoChapterId
  chapter8 : TaoChapterId
  chapter9 : TaoChapterId
  chapter10 : TaoChapterId
  chapter11 : TaoChapterId
  chapter12 : TaoChapterId
  chapter13 : TaoChapterId
  chapter14 : TaoChapterId
  chapter15 : TaoChapterId
  chapter16 : TaoChapterId
  chapter17 : TaoChapterId
  chapter18 : TaoChapterId
  chapter19 : TaoChapterId
  chapter20 : TaoChapterId
  chapter21 : TaoChapterId
  chapter22 : TaoChapterId
  chapter23 : TaoChapterId
  chapter24 : TaoChapterId
  chapter25 : TaoChapterId
  chapter26 : TaoChapterId
  chapter27 : TaoChapterId
  chapter28 : TaoChapterId
  chapter29 : TaoChapterId
  chapter30 : TaoChapterId
  chapter31 : TaoChapterId
  chapter32 : TaoChapterId
  chapter33 : TaoChapterId
  chapter34 : TaoChapterId
  chapter35 : TaoChapterId
  chapter36 : TaoChapterId
  chapter37 : TaoChapterId

canonicalTaoChapterIds : List TaoChapterId
canonicalTaoChapterIds =
  chapter1
  ∷ chapter2
  ∷ chapter3
  ∷ chapter4
  ∷ chapter5
  ∷ chapter6
  ∷ chapter7
  ∷ chapter8
  ∷ chapter9
  ∷ chapter10
  ∷ chapter11
  ∷ chapter12
  ∷ chapter13
  ∷ chapter14
  ∷ chapter15
  ∷ chapter16
  ∷ chapter17
  ∷ chapter18
  ∷ chapter19
  ∷ chapter20
  ∷ chapter21
  ∷ chapter22
  ∷ chapter23
  ∷ chapter24
  ∷ chapter25
  ∷ chapter26
  ∷ chapter27
  ∷ chapter28
  ∷ chapter29
  ∷ chapter30
  ∷ chapter31
  ∷ chapter32
  ∷ chapter33
  ∷ chapter34
  ∷ chapter35
  ∷ chapter36
  ∷ chapter37
  ∷ []

data TaoReadingKind : Set where
  ApophaticBoundary : TaoReadingKind
  NamingBoundary : TaoReadingKind
  OriginMetaphor : TaoReadingKind
  NonBeingUsefulness : TaoReadingKind
  ComplementarityGrammar : TaoReadingKind
  NonActionGovernance : TaoReadingKind
  AntiPossessionEthic : TaoReadingKind
  AntiDominationEthic : TaoReadingKind
  SoftOverHardOperator : TaoReadingKind
  ReturnToRootGrammar : TaoReadingKind
  StillnessGrammar : TaoReadingKind
  EmptinessUtilityGrammar : TaoReadingKind
  SelfEffacementGrammar : TaoReadingKind
  RulerTaxonomy : TaoReadingKind
  WarRestraintGrammar : TaoReadingKind
  SimplicityReductionGrammar : TaoReadingKind
  TranslationDependentMetaphor : TaoReadingKind
  CosmologicalMetaphor : TaoReadingKind
  PracticeAphorism : TaoReadingKind
  SpeechRestraintGrammar : TaoReadingKind
  AntiExcessGrammar : TaoReadingKind
  ReversalGrammar : TaoReadingKind
  UncarvedBlockGrammar : TaoReadingKind
  DesireReductionGrammar : TaoReadingKind

data AssertionStrength : Set where
  LiteralAssertion : AssertionStrength
  StrongUniversal : AssertionStrength
  ConditionalAphorism : AssertionStrength
  MetaphoricMapping : AssertionStrength
  ContrastiveReading : AssertionStrength
  NegativeBoundary : AssertionStrength
  PracticeGrammar : AssertionStrength
  TaxonomicReading : AssertionStrength
  CandidateAnalogy : AssertionStrength
  UncheckedTranslation : AssertionStrength

data TaoMotif : Set where
  dao : TaoMotif
  nameless : TaoMotif
  named : TaoMotif
  mystery : TaoMotif
  gate : TaoMotif
  nonBeing : TaoMotif
  being : TaoMotif
  emptiness : TaoMotif
  usefulnessThroughAbsence : TaoMotif
  nonAction : TaoMotif
  nonPossession : TaoMotif
  nonContention : TaoMotif
  stillness : TaoMotif
  returnToRoot : TaoMotif
  softness : TaoMotif
  water : TaoMotif
  valley : TaoMotif
  female : TaoMotif
  infant : TaoMotif
  breath : TaoMotif
  desireReduction : TaoMotif
  simplicity : TaoMotif
  uncarvedBlock : TaoMotif
  worldAsVessel : TaoMotif
  threshold : TaoMotif
  reversal : TaoMotif
  restraint : TaoMotif
  antiExcess : TaoMotif
  antiWeapon : TaoMotif
  selfEffacement : TaoMotif
  rulerBarelyKnown : TaoMotif
  spontaneousOrdering : TaoMotif
  complementarity : TaoMotif
  speechRestraint : TaoMotif
  greatImage : TaoMotif
  muddySettling : TaoMotif

data TaoRelation : Set where
  contrastsWith : TaoRelation
  associatedWith : TaoRelation
  coArisesWith : TaoRelation
  enablesUse : TaoRelation
  practices : TaoRelation
  allowsWithoutPossessing : TaoRelation
  resolves : TaoRelation
  returnsTo : TaoRelation
  overcomes : TaoRelation
  prefers : TaoRelation
  follows : TaoRelation
  functionsAs : TaoRelation
  alignsWith : TaoRelation
  reduces : TaoRelation
  selfOrders : TaoRelation

data TaoQualifier : Set where
  accordingToDocstringReading : TaoQualifier
  candidateOnlyQualifier : TaoQualifier
  translationDependentQualifier : TaoQualifier
  metaphorOnlyQualifier : TaoQualifier
  authorityBlockedQualifier : TaoQualifier

record TaoAuthorityBits : Set where
  constructor taoAuthorityBits
  field
    empiricalAuthority : Bool
    spiritualAuthority : Bool
    mysticalAuthority : Bool
    clinicalAuthority : Bool
    politicalAuthority : Bool
    metaphysicalAuthority : Bool
    philologicalAuthority : Bool
    canonicalTextAuthority : Bool
    promotedDoctrine : Bool
    interpretiveCandidate : Bool
    poeticFormalPayload : Bool

open TaoAuthorityBits public

canonicalTaoAuthorityBits : TaoAuthorityBits
canonicalTaoAuthorityBits =
  taoAuthorityBits
    false
    false
    false
    false
    false
    false
    false
    false
    false
    true
    true

record TaoBoundaryFailClosed : Set where
  constructor taoBoundaryFailClosed
  field
    empiricalAuthorityFalse :
      empiricalAuthority canonicalTaoAuthorityBits ≡ false
    spiritualAuthorityFalse :
      spiritualAuthority canonicalTaoAuthorityBits ≡ false
    mysticalAuthorityFalse :
      mysticalAuthority canonicalTaoAuthorityBits ≡ false
    clinicalAuthorityFalse :
      clinicalAuthority canonicalTaoAuthorityBits ≡ false
    politicalAuthorityFalse :
      politicalAuthority canonicalTaoAuthorityBits ≡ false
    metaphysicalAuthorityFalse :
      metaphysicalAuthority canonicalTaoAuthorityBits ≡ false
    philologicalAuthorityFalse :
      philologicalAuthority canonicalTaoAuthorityBits ≡ false
    canonicalTextAuthorityFalse :
      canonicalTextAuthority canonicalTaoAuthorityBits ≡ false
    promotedDoctrineFalse :
      promotedDoctrine canonicalTaoAuthorityBits ≡ false
    interpretiveCandidateTrue :
      interpretiveCandidate canonicalTaoAuthorityBits ≡ true
    poeticFormalPayloadTrue :
      poeticFormalPayload canonicalTaoAuthorityBits ≡ true

canonicalTaoBoundaryFailClosed : TaoBoundaryFailClosed
canonicalTaoBoundaryFailClosed =
  taoBoundaryFailClosed
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

taoLeanPastebinUrl : String
taoLeanPastebinUrl =
  "https://pastebin.xware.online/paste/20260621_131250_taoteching_lean"

taoLeanPastebinCanonicalId : String
taoLeanPastebinCanonicalId =
  "pastebin.xware.online/paste/20260621_131250_taoteching_lean"

record TaoExternalFormalismSource : Set where
  constructor taoExternalFormalismSource
  field
    sourceUrl : String
    canonicalId : String
    sourceHost : String
    sourceKind : String
    sourceRole : String
    sourceCandidateOnly : Bool
    sourcePromotesAuthority : Bool

open TaoExternalFormalismSource public

canonicalTaoExternalFormalismSource : TaoExternalFormalismSource
canonicalTaoExternalFormalismSource =
  taoExternalFormalismSource
    taoLeanPastebinUrl
    taoLeanPastebinCanonicalId
    "pastebin.xware.online"
    "Lean formalism paste"
    "candidate external formalism source for Tao chapter receipts"
    true
    false

record TaoSourceProvenanceSurface : Set where
  constructor taoSourceProvenanceSurface
  field
    provenanceExternalSource : TaoExternalFormalismSource
    normalizedCitationUrl : String
    normalizedCitationId : String
    citationStyle : String
    provenanceMode : String
    provenanceCandidateOnly : Bool
    provenancePromotesAuthority : Bool

open TaoSourceProvenanceSurface public

canonicalTaoSourceProvenanceSurface : TaoSourceProvenanceSurface
canonicalTaoSourceProvenanceSurface =
  taoSourceProvenanceSurface
    canonicalTaoExternalFormalismSource
    taoLeanPastebinUrl
    taoLeanPastebinCanonicalId
    "canonical URL citation"
    "candidate-only provenance surface"
    true
    false

record TaoExternalFormalismSourceWitness : Set where
  constructor taoExternalFormalismSourceWitness
  field
    urlIsCanonical :
      sourceUrl canonicalTaoExternalFormalismSource ≡ taoLeanPastebinUrl
    canonicalIdIsCanonical :
      canonicalId canonicalTaoExternalFormalismSource ≡ taoLeanPastebinCanonicalId
    candidateOnlyTrue :
      sourceCandidateOnly canonicalTaoExternalFormalismSource ≡ true
    promotesAuthorityFalse :
      sourcePromotesAuthority canonicalTaoExternalFormalismSource ≡ false

open TaoExternalFormalismSourceWitness public

canonicalTaoExternalFormalismSourceWitness :
  TaoExternalFormalismSourceWitness
canonicalTaoExternalFormalismSourceWitness =
  taoExternalFormalismSourceWitness
    refl
    refl
    refl
    refl

record TaoSourceProvenanceSurfaceWitness : Set where
  constructor taoSourceProvenanceSurfaceWitness
  field
    normalizedUrlIsCanonical :
      normalizedCitationUrl canonicalTaoSourceProvenanceSurface ≡ taoLeanPastebinUrl
    normalizedIdIsCanonical :
      normalizedCitationId canonicalTaoSourceProvenanceSurface ≡ taoLeanPastebinCanonicalId
    candidateOnlyTrue :
      provenanceCandidateOnly canonicalTaoSourceProvenanceSurface ≡ true
    promotesAuthorityFalse :
      provenancePromotesAuthority canonicalTaoSourceProvenanceSurface ≡ false

open TaoSourceProvenanceSurfaceWitness public

canonicalTaoSourceProvenanceSurfaceWitness :
  TaoSourceProvenanceSurfaceWitness
canonicalTaoSourceProvenanceSurfaceWitness =
  taoSourceProvenanceSurfaceWitness
    refl
    refl
    refl
    refl

record TaoSourceReceipt : Set where
  constructor taoSourceReceipt
  field
    sourceFamily : String
    chapterScope : String
    translationBasis : String
    sourceSpan : Maybe String
    languageBasis : String
    philologyStatus : String
    redactionStatus : String
    formalizer : Maybe String
    artifactHash : Maybe String
    externalFormalismSource : TaoExternalFormalismSource
    provenanceSurface : TaoSourceProvenanceSurface
    authorityBits : TaoAuthorityBits
    failClosed : TaoBoundaryFailClosed

open TaoSourceReceipt public

canonicalTaoSourceReceipt : TaoSourceReceipt
canonicalTaoSourceReceipt =
  taoSourceReceipt
    "TaoTeChing/Daodejing"
    "Book One Chapters 1-37"
    "Uploaded Lean docstrings"
    nothing
    "English rendered approximation"
    "unchecked"
    "chapter-local approximation"
    nothing
    nothing
    canonicalTaoExternalFormalismSource
    canonicalTaoSourceProvenanceSurface
    canonicalTaoAuthorityBits
    canonicalTaoBoundaryFailClosed

record TaoSourceReceiptWitness : Set where
  constructor taoSourceReceiptWitness
  field
    externalSourceIsCanonical :
      externalFormalismSource canonicalTaoSourceReceipt
      ≡ canonicalTaoExternalFormalismSource
    provenanceSurfaceIsCanonical :
      provenanceSurface canonicalTaoSourceReceipt
      ≡ canonicalTaoSourceProvenanceSurface
    authorityBitsAreCanonical :
      authorityBits canonicalTaoSourceReceipt ≡ canonicalTaoAuthorityBits
    failClosedIsCanonical :
      failClosed canonicalTaoSourceReceipt ≡ canonicalTaoBoundaryFailClosed

open TaoSourceReceiptWitness public

canonicalTaoSourceReceiptWitness : TaoSourceReceiptWitness
canonicalTaoSourceReceiptWitness =
  taoSourceReceiptWitness
    refl
    refl
    refl
    refl

record AssertionStrengthProfile : Set where
  constructor assertionStrengthProfile
  field
    literalClaims : Nat
    universalClaims : Nat
    metaphorRows : Nat
    aphorismRows : Nat
    boundaryRows : Nat
    translationDependent : Bool
    overassertionRisk : String

open AssertionStrengthProfile public

record CandidateFormalPayload : Set where
  constructor candidateFormalPayload
  field
    leanPropSurface : Maybe String
    agdaBoundarySurface : Maybe String
    normalizedRowCount : Nat

open CandidateFormalPayload public

record TaoReadingRow : Set where
  constructor taoReadingRow
  field
    rowId : Nat
    chapterId : TaoChapterId
    subject : TaoMotif
    relation : TaoRelation
    object : TaoMotif
    qualifier : TaoQualifier
    readingKind : TaoReadingKind
    strength : AssertionStrength
    authorityAllowed : Bool
    reading : String

open TaoReadingRow public

record TaoReadingRowReceipt (row : TaoReadingRow) : Set where
  constructor taoReadingRowReceipt
  field
    authorityBlocked :
      authorityAllowed row ≡ false

open TaoReadingRowReceipt public

record TaoChapterReceipt : Set where
  constructor taoChapterReceipt
  field
    chapterId : TaoChapterId
    sourceReceipt : TaoSourceReceipt
    docstringText : String
    candidatePayload : CandidateFormalPayload
    readingKinds : List TaoReadingKind
    operatorTerms : List TaoMotif
    strengthProfile : AssertionStrengthProfile
    rows : List TaoReadingRow
    authorityBits : TaoAuthorityBits
    failClosed : TaoBoundaryFailClosed

open TaoChapterReceipt public

chapter1PrimaryRow : TaoReadingRow
chapter1PrimaryRow =
  taoReadingRow
    0
    chapter1
    dao
    contrastsWith
    nameless
    translationDependentQualifier
    ApophaticBoundary
    NegativeBoundary
    false
    "Chapter 1 contrasts spoken Dao with the eternal or constant Dao without promoting a metaphysical theorem."

chapter1PrimaryRowReceipt : TaoReadingRowReceipt chapter1PrimaryRow
chapter1PrimaryRowReceipt =
  taoReadingRowReceipt refl

chapter1Receipt : TaoChapterReceipt
chapter1Receipt =
  taoChapterReceipt
    chapter1
    canonicalTaoSourceReceipt
    "The way that can be stated is not the eternal way."
    (candidateFormalPayload
      (just "TaoTeChing.Cosmos.chapter1")
      (just "DASHI.Culture.TaoChapterReadingReceipt.chapter1Receipt")
      1)
    (ApophaticBoundary ∷ NamingBoundary ∷ TranslationDependentMetaphor ∷ [])
    (dao ∷ nameless ∷ mystery ∷ gate ∷ [])
    (assertionStrengthProfile 0 0 1 0 1 true "high")
    (chapter1PrimaryRow ∷ [])
    canonicalTaoAuthorityBits
    canonicalTaoBoundaryFailClosed
