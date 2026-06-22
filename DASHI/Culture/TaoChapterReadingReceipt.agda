module DASHI.Culture.TaoChapterReadingReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc)
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
  CarrySeedGrammar : TaoReadingKind

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
  body : TaoMotif
  boundary : TaoMotif
  seed : TaoMotif
  carry : TaoMotif
  successor : TaoMotif
  oppositeSeed : TaoMotif

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

chapter11PrimaryRow : TaoReadingRow
chapter11PrimaryRow =
  taoReadingRow
    1
    chapter11
    emptiness
    enablesUse
    usefulnessThroughAbsence
    translationDependentQualifier
    EmptinessUtilityGrammar
    CandidateAnalogy
    false
    "Chapter 11 reads emptiness as enabling use rather than originating form."

chapter11PrimaryRowReceipt : TaoReadingRowReceipt chapter11PrimaryRow
chapter11PrimaryRowReceipt =
  taoReadingRowReceipt refl

chapter11Receipt : TaoChapterReceipt
chapter11Receipt =
  taoChapterReceipt
    chapter11
    canonicalTaoSourceReceipt
    "It is their empty space that is of use."
    (candidateFormalPayload
      (just "TaoTeChing.Cosmos.chapter11")
      (just "DASHI.Culture.TaoChapterReadingReceipt.chapter11Receipt")
      1)
    (EmptinessUtilityGrammar ∷ NonBeingUsefulness ∷ TranslationDependentMetaphor ∷ [])
    (emptiness ∷ usefulnessThroughAbsence ∷ boundary ∷ [])
    (assertionStrengthProfile 0 0 1 0 0 true "medium")
    (chapter11PrimaryRow ∷ [])
    canonicalTaoAuthorityBits
    canonicalTaoBoundaryFailClosed

chapter16PrimaryRow : TaoReadingRow
chapter16PrimaryRow =
  taoReadingRow
    2
    chapter16
    returnToRoot
    returnsTo
    stillness
    translationDependentQualifier
    ReturnToRootGrammar
    PracticeGrammar
    false
    "Chapter 16 reads return to the root as a stillness grammar rather than a metaphysical proof."

chapter16PrimaryRowReceipt : TaoReadingRowReceipt chapter16PrimaryRow
chapter16PrimaryRowReceipt =
  taoReadingRowReceipt refl

chapter16Receipt : TaoChapterReceipt
chapter16Receipt =
  taoChapterReceipt
    chapter16
    canonicalTaoSourceReceipt
    "Returning to the root is stillness."
    (candidateFormalPayload
      (just "TaoTeChing.Cosmos.chapter16")
      (just "DASHI.Culture.TaoChapterReadingReceipt.chapter16Receipt")
      1)
    (ReturnToRootGrammar ∷ StillnessGrammar ∷ PracticeAphorism ∷ [])
    (returnToRoot ∷ stillness ∷ dao ∷ [])
    (assertionStrengthProfile 0 0 0 1 0 true "medium")
    (chapter16PrimaryRow ∷ [])
    canonicalTaoAuthorityBits
    canonicalTaoBoundaryFailClosed

chapter22PrimaryRow : TaoReadingRow
chapter22PrimaryRow =
  taoReadingRow
    3
    chapter22
    reversal
    alignsWith
    complementarity
    translationDependentQualifier
    ReversalGrammar
    ContrastiveReading
    false
    "Chapter 22 reads yielding and reversal as a candidate polarity grammar of renewal."

chapter22PrimaryRowReceipt : TaoReadingRowReceipt chapter22PrimaryRow
chapter22PrimaryRowReceipt =
  taoReadingRowReceipt refl

chapter22Receipt : TaoChapterReceipt
chapter22Receipt =
  taoChapterReceipt
    chapter22
    canonicalTaoSourceReceipt
    "Yield and remain whole; empty and become full."
    (candidateFormalPayload
      (just "TaoTeChing.Cosmos.chapter22")
      (just "DASHI.Culture.TaoChapterReadingReceipt.chapter22Receipt")
      1)
    (ReversalGrammar ∷ ComplementarityGrammar ∷ SelfEffacementGrammar ∷ [])
    (reversal ∷ emptiness ∷ complementarity ∷ selfEffacement ∷ [])
    (assertionStrengthProfile 0 0 1 1 0 true "medium")
    (chapter22PrimaryRow ∷ [])
    canonicalTaoAuthorityBits
    canonicalTaoBoundaryFailClosed

chapter28PrimaryRow : TaoReadingRow
chapter28PrimaryRow =
  taoReadingRow
    4
    chapter28
    uncarvedBlock
    associatedWith
    complementarity
    translationDependentQualifier
    UncarvedBlockGrammar
    MetaphoricMapping
    false
    "Chapter 28 reads the uncarved block as a candidate polarity-retention grammar across paired aspects."

chapter28PrimaryRowReceipt : TaoReadingRowReceipt chapter28PrimaryRow
chapter28PrimaryRowReceipt =
  taoReadingRowReceipt refl

chapter28Receipt : TaoChapterReceipt
chapter28Receipt =
  taoChapterReceipt
    chapter28
    canonicalTaoSourceReceipt
    "Know the male but keep to the female."
    (candidateFormalPayload
      (just "TaoTeChing.Cosmos.chapter28")
      (just "DASHI.Culture.TaoChapterReadingReceipt.chapter28Receipt")
      1)
    (UncarvedBlockGrammar ∷ ComplementarityGrammar ∷ ReturnToRootGrammar ∷ [])
    (uncarvedBlock ∷ complementarity ∷ returnToRoot ∷ infant ∷ [])
    (assertionStrengthProfile 0 0 1 0 0 true "medium")
    (chapter28PrimaryRow ∷ [])
    canonicalTaoAuthorityBits
    canonicalTaoBoundaryFailClosed

chapter36PrimaryRow : TaoReadingRow
chapter36PrimaryRow =
  taoReadingRow
    5
    chapter36
    softness
    overcomes
    antiExcess
    translationDependentQualifier
    ReversalGrammar
    ConditionalAphorism
    false
    "Chapter 36 reads softness and weakness as reversal-at-extreme grammar rather than general strategic law."

chapter36PrimaryRowReceipt : TaoReadingRowReceipt chapter36PrimaryRow
chapter36PrimaryRowReceipt =
  taoReadingRowReceipt refl

chapter36Receipt : TaoChapterReceipt
chapter36Receipt =
  taoChapterReceipt
    chapter36
    canonicalTaoSourceReceipt
    "The soft overcomes the hard, the weak the strong."
    (candidateFormalPayload
      (just "TaoTeChing.Cosmos.chapter36")
      (just "DASHI.Culture.TaoChapterReadingReceipt.chapter36Receipt")
      1)
    (ReversalGrammar ∷ SoftOverHardOperator ∷ PracticeAphorism ∷ [])
    (softness ∷ antiExcess ∷ threshold ∷ [])
    (assertionStrengthProfile 0 0 0 1 0 true "medium")
    (chapter36PrimaryRow ∷ [])
    canonicalTaoAuthorityBits
    canonicalTaoBoundaryFailClosed

chapter37PrimaryRow : TaoReadingRow
chapter37PrimaryRow =
  taoReadingRow
    6
    chapter37
    nonAction
    selfOrders
    spontaneousOrdering
    authorityBlockedQualifier
    NonActionGovernance
    PracticeGrammar
    false
    "Chapter 37 reads non-action as a candidate self-ordering grammar with desire stilled by nameless simplicity."

chapter37PrimaryRowReceipt : TaoReadingRowReceipt chapter37PrimaryRow
chapter37PrimaryRowReceipt =
  taoReadingRowReceipt refl

chapter37CarryRow : TaoReadingRow
chapter37CarryRow =
  taoReadingRow
    7
    chapter37
    seed
    alignsWith
    carry
    candidateOnlyQualifier
    CarrySeedGrammar
    CandidateAnalogy
    false
    "Chapter 37 supports a candidate-only seed/carry reading in which simplicity opens the next non-forced transition."

chapter37CarryRowReceipt : TaoReadingRowReceipt chapter37CarryRow
chapter37CarryRowReceipt =
  taoReadingRowReceipt refl

chapter37Receipt : TaoChapterReceipt
chapter37Receipt =
  taoChapterReceipt
    chapter37
    canonicalTaoSourceReceipt
    "The Dao does nothing, yet nothing is left undone."
    (candidateFormalPayload
      (just "TaoTeChing.Cosmos.chapter37")
      (just "DASHI.Culture.TaoChapterReadingReceipt.chapter37Receipt")
      2)
    (NonActionGovernance ∷ DesireReductionGrammar ∷ CarrySeedGrammar ∷ [])
    (nonAction ∷ spontaneousOrdering ∷ simplicity ∷ seed ∷ carry ∷ [])
    (assertionStrengthProfile 0 0 1 1 0 true "medium")
    (chapter37PrimaryRow ∷ chapter37CarryRow ∷ [])
    canonicalTaoAuthorityBits
    canonicalTaoBoundaryFailClosed

canonicalTaoChapterReceipts : List TaoChapterReceipt
canonicalTaoChapterReceipts =
  chapter1Receipt
  ∷ chapter11Receipt
  ∷ chapter16Receipt
  ∷ chapter22Receipt
  ∷ chapter28Receipt
  ∷ chapter36Receipt
  ∷ chapter37Receipt
  ∷ []

taoChapterReceiptCount : List TaoChapterReceipt → Nat
taoChapterReceiptCount [] =
  zero
taoChapterReceiptCount (_ ∷ receipts) =
  suc (taoChapterReceiptCount receipts)

canonicalTaoChapterReceiptCount : Nat
canonicalTaoChapterReceiptCount =
  taoChapterReceiptCount canonicalTaoChapterReceipts
