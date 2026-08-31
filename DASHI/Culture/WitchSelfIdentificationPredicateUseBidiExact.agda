module DASHI.Culture.WitchSelfIdentificationPredicateUseBidiExact where

------------------------------------------------------------------------
-- "I AM A WITCH" -- PREDICATE / USE / SELF-AUTHORITY BIDI
--
-- The same sentence surface can instantiate different predicate bundles.
-- Self-description, religious affiliation, political reclamation, practice,
-- metaphysical commitment, community membership, genealogy and authority over
-- self-description are independent coordinates.
--
-- No Wittgenstein proposition is attributed here: the repository currently has
-- no recovered Wittgenstein source owner.  A future source-bounded bridge may
-- connect rule/use/practice ideas without changing the finite DASHI theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Culture.SymbolicInversionAuthorityTransferBidiExact as Symbol
import DASHI.Culture.ReligiousSanctionFeministWiccaCrossPollinationExact as FW

------------------------------------------------------------------------
-- 1. Predicate coordinates exposed by the sentence.
------------------------------------------------------------------------

data SelfIdentificationPredicateRole : Set where
  lexicalSelfDescription
  religiousAffiliation
  politicalReclamation
  metaphysicalCommitment
  ritualPractice
  communityMembership
  historicalGenealogy
  authorityOverSelfDescription
  publicPresentation
  temporalIdentity
  : SelfIdentificationPredicateRole

record SelfIdentificationPredicate : Set where
  constructor self-identification-predicate
  field
    name : String
    role : SelfIdentificationPredicateRole
    reading : String

open SelfIdentificationPredicate public

witchSelfIdentificationPredicates : List SelfIdentificationPredicate
witchSelfIdentificationPredicates =
  self-identification-predicate "self-description" lexicalSelfDescription
    "speaker applies the lexical token witch to themself"
  ∷ self-identification-predicate "religious-affiliation" religiousAffiliation
    "whether the speaker identifies with Wicca, Paganism or another religious tradition"
  ∷ self-identification-predicate "political-reclamation" politicalReclamation
    "whether the token is used as feminist/political reclamation"
  ∷ self-identification-predicate "metaphysical-commitment" metaphysicalCommitment
    "whether the utterance carries supernatural or theological commitments"
  ∷ self-identification-predicate "practice" ritualPractice
    "whether the speaker engages in ritual, magical, devotional or other named practice"
  ∷ self-identification-predicate "community" communityMembership
    "whether the speaker belongs to a recognised community or institution"
  ∷ self-identification-predicate "genealogy" historicalGenealogy
    "whether a claimed historical lineage is asserted and what evidence supports it"
  ∷ self-identification-predicate "self-authority" authorityOverSelfDescription
    "speaker's authority to describe their present self is distinct from authority over historical genealogy or external persons"
  ∷ self-identification-predicate "public-surface" publicPresentation
    "the same public sentence can be emitted by distinct fine-grained identity states"
  ∷ self-identification-predicate "time" temporalIdentity
    "present self-identification does not automatically reconstruct earlier identity"
  ∷ []

record WitchSelfIdentificationAssertion : Set where
  constructor witch-self-identification-assertion
  field
    naturalLanguage : String
    predicates : List SelfIdentificationPredicate
    provenance : String

open WitchSelfIdentificationAssertion public

canonicalWitchSelfIdentification : WitchSelfIdentificationAssertion
canonicalWitchSelfIdentification = witch-self-identification-assertion
  "I am a witch."
  witchSelfIdentificationPredicates
  "finite DASHI self-identification specimen; no universal claim about people using the term witch"

------------------------------------------------------------------------
-- 2. Fine identity states collapse to one public sentence.
------------------------------------------------------------------------

data WitchIdentityState : Set where
  wiccanReligiousIdentity
  paganNonWiccanIdentity
  feministPoliticalReclamation
  artisticSymbolicIdentity
  eclecticSpiritualIdentity
  historicalReenactmentUse
  : WitchIdentityState

data WitchSentenceSurface : Set where
  iAmAWitchSurface : WitchSentenceSurface

data WitchUseCode : Set where
  wiccanCode paganCode feministCode artisticCode eclecticCode reenactmentCode : WitchUseCode

witchSentence : WitchIdentityState → WitchSentenceSurface
witchSentence wiccanReligiousIdentity = iAmAWitchSurface
witchSentence paganNonWiccanIdentity = iAmAWitchSurface
witchSentence feministPoliticalReclamation = iAmAWitchSurface
witchSentence artisticSymbolicIdentity = iAmAWitchSurface
witchSentence eclecticSpiritualIdentity = iAmAWitchSurface
witchSentence historicalReenactmentUse = iAmAWitchSurface

witchUse : WitchIdentityState → WitchUseCode
witchUse wiccanReligiousIdentity = wiccanCode
witchUse paganNonWiccanIdentity = paganCode
witchUse feministPoliticalReclamation = feministCode
witchUse artisticSymbolicIdentity = artisticCode
witchUse eclecticSpiritualIdentity = eclecticCode
witchUse historicalReenactmentUse = reenactmentCode

wiccanAndFeministUsesDiffer :
  witchUse wiccanReligiousIdentity ≡ witchUse feministPoliticalReclamation → ⊥
wiccanAndFeministUsesDiffer ()

sameSentenceCannotRecoverUse : INF.FactorsThrough witchSentence witchUse → ⊥
sameSentenceCannotRecoverUse =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      wiccanReligiousIdentity
      feministPoliticalReclamation
      refl
      wiccanAndFeministUsesDiffer)

------------------------------------------------------------------------
-- 3. Self-authority is coordinate-specific.
------------------------------------------------------------------------

data AuthorityClaimKind : Set where
  authorityToSelfDescribe
  authorityToDefineCommunity
  authorityToAssertGenealogy
  authorityToAssertMetaphysicalTruth
  authorityToClassifyHistoricalPersons
  : AuthorityClaimKind

data SelfDescriptionPromotesCommunityAuthority : Set where
data SelfDescriptionPromotesGenealogyAuthority : Set where
data SelfDescriptionPromotesMetaphysicalAuthority : Set where
data SelfDescriptionPromotesHistoricalClassificationAuthority : Set where

selfDescriptionDoesNotPromoteCommunityAuthority :
  SelfDescriptionPromotesCommunityAuthority → ⊥
selfDescriptionDoesNotPromoteCommunityAuthority ()

selfDescriptionDoesNotPromoteGenealogyAuthority :
  SelfDescriptionPromotesGenealogyAuthority → ⊥
selfDescriptionDoesNotPromoteGenealogyAuthority ()

selfDescriptionDoesNotPromoteMetaphysicalAuthority :
  SelfDescriptionPromotesMetaphysicalAuthority → ⊥
selfDescriptionDoesNotPromoteMetaphysicalAuthority ()

selfDescriptionDoesNotPromoteHistoricalClassificationAuthority :
  SelfDescriptionPromotesHistoricalClassificationAuthority → ⊥
selfDescriptionDoesNotPromoteHistoricalClassificationAuthority ()

------------------------------------------------------------------------
-- 4. PNF-style independent obligations.
------------------------------------------------------------------------

data SelfIdentificationObligationKind : Set where
  lexicalMeaningObligation
  affiliationObligation
  reclamationObligation
  metaphysicalCommitmentObligation
  practiceObligation
  communityMembershipObligation
  genealogyObligation
  selfAuthorityObligation
  historicalContinuityObligation
  : SelfIdentificationObligationKind

data SelfIdentificationStatus : Set where
  recoveredFromUtterance
  requiresIndependentReceipt
  unresolved
  nonidentifiableFromSentence
  : SelfIdentificationStatus

record SelfIdentificationAudit : Set where
  constructor self-identification-audit
  field
    obligation : SelfIdentificationObligationKind
    status : SelfIdentificationStatus
    reason : String

open SelfIdentificationAudit public

canonicalWitchSentenceAudit : List SelfIdentificationAudit
canonicalWitchSentenceAudit =
  self-identification-audit lexicalMeaningObligation recoveredFromUtterance
    "speaker applies the token witch to themself at the utterance time"
  ∷ self-identification-audit affiliationObligation nonidentifiableFromSentence
    "the sentence alone does not distinguish Wiccan, Pagan, eclectic, political or artistic use"
  ∷ self-identification-audit reclamationObligation nonidentifiableFromSentence
    "reclamation is a use/history coordinate, not recoverable from the words alone"
  ∷ self-identification-audit metaphysicalCommitmentObligation nonidentifiableFromSentence
    "the sentence alone does not establish supernatural commitments"
  ∷ self-identification-audit practiceObligation requiresIndependentReceipt
    "practice requires separate evidence or self-report"
  ∷ self-identification-audit communityMembershipObligation requiresIndependentReceipt
    "community membership is distinct from lexical self-description"
  ∷ self-identification-audit genealogyObligation requiresIndependentReceipt
    "historical lineage requires source-bounded evidence"
  ∷ self-identification-audit selfAuthorityObligation recoveredFromUtterance
    "the speaker is the source of the present self-description; this does not expand authority to other coordinates"
  ∷ self-identification-audit historicalContinuityObligation unresolved
    "present identity does not by itself reconstruct prior historical identity"
  ∷ []

------------------------------------------------------------------------
-- 5. Explicit no-promotion gates.
------------------------------------------------------------------------

data WitchSentencePromotesWiccanAffiliation : Set where
data WitchSentencePromotesMetaphysicalCommitment : Set where
data WitchSentencePromotesRitualPractice : Set where
data WitchSentencePromotesCommunityMembership : Set where
data WitchSentencePromotesAncientGenealogy : Set where
data WitchSentencePromotesFeministPolitics : Set where
data PresentIdentityPromotesChildhoodFormationRoute : Set where

witchSentenceDoesNotPromoteWiccanAffiliation : WitchSentencePromotesWiccanAffiliation → ⊥
witchSentenceDoesNotPromoteWiccanAffiliation ()

witchSentenceDoesNotPromoteMetaphysicalCommitment : WitchSentencePromotesMetaphysicalCommitment → ⊥
witchSentenceDoesNotPromoteMetaphysicalCommitment ()

witchSentenceDoesNotPromoteRitualPractice : WitchSentencePromotesRitualPractice → ⊥
witchSentenceDoesNotPromoteRitualPractice ()

witchSentenceDoesNotPromoteCommunityMembership : WitchSentencePromotesCommunityMembership → ⊥
witchSentenceDoesNotPromoteCommunityMembership ()

witchSentenceDoesNotPromoteAncientGenealogy : WitchSentencePromotesAncientGenealogy → ⊥
witchSentenceDoesNotPromoteAncientGenealogy ()

witchSentenceDoesNotPromoteFeministPolitics : WitchSentencePromotesFeministPolitics → ⊥
witchSentenceDoesNotPromoteFeministPolitics ()

presentIdentityDoesNotPromoteChildhoodFormationRoute : PresentIdentityPromotesChildhoodFormationRoute → ⊥
presentIdentityDoesNotPromoteChildhoodFormationRoute ()

------------------------------------------------------------------------
-- 6. Weld to symbolic inversion / Wicca-feminist boundaries.
------------------------------------------------------------------------

record WitchSelfIdentificationWeld : Set where
  constructor witch-self-identification-weld
  field
    symbolicBoundary : Symbol.SymbolicInversionAuthorityTransferBoundary
    feministWiccaBoundary : FW.ReligiousSanctionFeministWiccaBoundary
    sameSentenceUseNonfactorability : INF.FactorsThrough witchSentence witchUse → ⊥
    wittgensteinSourceRecovered : Bool
    wittgensteinPropositionAttributed : Bool

canonicalWitchSelfIdentificationWeld : WitchSelfIdentificationWeld
canonicalWitchSelfIdentificationWeld = witch-self-identification-weld
  Symbol.canonicalSymbolicInversionAuthorityTransferBoundary
  FW.canonicalReligiousSanctionFeministWiccaBoundary
  sameSentenceCannotRecoverUse
  false false

record WitchSelfIdentificationBoundary : Set where
  constructor witch-self-identification-boundary
  field
    sameSentenceDeterminesSameUse : Bool
    witchMeansWiccanByDefault : Bool
    witchMeansFeministByDefault : Bool
    selfDescriptionDeterminesMetaphysics : Bool
    selfDescriptionDeterminesPractice : Bool
    selfDescriptionDeterminesCommunityMembership : Bool
    selfDescriptionDeterminesHistoricalGenealogy : Bool
    presentIdentityDeterminesChildhoodRoute : Bool
    selfAuthorityExtendsToHistoricalPersons : Bool
    lexicalMeaningDependsOnUseCoordinates : Bool
    unrecoveredWittgensteinSourceIsNotCited : Bool

canonicalWitchSelfIdentificationBoundary : WitchSelfIdentificationBoundary
canonicalWitchSelfIdentificationBoundary =
  witch-self-identification-boundary
    false false false false false false false false false true true
