module DASHI.Interop.FiberedCrankDASHISystem where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Small local order surface.

data _≤_ : Nat → Nat → Set where
  z≤n : {n : Nat} → zero ≤ n
  s≤s : {m n : Nat} → m ≤ n → suc m ≤ suc n

------------------------------------------------------------------------
-- JMD bridge vocabulary boundary.
--
-- The crank/protagonist words are vocabulary imported from the JMD bridge
-- surface.  This module keeps them as bridge terms only; it does not promote
-- them to DASHI semantic claims, theorem claims, or authority claims.

data JMDBridgeVocabularyTerm : Set where
  jmdCrankBridgeVocabulary :
    JMDBridgeVocabularyTerm

  jmdProtagonistBridgeVocabulary :
    JMDBridgeVocabularyTerm

data BridgeVocabularySource : Set where
  importedJMDBridgeVocabulary :
    BridgeVocabularySource

data DASHIPromotionStatus : Set where
  bridgeVocabularyOnly :
    DASHIPromotionStatus

  promotedDASHIClaimBlocked :
    DASHIPromotionStatus

record JMDTermNonClaimGuard
  (term : JMDBridgeVocabularyTerm) : Set where
  field
    source :
      BridgeVocabularySource

    sourceIsImportedJMDBridgeVocabulary :
      source ≡ importedJMDBridgeVocabulary

    status :
      DASHIPromotionStatus

    statusIsBridgeVocabularyOnly :
      status ≡ bridgeVocabularyOnly

    promotedAsDASHIClaim :
      Bool

    promotedAsDASHIClaimIsFalse :
      promotedAsDASHIClaim ≡ false

open JMDTermNonClaimGuard public

crankNonClaimGuard :
  JMDTermNonClaimGuard jmdCrankBridgeVocabulary
crankNonClaimGuard =
  record
    { source =
        importedJMDBridgeVocabulary
    ; sourceIsImportedJMDBridgeVocabulary =
        refl
    ; status =
        bridgeVocabularyOnly
    ; statusIsBridgeVocabularyOnly =
        refl
    ; promotedAsDASHIClaim =
        false
    ; promotedAsDASHIClaimIsFalse =
        refl
    }

protagonistNonClaimGuard :
  JMDTermNonClaimGuard jmdProtagonistBridgeVocabulary
protagonistNonClaimGuard =
  record
    { source =
        importedJMDBridgeVocabulary
    ; sourceIsImportedJMDBridgeVocabulary =
        refl
    ; status =
        bridgeVocabularyOnly
    ; statusIsBridgeVocabularyOnly =
        refl
    ; promotedAsDASHIClaim =
        false
    ; promotedAsDASHIClaimIsFalse =
        refl
    }

jmdCrankTermPromotedToDASHIClaim :
  Bool
jmdCrankTermPromotedToDASHIClaim =
  false

jmdCrankTermPromotedToDASHIClaimIsFalse :
  jmdCrankTermPromotedToDASHIClaim ≡ false
jmdCrankTermPromotedToDASHIClaimIsFalse =
  refl

jmdProtagonistTermPromotedToDASHIClaim :
  Bool
jmdProtagonistTermPromotedToDASHIClaim =
  false

jmdProtagonistTermPromotedToDASHIClaimIsFalse :
  jmdProtagonistTermPromotedToDASHIClaim ≡ false
jmdProtagonistTermPromotedToDASHIClaimIsFalse =
  refl

fiberedCrankDASHIPromotesJMDTerms :
  Bool
fiberedCrankDASHIPromotesJMDTerms =
  false

fiberedCrankDASHIPromotesJMDTermsIsFalse :
  fiberedCrankDASHIPromotesJMDTerms ≡ false
fiberedCrankDASHIPromotesJMDTermsIsFalse =
  refl

fiberedCrankDASHIFailClosedSummary :
  String
fiberedCrankDASHIFailClosedSummary =
  "fail-closed: crank and protagonist remain imported JMD bridge vocabulary; no JMD term is promoted as a DASHI claim"

------------------------------------------------------------------------
-- Fibered crank DASHI core.

record VerticalTransformPreservation
  {Artifact Semantic : Set}
  (projection : Artifact → Semantic)
  (Candidate : Artifact → Set)
  (generate : (artifact : Artifact) → Candidate artifact)
  (Score : {artifact : Artifact} → Candidate artifact → Nat)
  (Witness : (artifact : Artifact) → Candidate artifact → Set)
  (Invariant : Semantic → Set)
  (observe : (artifact : Artifact) → Invariant (projection artifact))
  (source target : Artifact) : Set where
  field
    semanticPreserved :
      projection source ≡ projection target

    scoreMonotone :
      Score (generate source) ≤ Score (generate target)

    witnessPreserved :
      Witness source (generate source) →
      Witness target (generate target)

    invariantObservedAfterTransform :
      Invariant (projection target)

open VerticalTransformPreservation public

record FiberedCrankDASHISystem : Set₁ where
  field
    Artifact :
      Set

    Semantic :
      Set

    projection :
      Artifact → Semantic

    Candidate :
      Artifact → Set

    generate :
      (artifact : Artifact) → Candidate artifact

    Score :
      {artifact : Artifact} → Candidate artifact → Nat

    Witness :
      (artifact : Artifact) → Candidate artifact → Set

    Authority :
      Set

    Invariant :
      Semantic → Set

    observe :
      (artifact : Artifact) → Invariant (projection artifact)

    VerticalTransform :
      Artifact → Artifact → Set

    verticalTransformPreservation :
      {source target : Artifact} →
      VerticalTransform source target →
      VerticalTransformPreservation
        projection Candidate generate Score Witness Invariant observe
        source target

    crankTermGuard :
      JMDTermNonClaimGuard jmdCrankBridgeVocabulary

    protagonistTermGuard :
      JMDTermNonClaimGuard jmdProtagonistBridgeVocabulary

open FiberedCrankDASHISystem public

------------------------------------------------------------------------
-- Concrete finite Bool-like instance.

data BitArtifact : Set where
  bitFalse :
    BitArtifact

  bitTrue :
    BitArtifact

BitSemantic :
  Set
BitSemantic =
  BitArtifact

constantBitProjection :
  BitArtifact → BitSemantic
constantBitProjection bitFalse =
  bitFalse
constantBitProjection bitTrue =
  bitFalse

data BitCandidate : BitArtifact → Set where
  generatedBitCandidate :
    {artifact : BitArtifact} →
    BitCandidate artifact

generateBitCandidate :
  (artifact : BitArtifact) → BitCandidate artifact
generateBitCandidate artifact =
  generatedBitCandidate

bitScore :
  {artifact : BitArtifact} →
  BitCandidate artifact →
  Nat
bitScore {bitFalse} generatedBitCandidate =
  zero
bitScore {bitTrue} generatedBitCandidate =
  suc zero

bitWitness :
  (artifact : BitArtifact) →
  BitCandidate artifact →
  Set
bitWitness artifact candidate =
  ⊤

BitAuthority :
  Set
BitAuthority =
  ⊤

bitInvariant :
  BitSemantic → Set
bitInvariant semantic =
  ⊤

observeBitInvariant :
  (artifact : BitArtifact) →
  bitInvariant (constantBitProjection artifact)
observeBitInvariant artifact =
  tt

data BitVerticalTransform : BitArtifact → BitArtifact → Set where
  stayFalse :
    BitVerticalTransform bitFalse bitFalse

  raiseFalseToTrue :
    BitVerticalTransform bitFalse bitTrue

  stayTrue :
    BitVerticalTransform bitTrue bitTrue

bitScoreStayFalseMonotone :
  bitScore (generateBitCandidate bitFalse) ≤
  bitScore (generateBitCandidate bitFalse)
bitScoreStayFalseMonotone =
  z≤n

bitScoreRaiseMonotone :
  bitScore (generateBitCandidate bitFalse) ≤
  bitScore (generateBitCandidate bitTrue)
bitScoreRaiseMonotone =
  z≤n

bitScoreStayTrueMonotone :
  bitScore (generateBitCandidate bitTrue) ≤
  bitScore (generateBitCandidate bitTrue)
bitScoreStayTrueMonotone =
  s≤s z≤n

bitVerticalTransformPreservation :
  {source target : BitArtifact} →
  BitVerticalTransform source target →
  VerticalTransformPreservation
    constantBitProjection
    BitCandidate
    generateBitCandidate
    bitScore
    bitWitness
    bitInvariant
    observeBitInvariant
    source
    target
bitVerticalTransformPreservation stayFalse =
  record
    { semanticPreserved =
        refl
    ; scoreMonotone =
        bitScoreStayFalseMonotone
    ; witnessPreserved =
        λ witness → witness
    ; invariantObservedAfterTransform =
        tt
    }
bitVerticalTransformPreservation raiseFalseToTrue =
  record
    { semanticPreserved =
        refl
    ; scoreMonotone =
        bitScoreRaiseMonotone
    ; witnessPreserved =
        λ witness → witness
    ; invariantObservedAfterTransform =
        tt
    }
bitVerticalTransformPreservation stayTrue =
  record
    { semanticPreserved =
        refl
    ; scoreMonotone =
        bitScoreStayTrueMonotone
    ; witnessPreserved =
        λ witness → witness
    ; invariantObservedAfterTransform =
        tt
    }

concreteFiniteBoolLikeFiberedCrankDASHISystem :
  FiberedCrankDASHISystem
concreteFiniteBoolLikeFiberedCrankDASHISystem =
  record
    { Artifact =
        BitArtifact
    ; Semantic =
        BitSemantic
    ; projection =
        constantBitProjection
    ; Candidate =
        BitCandidate
    ; generate =
        generateBitCandidate
    ; Score =
        bitScore
    ; Witness =
        bitWitness
    ; Authority =
        BitAuthority
    ; Invariant =
        bitInvariant
    ; observe =
        observeBitInvariant
    ; VerticalTransform =
        BitVerticalTransform
    ; verticalTransformPreservation =
        bitVerticalTransformPreservation
    ; crankTermGuard =
        crankNonClaimGuard
    ; protagonistTermGuard =
        protagonistNonClaimGuard
    }

concreteFiniteInstanceUsesConstantProjection :
  Bool
concreteFiniteInstanceUsesConstantProjection =
  true

concreteFiniteInstanceUsesConstantProjectionIsTrue :
  concreteFiniteInstanceUsesConstantProjection ≡ true
concreteFiniteInstanceUsesConstantProjectionIsTrue =
  refl

concreteFiniteInstanceScoreMonotoneInhabited :
  Bool
concreteFiniteInstanceScoreMonotoneInhabited =
  true

concreteFiniteInstanceScoreMonotoneInhabitedIsTrue :
  concreteFiniteInstanceScoreMonotoneInhabited ≡ true
concreteFiniteInstanceScoreMonotoneInhabitedIsTrue =
  refl

fiberedCrankDASHIControlCard :
  String
fiberedCrankDASHIControlCard =
  "O: FiberedCrankDASHISystem; R: nonclaim JMD bridge vocabulary; C: finite Bool-like constant projection instance; S: vertical transform semantics preservation and score monotone; L: JMD terms unpromoted; P: fail-closed guards; G: no promotion index edit; F: Agda typecheck target"
