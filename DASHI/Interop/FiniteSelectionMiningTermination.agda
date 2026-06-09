module DASHI.Interop.FiniteSelectionMiningTermination where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat using (_≤_; z≤n; s≤s)

------------------------------------------------------------------------
-- Finite selection/mining termination receipt.
--
-- This is a concrete finite DASHI interop witness: a generator emits a
-- finite list of artifact states, a canonical selector chooses the minimal
-- score representative, and the canonical transition has a Nat-valued
-- Lyapunov score L that never increases.  The crank-mining words below are
-- deliberately recorded only as imported JMD bridge vocabulary.  They are
-- not promoted as DASHI theorem content and are not Clay promotion evidence.

data Artifact : Set where
  rawArtifact :
    Artifact

  selectedArtifact :
    Artifact

  minedFixedArtifact :
    Artifact

L :
  Artifact → Nat
L rawArtifact =
  suc (suc zero)
L selectedArtifact =
  suc zero
L minedFixedArtifact =
  zero

generatorCandidates :
  List Artifact
generatorCandidates =
  rawArtifact ∷ selectedArtifact ∷ minedFixedArtifact ∷ []

better :
  Artifact → Artifact → Artifact
better minedFixedArtifact _ =
  minedFixedArtifact
better selectedArtifact minedFixedArtifact =
  minedFixedArtifact
better selectedArtifact _ =
  selectedArtifact
better rawArtifact candidate =
  candidate

bestCandidate :
  List Artifact → Artifact
bestCandidate [] =
  rawArtifact
bestCandidate (candidate ∷ candidates) =
  better candidate (bestCandidate candidates)

canonicalSelectedResult :
  Artifact
canonicalSelectedResult =
  bestCandidate generatorCandidates

canonicalSelectedResultIsMined :
  canonicalSelectedResult ≡ minedFixedArtifact
canonicalSelectedResultIsMined =
  refl

canonicalTransition :
  Artifact → Artifact
canonicalTransition rawArtifact =
  selectedArtifact
canonicalTransition selectedArtifact =
  minedFixedArtifact
canonicalTransition minedFixedArtifact =
  minedFixedArtifact

L-nonincrease :
  (artifact : Artifact) →
  L (canonicalTransition artifact) ≤ L artifact
L-nonincrease rawArtifact =
  s≤s z≤n
L-nonincrease selectedArtifact =
  z≤n
L-nonincrease minedFixedArtifact =
  z≤n

iterate :
  {A : Set} →
  (A → A) → Nat → A → A
iterate step zero value =
  value
iterate step (suc n) value =
  iterate step n (step value)

twoStepCanonicalMining :
  Artifact
twoStepCanonicalMining =
  iterate canonicalTransition (suc (suc zero)) rawArtifact

twoStepCanonicalMiningReachesFixed :
  twoStepCanonicalMining ≡ minedFixedArtifact
twoStepCanonicalMiningReachesFixed =
  refl

minedFixedArtifactIsFixed :
  canonicalTransition minedFixedArtifact ≡ minedFixedArtifact
minedFixedArtifactIsFixed =
  refl

rawToSelectedNonincrease :
  L selectedArtifact ≤ L rawArtifact
rawToSelectedNonincrease =
  L-nonincrease rawArtifact

selectedToMinedNonincrease :
  L minedFixedArtifact ≤ L selectedArtifact
selectedToMinedNonincrease =
  L-nonincrease selectedArtifact

minedToMinedNonincrease :
  L minedFixedArtifact ≤ L minedFixedArtifact
minedToMinedNonincrease =
  L-nonincrease minedFixedArtifact

record CanonicalFiniteFixedPoint : Set where
  field
    initialArtifact :
      Artifact

    selectedResult :
      Artifact

    fixedPoint :
      Artifact

    finiteBound :
      Nat

    selectedResultCanonical :
      selectedResult ≡ canonicalSelectedResult

    selectedResultIsFixedPoint :
      selectedResult ≡ fixedPoint

    fixedPointReached :
      iterate canonicalTransition finiteBound initialArtifact ≡ fixedPoint

    fixedPointStable :
      canonicalTransition fixedPoint ≡ fixedPoint

    initialStepLNonincrease :
      L (canonicalTransition initialArtifact) ≤ L initialArtifact

    selectedStepLNonincrease :
      L (canonicalTransition selectedArtifact) ≤ L selectedArtifact

    fixedStepLNonincrease :
      L (canonicalTransition fixedPoint) ≤ L fixedPoint

open CanonicalFiniteFixedPoint public

canonicalFiniteFixedPoint :
  CanonicalFiniteFixedPoint
canonicalFiniteFixedPoint =
  record
    { initialArtifact =
        rawArtifact
    ; selectedResult =
        canonicalSelectedResult
    ; fixedPoint =
        minedFixedArtifact
    ; finiteBound =
        suc (suc zero)
    ; selectedResultCanonical =
        refl
    ; selectedResultIsFixedPoint =
        refl
    ; fixedPointReached =
        twoStepCanonicalMiningReachesFixed
    ; fixedPointStable =
        minedFixedArtifactIsFixed
    ; initialStepLNonincrease =
        L-nonincrease rawArtifact
    ; selectedStepLNonincrease =
        L-nonincrease selectedArtifact
    ; fixedStepLNonincrease =
        L-nonincrease minedFixedArtifact
    }

data ImportedBridgeVocabulary : Set where
  jmdCrankMiningVocabulary :
    ImportedBridgeVocabulary

importedBridgeVocabulary :
  List ImportedBridgeVocabulary
importedBridgeVocabulary =
  jmdCrankMiningVocabulary ∷ []

record MiningGovernanceBoundary : Set where
  field
    vocabularySource :
      String

    vocabularyBoundary :
      String

    boundaryFiniteSelectionTerminates :
      Bool

    boundaryFiniteSelectionTerminatesIsTrue :
      boundaryFiniteSelectionTerminates ≡ true

    boundaryJmdCrankMiningVocabularyImported :
      Bool

    boundaryJmdCrankMiningVocabularyImportedIsTrue :
      boundaryJmdCrankMiningVocabularyImported ≡ true

    boundaryCrankMiningPromotedAsDASHIClaim :
      Bool

    boundaryCrankMiningPromotedAsDASHIClaimIsFalse :
      boundaryCrankMiningPromotedAsDASHIClaim ≡ false

    boundaryClayPromotion :
      Bool

    boundaryClayPromotionIsFalse :
      boundaryClayPromotion ≡ false

open MiningGovernanceBoundary public

finiteSelectionTerminates :
  Bool
finiteSelectionTerminates =
  true

finiteSelectionTerminatesIsTrue :
  finiteSelectionTerminates ≡ true
finiteSelectionTerminatesIsTrue =
  refl

jmdCrankMiningVocabularyImported :
  Bool
jmdCrankMiningVocabularyImported =
  true

jmdCrankMiningVocabularyImportedIsTrue :
  jmdCrankMiningVocabularyImported ≡ true
jmdCrankMiningVocabularyImportedIsTrue =
  refl

crankMiningPromotedAsDASHIClaim :
  Bool
crankMiningPromotedAsDASHIClaim =
  false

crankMiningPromotedAsDASHIClaimIsFalse :
  crankMiningPromotedAsDASHIClaim ≡ false
crankMiningPromotedAsDASHIClaimIsFalse =
  refl

clayPromotion :
  Bool
clayPromotion =
  false

clayPromotionIsFalse :
  clayPromotion ≡ false
clayPromotionIsFalse =
  refl

miningGovernanceBoundary :
  MiningGovernanceBoundary
miningGovernanceBoundary =
  record
    { vocabularySource =
        "JMD bridge vocabulary"
    ; vocabularyBoundary =
        "crank mining is imported vocabulary only, not DASHI theorem promotion"
    ; boundaryFiniteSelectionTerminates =
        finiteSelectionTerminates
    ; boundaryFiniteSelectionTerminatesIsTrue =
        finiteSelectionTerminatesIsTrue
    ; boundaryJmdCrankMiningVocabularyImported =
        jmdCrankMiningVocabularyImported
    ; boundaryJmdCrankMiningVocabularyImportedIsTrue =
        jmdCrankMiningVocabularyImportedIsTrue
    ; boundaryCrankMiningPromotedAsDASHIClaim =
        crankMiningPromotedAsDASHIClaim
    ; boundaryCrankMiningPromotedAsDASHIClaimIsFalse =
        crankMiningPromotedAsDASHIClaimIsFalse
    ; boundaryClayPromotion =
        clayPromotion
    ; boundaryClayPromotionIsFalse =
        clayPromotionIsFalse
    }

record FiniteSelectionMiningTerminationReceipt : Set where
  field
    candidates :
      List Artifact

    candidatesAreCanonical :
      candidates ≡ generatorCandidates

    selected :
      Artifact

    selectedIsCanonicalBest :
      selected ≡ canonicalSelectedResult

    terminationWitness :
      CanonicalFiniteFixedPoint

    governanceBoundary :
      MiningGovernanceBoundary

open FiniteSelectionMiningTerminationReceipt public

finiteSelectionMiningTerminationReceipt :
  FiniteSelectionMiningTerminationReceipt
finiteSelectionMiningTerminationReceipt =
  record
    { candidates =
        generatorCandidates
    ; candidatesAreCanonical =
        refl
    ; selected =
        canonicalSelectedResult
    ; selectedIsCanonicalBest =
        refl
    ; terminationWitness =
        canonicalFiniteFixedPoint
    ; governanceBoundary =
        miningGovernanceBoundary
    }
