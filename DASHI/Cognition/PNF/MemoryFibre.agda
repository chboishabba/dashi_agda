module DASHI.Cognition.PNF.MemoryFibre where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List)

import DASHI.Cognition.PNF.EventAlgebra as PNF

record MemoryFibre : Set where
  constructor memoryFibre
  field
    rememberedEvent : PNF.EventPNF
    valuation salience memoryConfidence phase actionWeight : Nat
    retrievalPolicy actionBias memoryProvenance : String

open MemoryFibre public

revalue : MemoryFibre → Nat → MemoryFibre
revalue memory newValuation =
  memoryFibre
    (rememberedEvent memory)
    newValuation
    (salience memory)
    (memoryConfidence memory)
    (phase memory)
    (actionWeight memory)
    (retrievalPolicy memory)
    (actionBias memory)
    (memoryProvenance memory)

habituate : MemoryFibre → MemoryFibre
habituate memory =
  memoryFibre
    (rememberedEvent memory)
    (valuation memory)
    zero
    (memoryConfidence memory)
    (phase memory)
    (actionWeight memory)
    (retrievalPolicy memory)
    (actionBias memory)
    (memoryProvenance memory)

reinforce : MemoryFibre → MemoryFibre
reinforce memory =
  memoryFibre
    (rememberedEvent memory)
    (valuation memory)
    (salience memory)
    (memoryConfidence memory)
    (phase memory)
    (suc (actionWeight memory))
    (retrievalPolicy memory)
    (actionBias memory)
    (memoryProvenance memory)

extinguishActionDominance : MemoryFibre → MemoryFibre
extinguishActionDominance memory =
  memoryFibre
    (rememberedEvent memory)
    (valuation memory)
    (salience memory)
    (memoryConfidence memory)
    (phase memory)
    zero
    (retrievalPolicy memory)
    "association retained; action projection inhibited"
    (memoryProvenance memory)

realignPhase : MemoryFibre → Nat → MemoryFibre
realignPhase memory newPhase =
  memoryFibre
    (rememberedEvent memory)
    (valuation memory)
    (salience memory)
    (memoryConfidence memory)
    newPhase
    (actionWeight memory)
    (retrievalPolicy memory)
    (actionBias memory)
    (memoryProvenance memory)

revaluePreservesRememberedEvent :
  ∀ memory value → rememberedEvent (revalue memory value) ≡ rememberedEvent memory
revaluePreservesRememberedEvent memory value = refl

habituationPreservesRememberedEvent :
  ∀ memory → rememberedEvent (habituate memory) ≡ rememberedEvent memory
habituationPreservesRememberedEvent memory = refl

extinctionPreservesRememberedEvent :
  ∀ memory →
  rememberedEvent (extinguishActionDominance memory) ≡ rememberedEvent memory
extinctionPreservesRememberedEvent memory = refl

record VersionedMemory : Set where
  constructor versionedMemory
  field
    current : MemoryFibre
    semanticRevisions : List PNF.PNFRevision
    priorMemoryStates : List MemoryFibre
    overwriteForbidden : Bool
    overwriteForbiddenIsTrue : overwriteForbidden ≡ true

open VersionedMemory public

record ExpectationFibre : Set where
  constructor expectationFibre
  field
    expectedEvent : PNF.EventPNF
    horizon expectationConfidence : Nat
    expectationContext evidenceBasis attributionMode : String

open ExpectationFibre public

data BeliefPNF : Nat → Set where
  baseBelief : PNF.EventPNF → BeliefPNF zero
  believedBy : ∀ {depth} → String → BeliefPNF depth → BeliefPNF (suc depth)

record BoundedCommonBelief : Set where
  constructor boundedCommonBelief
  field
    groupMembers : List String
    maximumDepth : Nat
    compressedRepresentative : PNF.EventPNF
    compressionReceipt : String
    exactInfiniteCommonKnowledgeClaimed : Bool
    exactInfiniteCommonKnowledgeClaimedIsFalse :
      exactInfiniteCommonKnowledgeClaimed ≡ false

open BoundedCommonBelief public
