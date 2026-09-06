module DASHI.Core.FinitePrefixAbsorptionExact where

------------------------------------------------------------------------
-- FINITE PREFIX ABSORPTION
--
-- Generic stopping semantics for a binary branch word. A path survives only
-- while every visited state remains outside the stopping predicate. Once a
-- prefix reaches the stopping set, every extension is killed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false; if_then_else_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary

record BinaryStoppingSystem : Set₁ where
  field
    State : Set
    branch0 branch1 : State → State
    stopped? : State → Bool

open BinaryStoppingSystem public

survives :
  (system : BinaryStoppingSystem) →
  {n : Nat} →
  Binary.BinaryWord n →
  State system →
  Bool
survives system Binary.end state =
  if stopped? system state then false else true
survives system (Binary.bit0 word) state with stopped? system state
... | true  = false
... | false = survives system word (branch0 system state)
survives system (Binary.bit1 word) state with stopped? system state
... | true  = false
... | false = survives system word (branch1 system state)

------------------------------------------------------------------------
-- Prefix-preserving word append. The left word executes first.
------------------------------------------------------------------------

appendWord :
  {m n : Nat} →
  Binary.BinaryWord m →
  Binary.BinaryWord n →
  Binary.BinaryWord (m + n)
appendWord Binary.end suffix = suffix
appendWord (Binary.bit0 prefix) suffix =
  Binary.bit0 (appendWord prefix suffix)
appendWord (Binary.bit1 prefix) suffix =
  Binary.bit1 (appendWord prefix suffix)

------------------------------------------------------------------------
-- Actual absorption theorem for the concrete recursive semantics.
------------------------------------------------------------------------

data Empty : Set where

emptyEliminate : ∀ {A : Set} → Empty → A
emptyEliminate ()

trueNotFalse : true ≡ false → Empty
trueNotFalse ()

stoppedNowKillsAny :
  (system : BinaryStoppingSystem) →
  {n : Nat} →
  (word : Binary.BinaryWord n) →
  (state : State system) →
  stopped? system state ≡ true →
  survives system word state ≡ false
stoppedNowKillsAny system Binary.end state stopped rewrite stopped = refl
stoppedNowKillsAny system (Binary.bit0 word) state stopped rewrite stopped = refl
stoppedNowKillsAny system (Binary.bit1 word) state stopped rewrite stopped = refl

killedPrefixKillsExtension :
  (system : BinaryStoppingSystem) →
  {m n : Nat} →
  (prefix : Binary.BinaryWord m) →
  (suffix : Binary.BinaryWord n) →
  (state : State system) →
  survives system prefix state ≡ false →
  survives system (appendWord prefix suffix) state ≡ false
killedPrefixKillsExtension system Binary.end suffix state killed
  with stopped? system state
... | true = stoppedNowKillsAny system suffix state refl
... | false = emptyEliminate (trueNotFalse killed)
killedPrefixKillsExtension system (Binary.bit0 prefix) suffix state killed
  with stopped? system state
... | true = refl
... | false =
  killedPrefixKillsExtension
    system prefix suffix (branch0 system state) killed
killedPrefixKillsExtension system (Binary.bit1 prefix) suffix state killed
  with stopped? system state
... | true = refl
... | false =
  killedPrefixKillsExtension
    system prefix suffix (branch1 system state) killed

------------------------------------------------------------------------
-- Abstract export shape for consumers with a different word representation.
------------------------------------------------------------------------

record PrefixAbsorptionReceipt : Set₁ where
  field
    State Word : Set
    killed : Word → State → Set
    extend : Word → Word → Word
    killedExtension :
      (prefix suffix : Word) →
      (state : State) →
      killed prefix state →
      killed (extend prefix suffix) state

open PrefixAbsorptionReceipt public

record PrefixAbsorptionBoundary : Set where
  constructor prefixAbsorptionBoundary
  field
    concreteRecursiveAbsorptionOwned : Bool
    sourceRwPathSameObjectWeldRequired : Bool
    endpointHitAloneImpliesEarlierPrefixHit : Bool
    prefixHitPersistsUnderPadding : Bool

canonicalPrefixAbsorptionBoundary : PrefixAbsorptionBoundary
canonicalPrefixAbsorptionBoundary =
  prefixAbsorptionBoundary true true false true

prefixAbsorptionGenericOwned :
  PrefixAbsorptionBoundary.concreteRecursiveAbsorptionOwned
    canonicalPrefixAbsorptionBoundary
  ≡ true
prefixAbsorptionGenericOwned = refl

sourcePathWeldStillRequired :
  PrefixAbsorptionBoundary.sourceRwPathSameObjectWeldRequired
    canonicalPrefixAbsorptionBoundary
  ≡ true
sourcePathWeldStillRequired = refl
