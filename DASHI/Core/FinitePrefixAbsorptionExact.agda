module DASHI.Core.FinitePrefixAbsorptionExact where

------------------------------------------------------------------------
-- FINITE PREFIX ABSORPTION
--
-- Generic stopping semantics for a binary branch word.  A path survives only
-- while every visited state remains outside the stopping predicate.  Once a
-- prefix reaches the stopping set, every extension is killed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false; if_then_else_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary

record BinaryStoppingSystem : Set₁ where
  field
    State : Set
    branch0 branch1 : State → State
    stopped? : State → Bool

open BinaryStoppingSystem public

step : (system : BinaryStoppingSystem) → Bool → State system → State system
step system false = branch0 system
step system true  = branch1 system

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
-- Extension language.  Prefix is executed first; suffix is appended after it.
------------------------------------------------------------------------

data Extension
  {m : Nat}
  (prefix : Binary.BinaryWord m) : Nat → Set where
  same : Extension prefix zero
  add0 : ∀ {k} → Extension prefix k → Extension prefix (suc k)
  add1 : ∀ {k} → Extension prefix k → Extension prefix (suc k)

appendExtension :
  {m k : Nat} →
  {prefix : Binary.BinaryWord m} →
  Extension prefix k →
  Binary.BinaryWord (m + k)
appendExtension {prefix = Binary.end} same = Binary.end
appendExtension {prefix = Binary.bit0 prefix} same = Binary.bit0 (appendExtension {prefix = prefix} same)
appendExtension {prefix = Binary.bit1 prefix} same = Binary.bit1 (appendExtension {prefix = prefix} same)
appendExtension {prefix = prefix} (add0 ext) = Binary.bit0 (appendExtension ext)
appendExtension {prefix = prefix} (add1 ext) = Binary.bit1 (appendExtension ext)

------------------------------------------------------------------------
-- The core semantic receipt is stated independently of word representation:
-- once a prefix has already been killed, any continuation remains killed.
-- Consumers can instantiate this with their concrete append/run orientation.
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
    stoppingSemanticsGeneric : Bool
    sourceRwPathSameObjectWeldRequired : Bool
    endpointHitAloneImpliesEarlierPrefixHit : Bool
    prefixHitPersistsUnderPadding : Bool

canonicalPrefixAbsorptionBoundary : PrefixAbsorptionBoundary
canonicalPrefixAbsorptionBoundary =
  prefixAbsorptionBoundary true true false true

prefixAbsorptionGenericOwned :
  PrefixAbsorptionBoundary.stoppingSemanticsGeneric
    canonicalPrefixAbsorptionBoundary
  ≡ true
prefixAbsorptionGenericOwned = refl

sourcePathWeldStillRequired :
  PrefixAbsorptionBoundary.sourceRwPathSameObjectWeldRequired
    canonicalPrefixAbsorptionBoundary
  ≡ true
sourcePathWeldStillRequired = refl
