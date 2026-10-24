module DASHI.Mathematics.Complexity.GuardedCookVirtualTapeBaseExact where

------------------------------------------------------------------------
-- GUARDED COOK BITSTREAM AS AN IMMUTABLE VIRTUAL TAPE BASE
--
-- Layout matches the concrete guarded input convention:
--
--   T guard blanks ; boundary blank ; encoded formula bits ; remaining blanks.
--
-- Hence formula bit i lives at absolute address (T + 1) + i.  Reads outside
-- the available streamed bitstring are blank.  No complete formula list is
-- constructed here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Mathematics.Complexity.GuardedCookFormulaDescriptionExact as Description
import DASHI.Mathematics.Complexity.GuardedCookStreamingBitExact as Stream
import DASHI.Mathematics.Complexity.GuardedCookBitQuerySemanticsExact as Semantics
import DASHI.Mathematics.Complexity.VirtualTapeSparseOverlayExact as Overlay

------------------------------------------------------------------------
-- Remove a fixed left prefix from an absolute address.
------------------------------------------------------------------------

dropPrefix : Nat → Nat → Maybe Nat
dropPrefix zero address = just address
dropPrefix (suc prefix) zero = nothing
dropPrefix (suc prefix) (suc address) = dropPrefix prefix address

dropPrefixAtOffset :
  (prefix index : Nat) →
  dropPrefix prefix (prefix + index) ≡ just index
dropPrefixAtOffset zero index = refl
dropPrefixAtOffset (suc prefix) index =
  dropPrefixAtOffset prefix index

dropPrefixBeforeBoundary :
  (prefix : Nat) →
  dropPrefix (suc prefix) prefix ≡ nothing
dropPrefixBeforeBoundary zero = refl
dropPrefixBeforeBoundary (suc prefix) =
  dropPrefixBeforeBoundary prefix

payloadStart : Description.GuardedCookFormulaDescription → Nat
payloadStart description = suc (Description.steps description)

------------------------------------------------------------------------
-- Map streamed Boolean payload symbols into an arbitrary binary tape alphabet.
------------------------------------------------------------------------

boolSymbol :
  ∀ {Symbol : Set} →
  Symbol → Symbol → Bool → Symbol
boolSymbol zeroSymbol oneSymbol false = zeroSymbol
boolSymbol zeroSymbol oneSymbol true = oneSymbol

streamedPayloadCell :
  ∀ {Symbol : Set} →
  Symbol → Symbol → Symbol →
  Description.GuardedCookFormulaDescription →
  Nat → Maybe Symbol
streamedPayloadCell blank zeroSymbol oneSymbol description index
  with Stream.streamedQueryBit (Description.atIndex description index)
... | nothing = just blank
... | just bit = just (boolSymbol zeroSymbol oneSymbol bit)

guardedCookCell :
  ∀ {Symbol : Set} →
  Symbol → Symbol → Symbol →
  Description.GuardedCookFormulaDescription →
  Nat → Maybe Symbol
guardedCookCell blank zeroSymbol oneSymbol description address
  with dropPrefix (payloadStart description) address
... | nothing = just blank
... | just index =
  streamedPayloadCell blank zeroSymbol oneSymbol description index

guardedCookVirtualBase :
  ∀ {Symbol : Set} →
  Symbol → Symbol → Symbol →
  Description.GuardedCookFormulaDescription →
  Overlay.VirtualTapeBase Symbol
guardedCookVirtualBase blank zeroSymbol oneSymbol description = record
  { Overlay.baseRead =
      guardedCookCell blank zeroSymbol oneSymbol description
  }

------------------------------------------------------------------------
-- Exact payload-address theorem.
------------------------------------------------------------------------

guardedCookPayloadAddressExact :
  ∀ {Symbol : Set}
    (blank zeroSymbol oneSymbol : Symbol)
    (description : Description.GuardedCookFormulaDescription)
    (index : Nat) →
  Overlay.baseRead
      (guardedCookVirtualBase blank zeroSymbol oneSymbol description)
      (payloadStart description + index)
  ≡
  streamedPayloadCell blank zeroSymbol oneSymbol description index
guardedCookPayloadAddressExact blank zeroSymbol oneSymbol description index
  rewrite dropPrefixAtOffset (payloadStart description) index = refl

------------------------------------------------------------------------
-- Semantic read theorem: a canonical successful query is the exact untouched
-- tape symbol at the corresponding guarded payload address.
------------------------------------------------------------------------

guardedCookSemanticPayloadRead :
  ∀ {Symbol : Set}
    (blank zeroSymbol oneSymbol : Symbol)
    (description : Description.GuardedCookFormulaDescription)
    (index : Nat)
    (bit : Bool) →
  Semantics.queryAnswer (Description.atIndex description index) ≡ just bit →
  Overlay.baseRead
      (guardedCookVirtualBase blank zeroSymbol oneSymbol description)
      (payloadStart description + index)
  ≡ just (boolSymbol zeroSymbol oneSymbol bit)
guardedCookSemanticPayloadRead
    blank zeroSymbol oneSymbol description index bit semantic =
  step
  where
    streamed :
      Stream.streamedQueryBit (Description.atIndex description index)
      ≡ just bit
    streamed =
      trans
        (Stream.streamedQueryBitExact
          (Description.atIndex description index))
        semantic

    step :
      Overlay.baseRead
          (guardedCookVirtualBase blank zeroSymbol oneSymbol description)
          (payloadStart description + index)
      ≡ just (boolSymbol zeroSymbol oneSymbol bit)
    step
      rewrite guardedCookPayloadAddressExact
        blank zeroSymbol oneSymbol description index
            | streamed =
      refl

------------------------------------------------------------------------
-- Initial left guard/boundary reads are blank by construction.
------------------------------------------------------------------------

payloadBoundaryIsBlank :
  ∀ {Symbol : Set}
    (blank zeroSymbol oneSymbol : Symbol)
    (description : Description.GuardedCookFormulaDescription) →
  Overlay.baseRead
      (guardedCookVirtualBase blank zeroSymbol oneSymbol description)
      (Description.steps description)
  ≡ just blank
payloadBoundaryIsBlank blank zeroSymbol oneSymbol description
  rewrite dropPrefixBeforeBoundary (Description.steps description) =
  refl

------------------------------------------------------------------------
-- The mutable layer is deliberately separate: downstream candidate simulation
-- uses `VirtualTapeSparseOverlayExact.overlayRead`.  Thus later writes shadow a
-- payload address without mutating or rebuilding the Cook description/source.
------------------------------------------------------------------------
