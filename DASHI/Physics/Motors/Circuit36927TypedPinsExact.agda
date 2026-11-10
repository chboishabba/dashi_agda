module DASHI.Physics.Motors.Circuit36927TypedPinsExact where

------------------------------------------------------------------------
-- Finite pin witness layer for the generic circuit model.
-- It disallows out-of-range part IDs and pin IDs *by construction*.
-- Source-selected physical connectivity is a separate claim.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
import Agda.Builtin.Fin as F

record FiniteParts : Set₁ where
  constructor finiteParts
  field
    partCount : Nat
    pinCount : F.Fin partCount → Nat

record ValidPort (p : FiniteParts) : Set where
  constructor validPort
  open FiniteParts p
  field
    partIndex : F.Fin partCount
    pinIndex : F.Fin (pinCount partIndex)

record ValidWire (p : FiniteParts) : Set where
  constructor validWire
  field
    from : ValidPort p
    to : ValidPort p

-- Identity of selected valid endpoints is preserved by a wire flip.
reverseWire : ∀ {p} → ValidWire p → ValidWire p
reverseWire (validWire a b) = validWire b a

doubleReverseWire : ∀ {p} (w : ValidWire p) →
  reverseWire (reverseWire w) ≡ w
doubleReverseWire (validWire a b) = refl

record TypedNetlist (p : FiniteParts) : Set where
  constructor typedNetlist
  field
    wireCount : Nat
    wires : F.Fin wireCount → ValidWire p

-- The indexed declaration alone cannot establish that the source is
-- real or that ports are electrically compatible. It does guarantee
-- no reference can be made to an out-of-range part/pin index.
