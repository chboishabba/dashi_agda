module DASHI.Core.RelationalTransportGroupoidActionExact where

------------------------------------------------------------------------
-- RELATIONAL TRANSPORT GROUPOID ACTION, EXTENSIONAL LAW SURFACE
--
-- DASHI CONTRIBUTION
--
-- RelationalSelfDescentExact already supplies invertible TypedTransport values,
-- but their source/target patches are record fields rather than type indices
-- and the record also retains proof/receipt data.  This module refines that
-- carrier to a genuinely source/target-indexed hom type:
--
--       RelTransportHom State A B
--
-- with identity, composition and inverse.
--
-- Equality of proof/receipt-bearing hom records is intentionally NOT forced.
-- Instead the category/groupoid laws are proved under the observationally
-- relevant extensional relation:
--
--       f ≈ g  iff  for every state x, forward f x = forward g x.
--
-- Thus this is an exact groupoid-action law surface on State, not yet a strict
-- record-equality groupoid object or a groupoid-valued presheaf.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.RelationalSelfDescentExact as Existing

------------------------------------------------------------------------
-- 1. Source/target-indexed invertible transport hom.
------------------------------------------------------------------------

record RelTransportHom
    (State : Set)
    (source target : Existing.RelationalPatch) : Set₁ where
  constructor rel-transport-hom
  field
    forward : State → State
    backward : State → State

    backwardAfterForward :
      (state : State) →
      backward (forward state) ≡ state

    forwardAfterBackward :
      (state : State) →
      forward (backward state) ≡ state

    receipt : String

open RelTransportHom public

fromExisting :
  {State : Set} →
  (transport : Existing.TypedTransport State) →
  RelTransportHom
    State
    (Existing.sourcePatch transport)
    (Existing.targetPatch transport)
fromExisting transport =
  rel-transport-hom
    (Existing.forward transport)
    (Existing.backward transport)
    (Existing.backwardAfterForward transport)
    (Existing.forwardAfterBackward transport)
    (Existing.transportReceipt transport)

------------------------------------------------------------------------
-- 2. Identity, inverse and composition.
------------------------------------------------------------------------

identityHom :
  {State : Set} →
  (patch : Existing.RelationalPatch) →
  RelTransportHom State patch patch
identityHom patch =
  rel-transport-hom
    (λ state → state)
    (λ state → state)
    (λ state → refl)
    (λ state → refl)
    "DASHI indexed identity transport"

inverseHom :
  {State : Set}
  {source target : Existing.RelationalPatch} →
  RelTransportHom State source target →
  RelTransportHom State target source
inverseHom hom =
  rel-transport-hom
    (backward hom)
    (forward hom)
    (forwardAfterBackward hom)
    (backwardAfterForward hom)
    "DASHI indexed inverse transport"

composeHom :
  {State : Set}
  {a b c : Existing.RelationalPatch} →
  RelTransportHom State b c →
  RelTransportHom State a b →
  RelTransportHom State a c
composeHom g f =
  rel-transport-hom
    (λ state → forward g (forward f state))
    (λ state → backward f (backward g state))
    backwardForward
    forwardBackward
    "DASHI indexed composed transport"
  where
    backwardForward :
      (state : State) →
      backward f
        (backward g
          (forward g
            (forward f state)))
      ≡ state
    backwardForward state
      rewrite backwardAfterForward g (forward f state)
            | backwardAfterForward f state
      = refl

    forwardBackward :
      (state : State) →
      forward g
        (forward f
          (backward f
            (backward g state)))
      ≡ state
    forwardBackward state
      rewrite forwardAfterBackward f (backward g state)
            | forwardAfterBackward g state
      = refl

------------------------------------------------------------------------
-- 3. Extensional equality of transport action.
------------------------------------------------------------------------

_≈_ :
  {State : Set}
  {source target : Existing.RelationalPatch} →
  RelTransportHom State source target →
  RelTransportHom State source target →
  Set
f ≈ g =
  (state : _) →
  forward f state ≡ forward g state

extensionalRefl :
  {State : Set}
  {source target : Existing.RelationalPatch}
  {f : RelTransportHom State source target} →
  f ≈ f
extensionalRefl state = refl

extensionalSym :
  {State : Set}
  {source target : Existing.RelationalPatch}
  {f g : RelTransportHom State source target} →
  f ≈ g →
  g ≈ f
extensionalSym proof state =
  sym (proof state)

extensionalTrans :
  {State : Set}
  {source target : Existing.RelationalPatch}
  {f g h : RelTransportHom State source target} →
  f ≈ g →
  g ≈ h →
  f ≈ h
extensionalTrans left right state =
  trans (left state) (right state)

------------------------------------------------------------------------
-- 4. Category laws modulo extensional action equality.
------------------------------------------------------------------------

leftIdentity :
  {State : Set}
  {a b : Existing.RelationalPatch}
  (f : RelTransportHom State a b) →
  composeHom (identityHom b) f ≈ f
leftIdentity f state = refl

rightIdentity :
  {State : Set}
  {a b : Existing.RelationalPatch}
  (f : RelTransportHom State a b) →
  composeHom f (identityHom a) ≈ f
rightIdentity f state = refl

associative :
  {State : Set}
  {a b c d : Existing.RelationalPatch}
  (h : RelTransportHom State c d) →
  (g : RelTransportHom State b c) →
  (f : RelTransportHom State a b) →
  composeHom h (composeHom g f)
  ≈
  composeHom (composeHom h g) f
associative h g f state = refl

------------------------------------------------------------------------
-- 5. Groupoid inverse laws modulo extensional action equality.
------------------------------------------------------------------------

inverseAfterForwardIsIdentity :
  {State : Set}
  {a b : Existing.RelationalPatch}
  (f : RelTransportHom State a b) →
  composeHom (inverseHom f) f
  ≈ identityHom a
inverseAfterForwardIsIdentity f state =
  backwardAfterForward f state

forwardAfterInverseIsIdentity :
  {State : Set}
  {a b : Existing.RelationalPatch}
  (f : RelTransportHom State a b) →
  composeHom f (inverseHom f)
  ≈ identityHom b
forwardAfterInverseIsIdentity f state =
  forwardAfterBackward f state

inverseInvolutiveAction :
  {State : Set}
  {a b : Existing.RelationalPatch}
  (f : RelTransportHom State a b) →
  inverseHom (inverseHom f) ≈ f
inverseInvolutiveAction f state = refl

------------------------------------------------------------------------
-- 6. Canonical existing transports embed without losing action.
------------------------------------------------------------------------

existingIdentityEmbeds :
  {State : Set}
  (source target : Existing.RelationalPatch) →
  fromExisting (Existing.identityTransport {State} source target)
  ≈
  rel-transport-hom
    (λ state → state)
    (λ state → state)
    (λ state → refl)
    (λ state → refl)
    "comparison identity"
existingIdentityEmbeds source target state = refl

------------------------------------------------------------------------
-- 7. Boundary.
------------------------------------------------------------------------

data ExtensionalTransportGroupoidIsStrictRecordEqualityGroupoid : Set where
data ExtensionalTransportGroupoidIsGroupoidValuedPresheaf : Set where

extensionalGroupoidDoesNotForceStrictRecordEquality :
  ExtensionalTransportGroupoidIsStrictRecordEqualityGroupoid → ⊥
extensionalGroupoidDoesNotForceStrictRecordEquality ()

extensionalGroupoidDoesNotYetCreatePresheaf :
  ExtensionalTransportGroupoidIsGroupoidValuedPresheaf → ⊥
extensionalGroupoidDoesNotYetCreatePresheaf ()

record RelationalTransportGroupoidActionBoundary : Set where
  constructor relational-transport-groupoid-action-boundary
  field
    sourceTargetIndexedHomConstructed : Bool
    identityConstructed : Bool
    compositionConstructed : Bool
    inverseConstructed : Bool
    extensionalEquivalenceConstructed : Bool
    leftRightIdentityProvedExtensionally : Bool
    associativityProvedExtensionally : Bool
    inverseLawsProvedExtensionally : Bool
    existingTypedTransportEmbeds : Bool
    strictRecordEqualityGroupoidClaimed : Bool
    groupoidValuedPresheafClaimed : Bool

canonicalRelationalTransportGroupoidActionBoundary :
  RelationalTransportGroupoidActionBoundary
canonicalRelationalTransportGroupoidActionBoundary =
  relational-transport-groupoid-action-boundary
    true
    true
    true
    true
    true
    true
    true
    true
    true
    false
    false
