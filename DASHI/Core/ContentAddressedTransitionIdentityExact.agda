module DASHI.Core.ContentAddressedTransitionIdentityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CONTENT-ADDRESSED SAME-TRANSITION IDENTITY
--
-- Runtime encodings may change representation, but the transition certified,
-- simulated, authorised, emitted, and executed must remain the same literal
-- semantic object.  A digest is a stable runtime handle for that spine; it is
-- not itself promoted to semantic equality or collision-freedom.
------------------------------------------------------------------------

record ContentAddressReceipt : Set where
  constructor content-address-receipt
  field
    canonicalisationReference : String
    digestAlgorithmReference : String
    digest : String
    payloadReference : String

open ContentAddressReceipt public

record SameTransitionSpine {Transition : Set} (canonical : Transition) : Set₁ where
  constructor same-transition-spine
  field
    address : ContentAddressReceipt

    proposed : Transition
    simulated : Transition
    admitted : Transition
    authorised : Transition
    emitted : Transition
    executed : Transition

    proposedExact : proposed ≡ canonical
    simulatedExact : simulated ≡ canonical
    admittedExact : admitted ≡ canonical
    authorisedExact : authorised ≡ canonical
    emittedExact : emitted ≡ canonical
    executedExact : executed ≡ canonical

    spineReference : String

open SameTransitionSpine public

canonicalSpine :
  ∀ {Transition : Set}
    (transition : Transition) →
    ContentAddressReceipt →
    String →
    SameTransitionSpine transition
canonicalSpine transition receipt reference =
  same-transition-spine
    receipt
    transition transition transition transition transition transition
    refl refl refl refl refl refl
    reference

record TransitionIdentityBoundary : Set where
  constructor transition-identity-boundary
  field
    sameDigestAutomaticallyProvesSemanticEquality : Bool
    sameDigestAutomaticallyProvesSemanticEqualityIsFalse :
      sameDigestAutomaticallyProvesSemanticEquality ≡ false

    contentAddressAutomaticallyProvesCollisionFreedom : Bool
    contentAddressAutomaticallyProvesCollisionFreedomIsFalse :
      contentAddressAutomaticallyProvesCollisionFreedom ≡ false

    extensionallySimilarActionMayReplaceCertifiedLiteralAction : Bool
    extensionallySimilarActionMayReplaceCertifiedLiteralActionIsFalse :
      extensionallySimilarActionMayReplaceCertifiedLiteralAction ≡ false

    runtimeEncodingMaySilentlyChangeTransition : Bool
    runtimeEncodingMaySilentlyChangeTransitionIsFalse :
      runtimeEncodingMaySilentlyChangeTransition ≡ false

canonicalTransitionIdentityBoundary : TransitionIdentityBoundary
canonicalTransitionIdentityBoundary =
  transition-identity-boundary
    false refl
    false refl
    false refl
    false refl
