module DASHI.Physics.CFD.SparseTwistLESBridge where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; _∷_; [])
open import Agda.Builtin.String using (String)

open import DASHI.Physics.CFD.SparseTwistLESOperator

------------------------------------------------------------------------
-- Bridge between the generic twist carrier and the full CFD state.
--
-- SparseTwistLESOperator deliberately keeps chart choice abstract.  This
-- bridge is the missing typed obligation that prevents a twist operator from
-- merely being carried beside the codec: a concrete scene must encode the full
-- field into the twist chart, decode it back, and prove that one full update is
-- exactly the decoded twist transport.
------------------------------------------------------------------------

record TwistCodecBridge
  (C : LosslessStructuralCodec)
  (O : ExactLearnedProxyOperator C)
  (T : TwistOperator) : Set₁ where
  field
    toTwistField : FullState C → Field T
    fromTwistField : Field T → FullState C

    from-to : ∀ x → fromTwistField (toTwistField x) ≡ x
    to-from : ∀ x → toTwistField (fromTwistField x) ≡ x

    controlAt : FullState C → Control T

    full-step-is-twist :
      ∀ x →
      fullStep O x ≡
      fromTwistField (twist T (toTwistField x) (controlAt x))

open TwistCodecBridge public

------------------------------------------------------------------------
-- Fully connected DASHI–LES theorem surface.
------------------------------------------------------------------------

record SparseTwistDASHILESFormalism : Setω where
  field
    codec : LosslessStructuralCodec
    learnedOperator : ExactLearnedProxyOperator codec
    twistOperator : TwistOperator
    twistBridge : TwistCodecBridge codec learnedOperator twistOperator

    structuralIndex : Set
    signedStructure : FullState codec → SignedSparseField structuralIndex

    claimBoundary : List String

open SparseTwistDASHILESFormalism public

------------------------------------------------------------------------
-- Reusable consequences.
------------------------------------------------------------------------

formalism-rollout-exact :
  (F : SparseTwistDASHILESFormalism) →
  ∀ n x →
  decode (codec F)
    (iterate n (proxyStep (learnedOperator F)) (encode (codec F) x))
  ≡
  iterate n (fullStep (learnedOperator F)) x
formalism-rollout-exact F =
  encoded-rollout-exact (codec F) (learnedOperator F)

formalism-one-step-is-twist :
  (F : SparseTwistDASHILESFormalism) →
  ∀ x →
  fullStep (learnedOperator F) x ≡
  fromTwistField (twistBridge F)
    (twist (twistOperator F)
      (toTwistField (twistBridge F) x)
      (controlAt (twistBridge F) x))
formalism-one-step-is-twist F = full-step-is-twist (twistBridge F)

------------------------------------------------------------------------
-- Honest promotion boundary for the generic package.
------------------------------------------------------------------------

canonicalDASHILESClaimBoundary : DASHILESClaimBoundary
canonicalDASHILESClaimBoundary = record
  { signedTernaryCarrierReused = true
  ; binarySupportIsDerived = true
  ; sparseTwistChannelPresent = true
  ; exactnessRequiresCommutingWitness = true
  ; asymptoticSpeedupProved = false
  ; navierStokesSolved = false
  ; empiricalCFDFidelityProved = false
  }

canonicalClaimBoundaryText : List String
canonicalClaimBoundaryText =
  "The structural carrier reuses DASHI.Algebra.Trit and derived binary support"
  ∷ "Negative vorticity remains active signed structure rather than absence"
  ∷ "Sparse atoms and twist transport are connected to full-state evolution by an explicit bridge"
  ∷ "Lossless finite-horizon rollout follows only from decode-encode and step-commutation witnesses"
  ∷ "Storage and update improvements are explicit nonexpansive cost witnesses"
  ∷ "No exponential speedup, Navier–Stokes solution, or empirical full-fidelity theorem is promoted here"
  ∷ []
