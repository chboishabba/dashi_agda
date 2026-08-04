module DASHI.Combinatorics.SSP15FractranCompression where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Nat using (_≤_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_)

open import DASHI.Combinatorics.FractranCOL using (EV5; step; run)
open import DASHI.Combinatorics.FractranComputationEquivalence
  using (SameOutcome)
open import MDL.Core using (CodeLength)
open import MonsterOntos using (SSP)

------------------------------------------------------------------------
-- Fifteen SSP labels as a quotient/compression alphabet.
--
-- A bare SSP label cannot be treated as a lossless encoding of every EV5
-- exponent vector without an additional theorem. It can nevertheless serve as:
--
--   1. an outcome-preserving quotient key;
--   2. the model/index part of a lossless label-plus-residual codec;
--   3. a transition alphabet when the quotient is a congruence for `step`.
------------------------------------------------------------------------

mapMaybe : {A B : Set} → (A → B) → Maybe A → Maybe B
mapMaybe f nothing  = nothing
mapMaybe f (just x) = just (f x)

------------------------------------------------------------------------
-- 1. Lossy but semantically sound quotient compression.
------------------------------------------------------------------------

record SSP15OutcomeQuotient : Set₁ where
  field
    encode         : EV5 → SSP
    representative : SSP → EV5

    representative-sound :
      ∀ state → SameOutcome (representative (encode state)) state

    key-complete-for-outcome :
      ∀ {left right} →
      encode left ≡ encode right →
      SameOutcome left right

open SSP15OutcomeQuotient public

quotientRoundtripOutcome :
  (Q : SSP15OutcomeQuotient) →
  ∀ state →
  run (representative Q (encode Q state)) ≡ run state
quotientRoundtripOutcome Q = representative-sound Q

------------------------------------------------------------------------
-- 2. Lossless compression requires a residual channel.
------------------------------------------------------------------------

record SSP15ResidualCodec : Set₁ where
  field
    Residual : Set

    encodeLabel    : EV5 → SSP
    encodeResidual : EV5 → Residual
    decode         : SSP → Residual → EV5

    decode-encode :
      ∀ state →
      decode (encodeLabel state) (encodeResidual state) ≡ state

open SSP15ResidualCodec public

EncodedSSP15State : SSP15ResidualCodec → Set
EncodedSSP15State C = SSP × Residual C

encodeState :
  (C : SSP15ResidualCodec) →
  EV5 → EncodedSSP15State C
encodeState C state = encodeLabel C state , encodeResidual C state

decodeState :
  (C : SSP15ResidualCodec) →
  EncodedSSP15State C → EV5
decodeState C (label , residual) = decode C label residual

codec-roundtrip :
  (C : SSP15ResidualCodec) →
  ∀ state → decodeState C (encodeState C state) ≡ state
codec-roundtrip C = decode-encode C

------------------------------------------------------------------------
-- 3. Compression of transitions.
--
-- A state quotient induces a deterministic compressed transition only when
-- states sharing one SSP label also have the same next compressed label. This
-- is the exact congruence obligation that prevents an arbitrary hash from being
-- mistaken for a dynamics-preserving quotient.
------------------------------------------------------------------------

record SSP15StepCongruence (encode : EV5 → SSP) : Set where
  field
    step-congruent :
      ∀ {left right} →
      encode left ≡ encode right →
      mapMaybe encode (step left) ≡ mapMaybe encode (step right)

open SSP15StepCongruence public

record SSP15TransitionCompression : Set₁ where
  field
    encode : EV5 → SSP
    compressedStep : SSP → Maybe SSP
    congruence : SSP15StepCongruence encode

    step-sound :
      ∀ state →
      compressedStep (encode state) ≡ mapMaybe encode (step state)

open SSP15TransitionCompression public

compressedTransition-preserves-step :
  (C : SSP15TransitionCompression) →
  ∀ {state next} →
  step state ≡ just next →
  compressedStep C (encode C state) ≡ just (encode C next)
compressedTransition-preserves-step C {state} {next} p
  rewrite step-sound C state | p = refl

compressedTransition-preserves-halt :
  (C : SSP15TransitionCompression) →
  ∀ {state} →
  step state ≡ nothing →
  compressedStep C (encode C state) ≡ nothing
compressedTransition-preserves-halt C {state} p
  rewrite step-sound C state | p = refl

------------------------------------------------------------------------
-- 4. Whole-run compression.
------------------------------------------------------------------------

record SSP15RunCompression : Set₁ where
  field
    transition : SSP15TransitionCompression
    compressedRun : SSP → SSP

    run-sound :
      ∀ state →
      compressedRun (encode transition state) ≡ encode transition (run state)

open SSP15RunCompression public

------------------------------------------------------------------------
-- 5. MDL receipt: fifteen labels are useful compression only when the saved
-- residual/transition description pays for the quotient model itself.
------------------------------------------------------------------------

record SSP15CompressionCost : Set where
  constructor ssp15CompressionCost
  field
    modelBits      : CodeLength
    labelBits      : CodeLength
    residualBits   : CodeLength
    transitionBits : CodeLength

  totalBits : CodeLength
  totalBits = modelBits + labelBits + residualBits + transitionBits

open SSP15CompressionCost public

record SSP15CompressionReceipt
  (literal compressed : SSP15CompressionCost) : Set₁ where
  field
    outcomeOrLosslessAuthority :
      SSP15OutcomeQuotient ⊎ SSP15ResidualCodec
    transitionAuthority : SSP15TransitionCompression
    mdlNonWorse : totalBits compressed ≤ totalBits literal

open SSP15CompressionReceipt public

------------------------------------------------------------------------
-- 6. Promotion boundary.
------------------------------------------------------------------------

record SSP15CompressionBoundary : Set₁ where
  field
    bareLabelLosslessnessProved : Bool
    bareLabelLosslessnessProvedIsFalse :
      bareLabelLosslessnessProved ≡ false

    outcomeQuotientSupported : Bool
    outcomeQuotientSupportedIsTrue :
      outcomeQuotientSupported ≡ true

    residualCodecRequiredForLosslessness : Bool
    residualCodecRequiredForLosslessnessIsTrue :
      residualCodecRequiredForLosslessness ≡ true

    transitionCongruenceRequired : Bool
    transitionCongruenceRequiredIsTrue :
      transitionCongruenceRequired ≡ true

    outcomeQuotientTarget      : Set₁
    residualCodecTarget        : Set₁
    transitionCongruenceTarget : Set₁
    runCompressionTarget       : Set₁

canonicalSSP15CompressionBoundary : SSP15CompressionBoundary
canonicalSSP15CompressionBoundary = record
  { bareLabelLosslessnessProved = false
  ; bareLabelLosslessnessProvedIsFalse = refl
  ; outcomeQuotientSupported = true
  ; outcomeQuotientSupportedIsTrue = refl
  ; residualCodecRequiredForLosslessness = true
  ; residualCodecRequiredForLosslessnessIsTrue = refl
  ; transitionCongruenceRequired = true
  ; transitionCongruenceRequiredIsTrue = refl
  ; outcomeQuotientTarget = SSP15OutcomeQuotient
  ; residualCodecTarget = SSP15ResidualCodec
  ; transitionCongruenceTarget =
      Σ (EV5 → SSP) SSP15StepCongruence
  ; runCompressionTarget = SSP15RunCompression
  }
