module DASHI.Moonshine.OggSSPP2PuncturedKernel2BidiExact where

------------------------------------------------------------------------
-- p=2 CONJUGATE MARK <-> CANONICAL PUNCTURED TRIADIC KERNEL 2
--
-- DASHI CONTRIBUTION
--
-- The existing p=2 conjugate fibre was proved to be the punctured ternary
-- plane T^2 \ {0}.  This module welds that carrier bidirectionally to the
-- canonical TriadicPAdicCodec.Kernel 2 object used elsewhere in the repo.
--
-- The puncture is proof-carrying: a state is a Kernel 2 vector together with
-- evidence that it is one of the eight nonzero vectors.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Product using (Σ; _,_)
open import Data.Empty using (⊥)

import DASHI.Codec.TriadicPAdicCodec as Codec
import DASHI.Algebra.Trit as Trit
import DASHI.Moonshine.OggSSPP2BalancedTernaryPuncturedPlaneExact as Plane
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

Kernel2 : Set
Kernel2 = Codec.Kernel 2

data Kernel2Nonzero : Kernel2 -> Set where
  negZero :
    Kernel2Nonzero
      (Trit.neg Codec.∷ᵥ Trit.zer Codec.∷ᵥ Codec.[]ᵥ)

  posZero :
    Kernel2Nonzero
      (Trit.pos Codec.∷ᵥ Trit.zer Codec.∷ᵥ Codec.[]ᵥ)

  zeroNeg :
    Kernel2Nonzero
      (Trit.zer Codec.∷ᵥ Trit.neg Codec.∷ᵥ Codec.[]ᵥ)

  zeroPos :
    Kernel2Nonzero
      (Trit.zer Codec.∷ᵥ Trit.pos Codec.∷ᵥ Codec.[]ᵥ)

  negNeg :
    Kernel2Nonzero
      (Trit.neg Codec.∷ᵥ Trit.neg Codec.∷ᵥ Codec.[]ᵥ)

  posPos :
    Kernel2Nonzero
      (Trit.pos Codec.∷ᵥ Trit.pos Codec.∷ᵥ Codec.[]ᵥ)

  negPos :
    Kernel2Nonzero
      (Trit.neg Codec.∷ᵥ Trit.pos Codec.∷ᵥ Codec.[]ᵥ)

  posNeg :
    Kernel2Nonzero
      (Trit.pos Codec.∷ᵥ Trit.neg Codec.∷ᵥ Codec.[]ᵥ)

PuncturedKernel2 : Set
PuncturedKernel2 = Σ Kernel2 Kernel2Nonzero

planeToPuncturedKernel2 :
  Plane.PuncturedNineSheet ->
  PuncturedKernel2
planeToPuncturedKernel2 Plane.negativeFirstAxis =
  (Trit.neg Codec.∷ᵥ Trit.zer Codec.∷ᵥ Codec.[]ᵥ) , negZero
planeToPuncturedKernel2 Plane.positiveFirstAxis =
  (Trit.pos Codec.∷ᵥ Trit.zer Codec.∷ᵥ Codec.[]ᵥ) , posZero
planeToPuncturedKernel2 Plane.negativeSecondAxis =
  (Trit.zer Codec.∷ᵥ Trit.neg Codec.∷ᵥ Codec.[]ᵥ) , zeroNeg
planeToPuncturedKernel2 Plane.positiveSecondAxis =
  (Trit.zer Codec.∷ᵥ Trit.pos Codec.∷ᵥ Codec.[]ᵥ) , zeroPos
planeToPuncturedKernel2 Plane.negativeEqualDiagonal =
  (Trit.neg Codec.∷ᵥ Trit.neg Codec.∷ᵥ Codec.[]ᵥ) , negNeg
planeToPuncturedKernel2 Plane.positiveEqualDiagonal =
  (Trit.pos Codec.∷ᵥ Trit.pos Codec.∷ᵥ Codec.[]ᵥ) , posPos
planeToPuncturedKernel2 Plane.negativeOppositeDiagonal =
  (Trit.neg Codec.∷ᵥ Trit.pos Codec.∷ᵥ Codec.[]ᵥ) , negPos
planeToPuncturedKernel2 Plane.positiveOppositeDiagonal =
  (Trit.pos Codec.∷ᵥ Trit.neg Codec.∷ᵥ Codec.[]ᵥ) , posNeg

puncturedKernel2ToPlane :
  PuncturedKernel2 ->
  Plane.PuncturedNineSheet
puncturedKernel2ToPlane
  ((Trit.neg Codec.∷ᵥ Trit.zer Codec.∷ᵥ Codec.[]ᵥ) , negZero) =
  Plane.negativeFirstAxis
puncturedKernel2ToPlane
  ((Trit.pos Codec.∷ᵥ Trit.zer Codec.∷ᵥ Codec.[]ᵥ) , posZero) =
  Plane.positiveFirstAxis
puncturedKernel2ToPlane
  ((Trit.zer Codec.∷ᵥ Trit.neg Codec.∷ᵥ Codec.[]ᵥ) , zeroNeg) =
  Plane.negativeSecondAxis
puncturedKernel2ToPlane
  ((Trit.zer Codec.∷ᵥ Trit.pos Codec.∷ᵥ Codec.[]ᵥ) , zeroPos) =
  Plane.positiveSecondAxis
puncturedKernel2ToPlane
  ((Trit.neg Codec.∷ᵥ Trit.neg Codec.∷ᵥ Codec.[]ᵥ) , negNeg) =
  Plane.negativeEqualDiagonal
puncturedKernel2ToPlane
  ((Trit.pos Codec.∷ᵥ Trit.pos Codec.∷ᵥ Codec.[]ᵥ) , posPos) =
  Plane.positiveEqualDiagonal
puncturedKernel2ToPlane
  ((Trit.neg Codec.∷ᵥ Trit.pos Codec.∷ᵥ Codec.[]ᵥ) , negPos) =
  Plane.negativeOppositeDiagonal
puncturedKernel2ToPlane
  ((Trit.pos Codec.∷ᵥ Trit.neg Codec.∷ᵥ Codec.[]ᵥ) , posNeg) =
  Plane.positiveOppositeDiagonal

planeKernel2RoundTrip :
  (point : Plane.PuncturedNineSheet) ->
  puncturedKernel2ToPlane (planeToPuncturedKernel2 point)
  ≡ point
planeKernel2RoundTrip Plane.negativeFirstAxis = refl
planeKernel2RoundTrip Plane.positiveFirstAxis = refl
planeKernel2RoundTrip Plane.negativeSecondAxis = refl
planeKernel2RoundTrip Plane.positiveSecondAxis = refl
planeKernel2RoundTrip Plane.negativeEqualDiagonal = refl
planeKernel2RoundTrip Plane.positiveEqualDiagonal = refl
planeKernel2RoundTrip Plane.negativeOppositeDiagonal = refl
planeKernel2RoundTrip Plane.positiveOppositeDiagonal = refl

kernel2PlaneRoundTrip :
  (point : PuncturedKernel2) ->
  planeToPuncturedKernel2 (puncturedKernel2ToPlane point)
  ≡ point
kernel2PlaneRoundTrip
  ((Trit.neg Codec.∷ᵥ Trit.zer Codec.∷ᵥ Codec.[]ᵥ) , negZero) = refl
kernel2PlaneRoundTrip
  ((Trit.pos Codec.∷ᵥ Trit.zer Codec.∷ᵥ Codec.[]ᵥ) , posZero) = refl
kernel2PlaneRoundTrip
  ((Trit.zer Codec.∷ᵥ Trit.neg Codec.∷ᵥ Codec.[]ᵥ) , zeroNeg) = refl
kernel2PlaneRoundTrip
  ((Trit.zer Codec.∷ᵥ Trit.pos Codec.∷ᵥ Codec.[]ᵥ) , zeroPos) = refl
kernel2PlaneRoundTrip
  ((Trit.neg Codec.∷ᵥ Trit.neg Codec.∷ᵥ Codec.[]ᵥ) , negNeg) = refl
kernel2PlaneRoundTrip
  ((Trit.pos Codec.∷ᵥ Trit.pos Codec.∷ᵥ Codec.[]ᵥ) , posPos) = refl
kernel2PlaneRoundTrip
  ((Trit.neg Codec.∷ᵥ Trit.pos Codec.∷ᵥ Codec.[]ᵥ) , negPos) = refl
kernel2PlaneRoundTrip
  ((Trit.pos Codec.∷ᵥ Trit.neg Codec.∷ᵥ Codec.[]ᵥ) , posNeg) = refl

------------------------------------------------------------------------
-- Promotion firewall.
------------------------------------------------------------------------

data CanonicalKernelReuseCreatesArithmeticCMMeaning : Set where

canonicalKernelReuseDoesNotCreateArithmeticCMMeaning :
  CanonicalKernelReuseCreatesArithmeticCMMeaning -> ⊥
canonicalKernelReuseDoesNotCreateArithmeticCMMeaning ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryCrossModuleInference

record PuncturedKernel2BidiBoundary : Set where
  constructor punctured-kernel2-bidi-boundary
  field
    canonicalKernel2Reused : Bool
    proofCarryingPunctureConstructed : Bool
    planeToKernel2MapConstructed : Bool
    kernel2ToPlaneMapConstructed : Bool
    twoSidedRoundTripsProved : Bool
    arithmeticCMMeaningClaimed : Bool

canonicalPuncturedKernel2BidiBoundary :
  PuncturedKernel2BidiBoundary
canonicalPuncturedKernel2BidiBoundary =
  punctured-kernel2-bidi-boundary
    true true true true true false
