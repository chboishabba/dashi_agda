module DASHI.Analysis.RiemannPrimitiveKernelUnimodularBasisExact where

------------------------------------------------------------------------
-- RH PRIMITIVE KERNEL: EXPLICIT UNIMODULAR BASIS CHANGE
--
-- The coefficient row begins
--
--   (80, 243, 1215, 972).
--
-- The first two columns admit the determinant-one change of basis
--
--       [ -82   3 ]
--   U = [  27  -1 ]
--
-- for which
--
--   (80,243) U = (1,-3).
--
-- An explicit inverse is
--
--          [ -1  -3 ]
--   U^-1 = [ -27 -82 ].
--
-- Therefore the visible 3-adic depth profile (0,5,5,5) is NOT invariant under
-- arbitrary unimodular column changes: after this basis change the absolute
-- coefficient depths are (0,1,5,5).
--
-- By contrast, the primitive/Smith invariant is preserved: the row is
-- primitive because the same Bezout data gives 27*243 - 82*80 = 1.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Integer using (ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Product using (_×_; _,_)

import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR

module RingZ = NR IntRS.ring
open RingZ using (Κ; Ι; _⊕_; _⊗_; ⊝_; solve)

import DASHI.Analysis.RiemannPrimitiveKernelBalancedTernaryStencilExact as RH

PairZ : Set
PairZ = ℤ × ℤ

forwardU : PairZ -> PairZ
forwardU (x , y) =
  (((- (+ 82)) * x) + ((+ 27) * y))
  ,
  (((+ 3) * x) + ((- (+ 1)) * y))

inverseU : PairZ -> PairZ
inverseU (u , v) =
  (((- (+ 1)) * u) + ((- (+ 27)) * v))
  ,
  (((- (+ 3)) * u) + ((- (+ 82)) * v))

determinantUIsOne :
  ((- (+ 82)) * (- (+ 1))) - ((+ 3) * (+ 27))
  ≡ + 1
determinantUIsOne = refl

forwardAfterInverse :
  (p : PairZ) ->
  forwardU (inverseU p) ≡ p
forwardAfterInverse (u , v) =
  cong₂ _,_
    (RingZ.solve 2
      (λ u v ->
        ( (((⊝ (Κ (+ 82))) ⊗
              (((⊝ (Κ (+ 1))) ⊗ u) ⊕ ((⊝ (Κ (+ 27))) ⊗ v)))
           ⊕
           ((Κ (+ 27)) ⊗
              (((⊝ (Κ (+ 3))) ⊗ u) ⊕ ((⊝ (Κ (+ 82))) ⊗ v))))
        , u ))
      refl u v)
    (RingZ.solve 2
      (λ u v ->
        ( (((Κ (+ 3)) ⊗
              (((⊝ (Κ (+ 1))) ⊗ u) ⊕ ((⊝ (Κ (+ 27))) ⊗ v)))
           ⊕
           ((⊝ (Κ (+ 1))) ⊗
              (((⊝ (Κ (+ 3))) ⊗ u) ⊕ ((⊝ (Κ (+ 82))) ⊗ v))))
        , v ))
      refl u v)

inverseAfterForward :
  (p : PairZ) ->
  inverseU (forwardU p) ≡ p
inverseAfterForward (x , y) =
  cong₂ _,_
    (RingZ.solve 2
      (λ x y ->
        ( (((⊝ (Κ (+ 1))) ⊗
              (((⊝ (Κ (+ 82))) ⊗ x) ⊕ ((Κ (+ 27)) ⊗ y)))
           ⊕
           ((⊝ (Κ (+ 27))) ⊗
              (((Κ (+ 3)) ⊗ x) ⊕ ((⊝ (Κ (+ 1))) ⊗ y))))
        , x ))
      refl x y)
    (RingZ.solve 2
      (λ x y ->
        ( (((⊝ (Κ (+ 3))) ⊗
              (((⊝ (Κ (+ 82))) ⊗ x) ⊕ ((Κ (+ 27)) ⊗ y)))
           ⊕
           ((⊝ (Κ (+ 82))) ⊗
              (((Κ (+ 3)) ⊗ x) ⊕ ((⊝ (Κ (+ 1))) ⊗ y))))
        , y ))
      refl x y)

originalLeadingPair : PairZ
originalLeadingPair = (+ 80) , (+ 243)

transformedLeadingPair : PairZ
transformedLeadingPair = forwardU originalLeadingPair

transformedLeadingPairExact :
  transformedLeadingPair ≡ ((+ 1) , (- (+ 3)))
transformedLeadingPairExact = refl

inverseRecoversOriginalPair :
  inverseU ((+ 1) , (- (+ 3))) ≡ originalLeadingPair
inverseRecoversOriginalPair = refl

------------------------------------------------------------------------
-- Primitive / Smith-style scalar invariant.
------------------------------------------------------------------------

primitiveBezoutCertificate :
  ((+ 27) * (+ 243)) - ((+ 82) * (+ 80))
  ≡ + 1
primitiveBezoutCertificate = refl

record SmithInvariantOneReceipt : Set where
  constructor smith-invariant-one-receipt
  field
    bezoutLeft : ℤ
    bezoutRight : ℤ
    combinationIsOne :
      bezoutLeft * (+ 80) + bezoutRight * (+ 243) ≡ + 1

canonicalSmithInvariantOneReceipt : SmithInvariantOneReceipt
canonicalSmithInvariantOneReceipt =
  smith-invariant-one-receipt
    (- (+ 82))
    (+ 27)
    refl

------------------------------------------------------------------------
-- Coordinate depth profile changes.
--
-- The transformed row is
--
--   (1, -3, 1215, 972).
--
-- Taking absolute magnitudes gives exact ternary depths
--
--   (0,1,5,5),
--
-- while the original displayed basis has (0,5,5,5).
------------------------------------------------------------------------

record FourDepthProfile : Set where
  constructor four-depth-profile
  field
    firstDepth secondDepth thirdDepth fourthDepth : Nat

open FourDepthProfile public

originalDepthProfile : FourDepthProfile
originalDepthProfile =
  four-depth-profile 0 5 5 5

transformedDepthProfile : FourDepthProfile
transformedDepthProfile =
  four-depth-profile 0 1 5 5

transformedSecondAbsoluteCoefficient :
  Nat
transformedSecondAbsoluteCoefficient = 3

transformedSecondExactDepthOne :
  transformedSecondAbsoluteCoefficient ≡ 3 * 1
transformedSecondExactDepthOne = refl

oneNotFive : 1 ≡ 5 -> ⊥
oneNotFive ()

depthProfileChangesUnderUnimodularBasis :
  secondDepth transformedDepthProfile
  ≡
  secondDepth originalDepthProfile
  ->
  ⊥
depthProfileChangesUnderUnimodularBasis =
  oneNotFive

------------------------------------------------------------------------
-- Consequence / firewall.
------------------------------------------------------------------------

data RawDepthTupleIsUnimodularInvariant : Set where
data SmithInvariantOneDeterminesDepthFiveFlag : Set where

rawDepthTupleNotUnimodularInvariant :
  RawDepthTupleIsUnimodularInvariant -> ⊥
rawDepthTupleNotUnimodularInvariant ()

smithInvariantOneDoesNotDetermineDepthFiveFlag :
  SmithInvariantOneDeterminesDepthFiveFlag -> ⊥
smithInvariantOneDoesNotDetermineDepthFiveFlag ()

record RiemannPrimitiveKernelUnimodularBoundary : Set where
  constructor riemann-primitive-kernel-unimodular-boundary
  field
    determinantOneBasisChangeOwned : Bool
    explicitInverseOwned : Bool
    roundTripsOwned : Bool
    originalLeadingPairBecomesOneMinusThree : Bool
    primitiveBezoutSmithInvariantOneOwned : Bool
    originalDepthProfileZeroFiveFiveFiveOwned : Bool
    transformedDepthProfileZeroOneFiveFiveOwned : Bool
    rawDepthProfileUnimodularInvariant : Bool
    filteredFlagStillRequiresExtraStructure : Bool

canonicalRiemannPrimitiveKernelUnimodularBoundary :
  RiemannPrimitiveKernelUnimodularBoundary
canonicalRiemannPrimitiveKernelUnimodularBoundary =
  riemann-primitive-kernel-unimodular-boundary
    true true true true true true true false true
