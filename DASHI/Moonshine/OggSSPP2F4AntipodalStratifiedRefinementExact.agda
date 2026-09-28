module DASHI.Moonshine.OggSSPP2F4AntipodalStratifiedRefinementExact where

------------------------------------------------------------------------
-- p=2 F4 FROBENIUS STRATA -> 1 + 1 + 8 ANTIPODAL TARGET RECHART
--
-- DASHI CONTRIBUTION
--
-- Raw F4/F2 Frobenius has three orbit strata:
--
--   fixed 0
--   fixed 1
--   conjugate pair.
--
-- The retained Base369 target B x (T^2/C2) has:
--
--   two binary copies of the rank-2 antipodal centre, and
--   two binary copies of four noncentral antipodal classes.
--
-- Hence its ten states admit an exact stratified presentation:
--
--   1 + 1 + (2 * 4) = 10.
--
-- Moreover the inherited antipodal stabilizer TYPE matches the raw F4
-- Frobenius orbit TYPE:
--
--   fixed0         -> centre copy -> size 2
--   fixed1         -> centre copy -> size 2
--   conjugate pair -> noncentral  -> size 1.
--
-- This is a target-side rechart and stabilizer-type compatibility theorem.
-- It does NOT prove that the arithmetic marked CM source chooses this
-- refinement.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Moonshine.OggSSPP2F4FrobeniusCandidateNoGoExact as F4
import DASHI.Moonshine.OggSSPSmallCharacteristicResidualGroupoidExact as Target
import DASHI.Moonshine.QuadraticApproximationPrimeCompressionBidiExact as Compression
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Four noncentral rank-2 antipodal classes.
------------------------------------------------------------------------

data NoncentralNineOrbit : Set where
  firstAxisNoncentral : NoncentralNineOrbit
  secondAxisNoncentral : NoncentralNineOrbit
  equalSignNoncentral : NoncentralNineOrbit
  oppositeSignNoncentral : NoncentralNineOrbit

noncentralToNineOrbit :
  NoncentralNineOrbit ->
  Triadic.NineOrbit
noncentralToNineOrbit firstAxisNoncentral =
  Triadic.firstAxisOrbit
noncentralToNineOrbit secondAxisNoncentral =
  Triadic.secondAxisOrbit
noncentralToNineOrbit equalSignNoncentral =
  Triadic.equalSignOrbit
noncentralToNineOrbit oppositeSignNoncentral =
  Triadic.oppositeSignOrbit

------------------------------------------------------------------------
-- 2. Explicit 1 + 1 + 8 stratified target presentation.
------------------------------------------------------------------------

data F4StratifiedTargetState : Set where
  fixedZeroRefinement :
    F4StratifiedTargetState

  fixedOneRefinement :
    F4StratifiedTargetState

  conjugateRefinement :
    Compression.StrictSignedSide ->
    NoncentralNineOrbit ->
    F4StratifiedTargetState

stratumOf :
  F4StratifiedTargetState ->
  F4.F4FrobeniusOrbit
stratumOf fixedZeroRefinement =
  F4.zeroFixedOrbit
stratumOf fixedOneRefinement =
  F4.oneFixedOrbit
stratumOf (conjugateRefinement side orbit) =
  F4.conjugatePairOrbit

toRetainedTarget :
  F4StratifiedTargetState ->
  Target.P2ResidualObject
toRetainedTarget fixedZeroRefinement =
  Compression.lowerSide , Triadic.zeroOrbit
toRetainedTarget fixedOneRefinement =
  Compression.upperSide , Triadic.zeroOrbit
toRetainedTarget (conjugateRefinement side firstAxisNoncentral) =
  side , Triadic.firstAxisOrbit
toRetainedTarget (conjugateRefinement side secondAxisNoncentral) =
  side , Triadic.secondAxisOrbit
toRetainedTarget (conjugateRefinement side equalSignNoncentral) =
  side , Triadic.equalSignOrbit
toRetainedTarget (conjugateRefinement side oppositeSignNoncentral) =
  side , Triadic.oppositeSignOrbit

fromRetainedTarget :
  Target.P2ResidualObject ->
  F4StratifiedTargetState
fromRetainedTarget (Compression.lowerSide , Triadic.zeroOrbit) =
  fixedZeroRefinement
fromRetainedTarget (Compression.upperSide , Triadic.zeroOrbit) =
  fixedOneRefinement
fromRetainedTarget (side , Triadic.firstAxisOrbit) =
  conjugateRefinement side firstAxisNoncentral
fromRetainedTarget (side , Triadic.secondAxisOrbit) =
  conjugateRefinement side secondAxisNoncentral
fromRetainedTarget (side , Triadic.equalSignOrbit) =
  conjugateRefinement side equalSignNoncentral
fromRetainedTarget (side , Triadic.oppositeSignOrbit) =
  conjugateRefinement side oppositeSignNoncentral

stratifiedTargetRoundTrip :
  (state : F4StratifiedTargetState) ->
  fromRetainedTarget (toRetainedTarget state) ≡ state
stratifiedTargetRoundTrip fixedZeroRefinement = refl
stratifiedTargetRoundTrip fixedOneRefinement = refl
stratifiedTargetRoundTrip
  (conjugateRefinement Compression.lowerSide firstAxisNoncentral) = refl
stratifiedTargetRoundTrip
  (conjugateRefinement Compression.upperSide firstAxisNoncentral) = refl
stratifiedTargetRoundTrip
  (conjugateRefinement Compression.lowerSide secondAxisNoncentral) = refl
stratifiedTargetRoundTrip
  (conjugateRefinement Compression.upperSide secondAxisNoncentral) = refl
stratifiedTargetRoundTrip
  (conjugateRefinement Compression.lowerSide equalSignNoncentral) = refl
stratifiedTargetRoundTrip
  (conjugateRefinement Compression.upperSide equalSignNoncentral) = refl
stratifiedTargetRoundTrip
  (conjugateRefinement Compression.lowerSide oppositeSignNoncentral) = refl
stratifiedTargetRoundTrip
  (conjugateRefinement Compression.upperSide oppositeSignNoncentral) = refl

retainedTargetRoundTrip :
  (state : Target.P2ResidualObject) ->
  toRetainedTarget (fromRetainedTarget state) ≡ state
retainedTargetRoundTrip (Compression.lowerSide , Triadic.zeroOrbit) = refl
retainedTargetRoundTrip (Compression.upperSide , Triadic.zeroOrbit) = refl
retainedTargetRoundTrip (Compression.lowerSide , Triadic.firstAxisOrbit) = refl
retainedTargetRoundTrip (Compression.upperSide , Triadic.firstAxisOrbit) = refl
retainedTargetRoundTrip (Compression.lowerSide , Triadic.secondAxisOrbit) = refl
retainedTargetRoundTrip (Compression.upperSide , Triadic.secondAxisOrbit) = refl
retainedTargetRoundTrip (Compression.lowerSide , Triadic.equalSignOrbit) = refl
retainedTargetRoundTrip (Compression.upperSide , Triadic.equalSignOrbit) = refl
retainedTargetRoundTrip (Compression.lowerSide , Triadic.oppositeSignOrbit) = refl
retainedTargetRoundTrip (Compression.upperSide , Triadic.oppositeSignOrbit) = refl

------------------------------------------------------------------------
-- 3. Fibre profile.
------------------------------------------------------------------------

stratumRefinementCount :
  F4.F4FrobeniusOrbit ->
  Nat
stratumRefinementCount F4.zeroFixedOrbit = 1
stratumRefinementCount F4.oneFixedOrbit = 1
stratumRefinementCount F4.conjugatePairOrbit = 8

stratifiedProfileTotal : Nat
stratifiedProfileTotal =
  stratumRefinementCount F4.zeroFixedOrbit
  + stratumRefinementCount F4.oneFixedOrbit
  + stratumRefinementCount F4.conjugatePairOrbit

stratifiedProfileIsOnePlusOnePlusEight :
  stratifiedProfileTotal ≡ 10
stratifiedProfileIsOnePlusOnePlusEight = refl

conjugateRefinementCountIsBinaryTimesFour :
  stratumRefinementCount F4.conjugatePairOrbit ≡ 2 * 4
conjugateRefinementCountIsBinaryTimesFour = refl

------------------------------------------------------------------------
-- 4. Stabilizer-TYPE compatibility.
--
-- The retained target groupoid itself is currently identity-only.  These
-- numbers refer instead to the stabilizer inherited from the underlying
-- rank-2 antipodal C2 geometry, which is exactly the structure being compared
-- to raw F4 Frobenius orbit type.
------------------------------------------------------------------------

rawF4OrbitStabilizerSize :
  F4.F4FrobeniusOrbit ->
  Nat
rawF4OrbitStabilizerSize F4.zeroFixedOrbit = 2
rawF4OrbitStabilizerSize F4.oneFixedOrbit = 2
rawF4OrbitStabilizerSize F4.conjugatePairOrbit = 1

inheritedAntipodalStabilizerSize :
  Target.P2ResidualObject ->
  Nat
inheritedAntipodalStabilizerSize
  (side , Triadic.zeroOrbit) = 2
inheritedAntipodalStabilizerSize
  (side , Triadic.firstAxisOrbit) = 1
inheritedAntipodalStabilizerSize
  (side , Triadic.secondAxisOrbit) = 1
inheritedAntipodalStabilizerSize
  (side , Triadic.equalSignOrbit) = 1
inheritedAntipodalStabilizerSize
  (side , Triadic.oppositeSignOrbit) = 1

stratifiedRechartPreservesStabilizerType :
  (state : F4StratifiedTargetState) ->
  rawF4OrbitStabilizerSize (stratumOf state)
  ≡
  inheritedAntipodalStabilizerSize (toRetainedTarget state)
stratifiedRechartPreservesStabilizerType fixedZeroRefinement = refl
stratifiedRechartPreservesStabilizerType fixedOneRefinement = refl
stratifiedRechartPreservesStabilizerType
  (conjugateRefinement side firstAxisNoncentral) = refl
stratifiedRechartPreservesStabilizerType
  (conjugateRefinement side secondAxisNoncentral) = refl
stratifiedRechartPreservesStabilizerType
  (conjugateRefinement side equalSignNoncentral) = refl
stratifiedRechartPreservesStabilizerType
  (conjugateRefinement side oppositeSignNoncentral) = refl

------------------------------------------------------------------------
-- 5. Arithmetic firewall.
------------------------------------------------------------------------

data TargetRechartCreatesArithmeticMarkedRefinement : Set where
data StabilizerTypeMatchCreatesArithmeticRecognition : Set where

targetRechartDoesNotCreateArithmeticMarkedRefinement :
  TargetRechartCreatesArithmeticMarkedRefinement -> ⊥
targetRechartDoesNotCreateArithmeticMarkedRefinement ()

stabilizerTypeMatchDoesNotCreateArithmeticRecognition :
  StabilizerTypeMatchCreatesArithmeticRecognition -> ⊥
stabilizerTypeMatchDoesNotCreateArithmeticRecognition ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryCrossModuleInference

record P2F4AntipodalStratifiedRefinementBoundary : Set where
  constructor p2-f4-antipodal-stratified-refinement-boundary
  field
    exactOneOneEightTargetRechartConstructed : Bool
    twoFixedRawStrataMatchTwoCentreCopiesByType : Bool
    conjugateRawStratumMatchesEightNoncentralCopiesByType : Bool
    inheritedStabilizerTypePreserved : Bool
    uniformThreeStratumLiftAlreadyRuledOut : Bool
    arithmeticMarkedRefinementConstructed : Bool
    arithmeticRecognitionClaimed : Bool

canonicalP2F4AntipodalStratifiedRefinementBoundary :
  P2F4AntipodalStratifiedRefinementBoundary
canonicalP2F4AntipodalStratifiedRefinementBoundary =
  p2-f4-antipodal-stratified-refinement-boundary
    true true true true true false false
