module DASHI.Moonshine.OggSSPP2F4DependentMarkedCoverExact where

------------------------------------------------------------------------
-- p=2 F4/F2 NONUNIFORM MARKED COVER AS DEPENDENT RECOVERABLE PROJECTION
--
-- DASHI CONTRIBUTION
--
-- Reuse the repository's generic dependent residual machinery on the exact
-- target-side 1+1+8 stratification:
--
--   coarse orbit = one of the three raw F4 Frobenius orbit labels
--
--   Mark(zeroFixed)      = Unit
--   Mark(oneFixed)       = Unit
--   Mark(conjugatePair)  = StrictSignedSide x NoncentralNineOrbit
--
-- Thus the fine code is exactly the dependent sum
--
--   Sigma(o : F4Orbit), Mark(o)
--
-- with fibre sizes 1,1,8 and exact reopening onto the ten-state retained
-- Base369 target presentation.
--
-- This is a target-side marked-cover NORMAL FORM.  It does not assert that
-- the arithmetic Gaussian-CM / X0(4) source supplies this Mark family.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Empty using (⊥)

import DASHI.Core.DependentRecoverableProjectionExact as Dependent
import DASHI.Moonshine.OggSSPP2F4FrobeniusCandidateNoGoExact as F4
import DASHI.Moonshine.OggSSPP2F4AntipodalStratifiedRefinementExact as Stratified
import DASHI.Moonshine.QuadraticApproximationPrimeCompressionBidiExact as Compression
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. State-dependent marking family.
------------------------------------------------------------------------

F4OrbitMark : F4.F4FrobeniusOrbit -> Set
F4OrbitMark F4.zeroFixedOrbit = ⊤
F4OrbitMark F4.oneFixedOrbit = ⊤
F4OrbitMark F4.conjugatePairOrbit =
  Compression.StrictSignedSide × Stratified.NoncentralNineOrbit

markedCode : Set
markedCode = Σ F4.F4FrobeniusOrbit F4OrbitMark

------------------------------------------------------------------------
-- 2. Exact encoding of the ten-state stratified target.
------------------------------------------------------------------------

projectToF4Orbit :
  Stratified.F4StratifiedTargetState ->
  F4.F4FrobeniusOrbit
projectToF4Orbit = Stratified.stratumOf

markOf :
  (state : Stratified.F4StratifiedTargetState) ->
  F4OrbitMark (projectToF4Orbit state)
markOf Stratified.fixedZeroRefinement = tt
markOf Stratified.fixedOneRefinement = tt
markOf
  (Stratified.conjugateRefinement side orbit) =
  side , orbit

reopenMarked :
  (orbit : F4.F4FrobeniusOrbit) ->
  F4OrbitMark orbit ->
  Stratified.F4StratifiedTargetState
reopenMarked F4.zeroFixedOrbit tt =
  Stratified.fixedZeroRefinement
reopenMarked F4.oneFixedOrbit tt =
  Stratified.fixedOneRefinement
reopenMarked F4.conjugatePairOrbit (side , orbit) =
  Stratified.conjugateRefinement side orbit

reopenMarkedExact :
  (state : Stratified.F4StratifiedTargetState) ->
  reopenMarked
    (projectToF4Orbit state)
    (markOf state)
  ≡ state
reopenMarkedExact Stratified.fixedZeroRefinement = refl
reopenMarkedExact Stratified.fixedOneRefinement = refl
reopenMarkedExact
  (Stratified.conjugateRefinement side orbit) = refl

p2F4DependentMarkedProjection :
  Dependent.DependentExactRecoverableProjection
    Stratified.F4StratifiedTargetState
    F4.F4FrobeniusOrbit
p2F4DependentMarkedProjection =
  Dependent.dependentExactRecoverableProjection
    F4OrbitMark
    projectToF4Orbit
    markOf
    reopenMarked
    reopenMarkedExact

------------------------------------------------------------------------
-- 3. Exact encode/decode through the generic owner.
------------------------------------------------------------------------

encodeMarked :
  Stratified.F4StratifiedTargetState ->
  Dependent.DependentCode p2F4DependentMarkedProjection
encodeMarked =
  Dependent.encode p2F4DependentMarkedProjection

decodeMarked :
  Dependent.DependentCode p2F4DependentMarkedProjection ->
  Stratified.F4StratifiedTargetState
decodeMarked =
  Dependent.decode p2F4DependentMarkedProjection

decodeEncodeMarked :
  (state : Stratified.F4StratifiedTargetState) ->
  decodeMarked (encodeMarked state) ≡ state
decodeEncodeMarked =
  Dependent.decodeEncodeExact p2F4DependentMarkedProjection

encodeDecodeMarked :
  (code : Dependent.DependentCode p2F4DependentMarkedProjection) ->
  encodeMarked (decodeMarked code) ≡ code
encodeDecodeMarked (F4.zeroFixedOrbit , tt) = refl
encodeDecodeMarked (F4.oneFixedOrbit , tt) = refl
encodeDecodeMarked
  (F4.conjugatePairOrbit , (side , orbit)) = refl

markedCodeBidi :
  ( (state : Stratified.F4StratifiedTargetState) ->
      decodeMarked (encodeMarked state) ≡ state )
  ×
  ( (code : Dependent.DependentCode p2F4DependentMarkedProjection) ->
      encodeMarked (decodeMarked code) ≡ code )
markedCodeBidi =
  decodeEncodeMarked , encodeDecodeMarked

markedCodeSeparating :
  Dependent.DependentCodeSeparating p2F4DependentMarkedProjection
markedCodeSeparating =
  Dependent.dependentCodeSeparating p2F4DependentMarkedProjection

------------------------------------------------------------------------
-- 4. Fibre-size surface.
------------------------------------------------------------------------

markFibreSize :
  F4.F4FrobeniusOrbit ->
  Nat
markFibreSize F4.zeroFixedOrbit = 1
markFibreSize F4.oneFixedOrbit = 1
markFibreSize F4.conjugatePairOrbit = 8

markFibreProfileIsOneOneEight :
  (markFibreSize F4.zeroFixedOrbit ≡ 1)
  ×
  (markFibreSize F4.oneFixedOrbit ≡ 1)
  ×
  (markFibreSize F4.conjugatePairOrbit ≡ 8)
markFibreProfileIsOneOneEight = refl , refl , refl

totalMarkedComponentCount : Nat
totalMarkedComponentCount =
  markFibreSize F4.zeroFixedOrbit
  + markFibreSize F4.oneFixedOrbit
  + markFibreSize F4.conjugatePairOrbit

totalMarkedComponentCountIsTen :
  totalMarkedComponentCount ≡ 10
totalMarkedComponentCountIsTen = refl

uniformResidualWouldLoseStratification :
  markFibreSize F4.zeroFixedOrbit
  ≡ markFibreSize F4.conjugatePairOrbit ->
  ⊥
uniformResidualWouldLoseStratification ()

------------------------------------------------------------------------
-- 5. Arithmetic acquisition socket.
--
-- The actual arithmetic theorem must produce a marking family over the raw F4
-- Frobenius orbit presentation and identify it with this target normal form.
-- Receipt labels alone cannot inhabit this socket.
------------------------------------------------------------------------

record ArithmeticGaussianCMMarking : Set₁ where
  field
    Mark : F4.F4FrobeniusOrbit -> Set

    fineState : Set

    projection :
      Dependent.DependentExactRecoverableProjection
        fineState
        F4.F4FrobeniusOrbit

    residualFamilyIsArithmeticLevelFourMarking : Bool
    residualFamilyIsArithmeticLevelFourMarkingIsTrue :
      residualFamilyIsArithmeticLevelFourMarking ≡ true

    zeroFixedMarkMatchesTarget :
      Mark F4.zeroFixedOrbit ≡ F4OrbitMark F4.zeroFixedOrbit

    oneFixedMarkMatchesTarget :
      Mark F4.oneFixedOrbit ≡ F4OrbitMark F4.oneFixedOrbit

    conjugateMarkMatchesTarget :
      Mark F4.conjugatePairOrbit ≡ F4OrbitMark F4.conjugatePairOrbit

open ArithmeticGaussianCMMarking public

data ReceiptMetadataConstructsArithmeticGaussianCMMarking : Set where

receiptMetadataDoesNotConstructArithmeticGaussianCMMarking :
  ReceiptMetadataConstructsArithmeticGaussianCMMarking -> ⊥
receiptMetadataDoesNotConstructArithmeticGaussianCMMarking ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryNewExtension

record P2F4DependentMarkedCoverBoundary : Set where
  constructor p2-f4-dependent-marked-cover-boundary
  field
    dependentResidualCoreReused : Bool
    exactOneOneEightMarkFamilyConstructed : Bool
    exactReopenConstructed : Bool
    exactEncodeDecodeConstructed : Bool
    dependentCodeSeparatingProved : Bool
    uniformMarkingRejected : Bool
    targetNormalFormHasTenComponents : Bool
    arithmeticGaussianCMMarkingConstructed : Bool
    receiptMetadataPromotedToMarking : Bool

canonicalP2F4DependentMarkedCoverBoundary :
  P2F4DependentMarkedCoverBoundary
canonicalP2F4DependentMarkedCoverBoundary =
  p2-f4-dependent-marked-cover-boundary
    true true true true true true true false false
