module DASHI.Moonshine.Base369P3ConstantTernaryActionGroupoidExact where

------------------------------------------------------------------------
-- BASE369 p=3 CONSTANT-TERNARY ACTION GROUPOID
--
-- DASHI CONTRIBUTION
--
-- Independent target presentation for the exceptional p=3 residual:
--
--   State    = canonical SSPTrit {-1,0,+1}
--   Symmetry = canonical C2 sign inversion
--   Orbits   = {zero, nonzero}
--
-- The zero orbit has the full C2 stabilizer; the nonzero orbit has trivial
-- stabilizer.  This module does not mention Ogg/Duncan--Swisher arithmetic.
-- It is therefore suitable as an independently constructed 369 recognition
-- target for the arithmetic/source-side groupoid on the #1053 lane.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ResidualSymmetryCollisionFibreExact as Action
import DASHI.Core.OrbitStabilizerResidualPresentationExact as Orbit
import DASHI.Foundations.BalancedTernaryOrbitStabilizerResidualBridgeExact as C2
import DASHI.Foundations.SSPTritCarrier as SSP

------------------------------------------------------------------------
-- 1. Canonical sign inversion on SSPTrit.
------------------------------------------------------------------------

negateSSP : SSP.SSPTrit -> SSP.SSPTrit
negateSSP SSP.sspNegOne = SSP.sspPosOne
negateSSP SSP.sspZero = SSP.sspZero
negateSSP SSP.sspPosOne = SSP.sspNegOne

negateSSPInvolutive :
  (state : SSP.SSPTrit) ->
  negateSSP (negateSSP state) ≡ state
negateSSPInvolutive SSP.sspNegOne = refl
negateSSPInvolutive SSP.sspZero = refl
negateSSPInvolutive SSP.sspPosOne = refl

actP3C2 :
  C2.C2 ->
  SSP.SSPTrit ->
  SSP.SSPTrit
actP3C2 C2.identity state = state
actP3C2 C2.flip state = negateSSP state

identityActs :
  (state : SSP.SSPTrit) ->
  actP3C2 C2.identity state ≡ state
identityActs state = refl

combineActs :
  (g h : C2.C2) ->
  (state : SSP.SSPTrit) ->
  actP3C2 (C2.combineC2 g h) state
  ≡
  actP3C2 g (actP3C2 h state)
combineActs C2.identity h state = refl
combineActs C2.flip C2.identity state = refl
combineActs C2.flip C2.flip state =
  sym (negateSSPInvolutive state)

inverseLeftActs :
  (g : C2.C2) ->
  (state : SSP.SSPTrit) ->
  actP3C2 (C2.inverseC2 g) (actP3C2 g state) ≡ state
inverseLeftActs C2.identity state = refl
inverseLeftActs C2.flip state = negateSSPInvolutive state

inverseRightActs :
  (g : C2.C2) ->
  (state : SSP.SSPTrit) ->
  actP3C2 g (actP3C2 (C2.inverseC2 g) state) ≡ state
inverseRightActs C2.identity state = refl
inverseRightActs C2.flip state = negateSSPInvolutive state

p3C2Action :
  Action.InvertibleSymmetryAction SSP.SSPTrit C2.C2
p3C2Action =
  Action.invertibleSymmetryAction
    C2.identity
    C2.combineC2
    C2.inverseC2
    actP3C2
    identityActs
    combineActs
    inverseLeftActs
    inverseRightActs

------------------------------------------------------------------------
-- 2. Two orbit strata.
------------------------------------------------------------------------

data P3Orbit : Set where
  zeroOrbit : P3Orbit
  nonzeroOrbit : P3Orbit

orbitOf :
  SSP.SSPTrit ->
  P3Orbit
orbitOf SSP.sspZero = zeroOrbit
orbitOf SSP.sspNegOne = nonzeroOrbit
orbitOf SSP.sspPosOne = nonzeroOrbit

representative :
  P3Orbit ->
  SSP.SSPTrit
representative zeroOrbit = SSP.sspZero
representative nonzeroOrbit = SSP.sspPosOne

orbitInvariant :
  (g : C2.C2) ->
  (state : SSP.SSPTrit) ->
  orbitOf (actP3C2 g state) ≡ orbitOf state
orbitInvariant C2.identity state = refl
orbitInvariant C2.flip SSP.sspNegOne = refl
orbitInvariant C2.flip SSP.sspZero = refl
orbitInvariant C2.flip SSP.sspPosOne = refl

representativeInOrbit :
  (orbit : P3Orbit) ->
  orbitOf (representative orbit) ≡ orbit
representativeInOrbit zeroOrbit = refl
representativeInOrbit nonzeroOrbit = refl

transporter :
  SSP.SSPTrit ->
  C2.C2
transporter SSP.sspNegOne = C2.flip
transporter SSP.sspZero = C2.identity
transporter SSP.sspPosOne = C2.identity

transporterHits :
  (state : SSP.SSPTrit) ->
  actP3C2
    (transporter state)
    (representative (orbitOf state))
  ≡ state
transporterHits SSP.sspNegOne = refl
transporterHits SSP.sspZero = refl
transporterHits SSP.sspPosOne = refl

p3OrbitPresentation :
  Orbit.OrbitPresentation p3C2Action
p3OrbitPresentation =
  Orbit.orbitPresentation
    P3Orbit
    orbitOf
    representative
    orbitInvariant
    representativeInOrbit
    transporter
    transporterHits

------------------------------------------------------------------------
-- 3. Explicit stabilizer split.
------------------------------------------------------------------------

data StabilizerClass : Set where
  fullC2Stabilizer : StabilizerClass
  trivialStabilizer : StabilizerClass

stabilizerClass :
  P3Orbit ->
  StabilizerClass
stabilizerClass zeroOrbit = fullC2Stabilizer
stabilizerClass nonzeroOrbit = trivialStabilizer

zeroFixedByFlip :
  actP3C2 C2.flip (representative zeroOrbit)
  ≡ representative zeroOrbit
zeroFixedByFlip = refl

nonzeroNotFixedByFlip :
  actP3C2 C2.flip (representative nonzeroOrbit)
  ≡ representative nonzeroOrbit
  ->
  ⊥
nonzeroNotFixedByFlip ()

------------------------------------------------------------------------
-- 4. Provenance coordinate for recognition.
--
-- We retain exact SSP polarity rather than quotienting it to orbit class.
------------------------------------------------------------------------

P3Provenance : Set
P3Provenance = SSP.SSPTritPolarity

stateProvenance :
  SSP.SSPTrit ->
  P3Provenance
stateProvenance = SSP.sspTritPolarity

data OrbitClassErasesPolarityWithoutReceipt : Set where

orbitClassDoesNotAuthorizePolarityErasure :
  OrbitClassErasesPolarityWithoutReceipt -> ⊥
orbitClassDoesNotAuthorizePolarityErasure ()

record Base369P3ConstantTernaryGroupoidBoundary : Set where
  constructor base369-p3-constant-ternary-groupoid-boundary
  field
    canonicalSSPTritCarrierUsed : Bool
    canonicalC2SignInversionUsed : Bool
    twoOrbitPresentationConstructed : Bool
    zeroOrbitHasFullC2Stabilizer : Bool
    nonzeroOrbitHasTrivialStabilizer : Bool
    polarityProvenanceRetained : Bool
    arithmeticRecognitionClaimedHere : Bool

canonicalBase369P3ConstantTernaryGroupoidBoundary :
  Base369P3ConstantTernaryGroupoidBoundary
canonicalBase369P3ConstantTernaryGroupoidBoundary =
  base369-p3-constant-ternary-groupoid-boundary
    true true true true true true false
