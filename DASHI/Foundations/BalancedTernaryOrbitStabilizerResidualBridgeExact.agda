module DASHI.Foundations.BalancedTernaryOrbitStabilizerResidualBridgeExact where

------------------------------------------------------------------------
-- GENERIC ORBIT/STABILIZER RESIDUAL THEOREM INSTANTIATED ON 27 = 1 + 13*2
--
-- This bridge proves that the existing balanced-ternary antipodal codec is not
-- merely an ad hoc quotient table.  It is an instance of the generic
-- orbit/stabilizer residual presentation:
--
--   centre orbit     : stabilizer = C2, residual quotient is singleton
--   noncentral orbit : stabilizer = 1,  residual quotient is C2 orientation.
--
-- Hence the state-dependent 1/2 residual rank is exactly stabilizer-indexed.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.OrbitStabilizerResidualPresentationExact as Generic
import DASHI.Core.ResidualSymmetryCollisionFibreExact as Symmetry
import DASHI.Foundations.Base369AddressSymmetryAndBranchGeometryExact as Branch
import DASHI.Foundations.BalancedTernaryAntipodalOrbitExact as Orbit
import DASHI.Foundations.BalancedTernaryAntipodalResidualCodecExact as Codec
import DASHI.Foundations.SSPTritCarrier as SSP

data C2 : Set where
  identity flip : C2

combineC2 : C2 -> C2 -> C2
combineC2 identity h = h
combineC2 flip identity = flip
combineC2 flip flip = identity

inverseC2 : C2 -> C2
inverseC2 identity = identity
inverseC2 flip = flip

actC2 : C2 -> Orbit.TritTriple -> Orbit.TritTriple
actC2 identity state = state
actC2 flip state = Orbit.strictAntipodeTriple state

identityActsC2 : (state : Orbit.TritTriple) -> actC2 identity state ≡ state
identityActsC2 state = refl

combineActsC2 :
  (g h : C2) (state : Orbit.TritTriple) ->
  actC2 (combineC2 g h) state ≡ actC2 g (actC2 h state)
combineActsC2 identity h state = refl
combineActsC2 flip identity state = refl
combineActsC2 flip flip state = sym (Orbit.strictAntipodeTripleInvolutive state)

inverseLeftActsC2 :
  (g : C2) (state : Orbit.TritTriple) ->
  actC2 (inverseC2 g) (actC2 g state) ≡ state
inverseLeftActsC2 identity state = refl
inverseLeftActsC2 flip state = Orbit.strictAntipodeTripleInvolutive state

inverseRightActsC2 :
  (g : C2) (state : Orbit.TritTriple) ->
  actC2 g (actC2 (inverseC2 g) state) ≡ state
inverseRightActsC2 identity state = refl
inverseRightActsC2 flip state = Orbit.strictAntipodeTripleInvolutive state

ternaryTripleC2Action :
  Symmetry.InvertibleSymmetryAction Orbit.TritTriple C2
ternaryTripleC2Action =
  Symmetry.invertibleSymmetryAction
    identity combineC2 inverseC2 actC2
    identityActsC2 combineActsC2 inverseLeftActsC2 inverseRightActsC2

canonicalRepresentative27 : Orbit.AntipodalClass27 -> Orbit.TritTriple
canonicalRepresentative27 Orbit.centre27 =
  Branch.triple SSP.sspZero SSP.sspZero SSP.sspZero
canonicalRepresentative27 (Orbit.firstPositive27 b c) =
  Branch.triple SSP.sspPosOne b c
canonicalRepresentative27 (Orbit.secondPositive27 c) =
  Branch.triple SSP.sspZero SSP.sspPosOne c
canonicalRepresentative27 Orbit.thirdPositive27 =
  Branch.triple SSP.sspZero SSP.sspZero SSP.sspPosOne

representativeInClass27 :
  (orbit : Orbit.AntipodalClass27) ->
  Orbit.classifyAntipodal27 (canonicalRepresentative27 orbit) ≡ orbit
representativeInClass27 Orbit.centre27 = refl
representativeInClass27 (Orbit.firstPositive27 b c) = refl
representativeInClass27 (Orbit.secondPositive27 c) = refl
representativeInClass27 Orbit.thirdPositive27 = refl

transporter27 : Orbit.TritTriple -> C2
transporter27 (Branch.triple SSP.sspPosOne b c) = identity
transporter27 (Branch.triple SSP.sspNegOne b c) = flip
transporter27 (Branch.triple SSP.sspZero SSP.sspPosOne c) = identity
transporter27 (Branch.triple SSP.sspZero SSP.sspNegOne c) = flip
transporter27 (Branch.triple SSP.sspZero SSP.sspZero SSP.sspPosOne) = identity
transporter27 (Branch.triple SSP.sspZero SSP.sspZero SSP.sspNegOne) = flip
transporter27 (Branch.triple SSP.sspZero SSP.sspZero SSP.sspZero) = identity

transporterHits27 :
  (state : Orbit.TritTriple) ->
  actC2 (transporter27 state)
    (canonicalRepresentative27 (Orbit.classifyAntipodal27 state))
  ≡ state
transporterHits27 (Branch.triple SSP.sspPosOne b c) = refl
transporterHits27 (Branch.triple SSP.sspNegOne b c)
  rewrite Orbit.strictAntipodeInvolutive b
        | Orbit.strictAntipodeInvolutive c = refl
transporterHits27 (Branch.triple SSP.sspZero SSP.sspPosOne c) = refl
transporterHits27 (Branch.triple SSP.sspZero SSP.sspNegOne c)
  rewrite Orbit.strictAntipodeInvolutive c = refl
transporterHits27 (Branch.triple SSP.sspZero SSP.sspZero SSP.sspPosOne) = refl
transporterHits27 (Branch.triple SSP.sspZero SSP.sspZero SSP.sspNegOne) = refl
transporterHits27 (Branch.triple SSP.sspZero SSP.sspZero SSP.sspZero) = refl

orbitInvariantC2 :
  (g : C2) (state : Orbit.TritTriple) ->
  Orbit.classifyAntipodal27 (actC2 g state)
  ≡ Orbit.classifyAntipodal27 state
orbitInvariantC2 identity state = refl
orbitInvariantC2 flip state = Orbit.classifyAntipodal27Invariant state

ternary27OrbitPresentation :
  Generic.OrbitPresentation ternaryTripleC2Action
ternary27OrbitPresentation =
  Generic.orbitPresentation
    Orbit.AntipodalClass27
    Orbit.classifyAntipodal27
    canonicalRepresentative27
    orbitInvariantC2
    representativeInClass27
    transporter27
    transporterHits27

Residual27 : Orbit.AntipodalClass27 -> Set
Residual27 = Codec.OrientationResidual27

groupClass27 : (orbit : Orbit.AntipodalClass27) -> C2 -> Residual27 orbit
groupClass27 Orbit.centre27 identity = tt
groupClass27 Orbit.centre27 flip = tt
groupClass27 (Orbit.firstPositive27 b c) identity = Codec.direct
groupClass27 (Orbit.firstPositive27 b c) flip = Codec.counter
groupClass27 (Orbit.secondPositive27 c) identity = Codec.direct
groupClass27 (Orbit.secondPositive27 c) flip = Codec.counter
groupClass27 Orbit.thirdPositive27 identity = Codec.direct
groupClass27 Orbit.thirdPositive27 flip = Codec.counter

groupClassSound27 :
  ∀ {orbit g h} ->
  groupClass27 orbit g ≡ groupClass27 orbit h ->
  Generic.StabilizerEquivalent ternary27OrbitPresentation orbit g h
groupClassSound27 {Orbit.centre27} {identity} {identity} same = refl
groupClassSound27 {Orbit.centre27} {identity} {flip} same = refl
groupClassSound27 {Orbit.centre27} {flip} {identity} same = refl
groupClassSound27 {Orbit.centre27} {flip} {flip} same = refl
groupClassSound27 {Orbit.firstPositive27 b c} {identity} {identity} same = refl
groupClassSound27 {Orbit.firstPositive27 b c} {identity} {flip} ()
groupClassSound27 {Orbit.firstPositive27 b c} {flip} {identity} ()
groupClassSound27 {Orbit.firstPositive27 b c} {flip} {flip} same = refl
groupClassSound27 {Orbit.secondPositive27 c} {identity} {identity} same = refl
groupClassSound27 {Orbit.secondPositive27 c} {identity} {flip} ()
groupClassSound27 {Orbit.secondPositive27 c} {flip} {identity} ()
groupClassSound27 {Orbit.secondPositive27 c} {flip} {flip} same = refl
groupClassSound27 {Orbit.thirdPositive27} {identity} {identity} same = refl
groupClassSound27 {Orbit.thirdPositive27} {identity} {flip} ()
groupClassSound27 {Orbit.thirdPositive27} {flip} {identity} ()
groupClassSound27 {Orbit.thirdPositive27} {flip} {flip} same = refl

groupClassComplete27 :
  ∀ {orbit g h} ->
  Generic.StabilizerEquivalent ternary27OrbitPresentation orbit g h ->
  groupClass27 orbit g ≡ groupClass27 orbit h
groupClassComplete27 {Orbit.centre27} {identity} {identity} same = refl
groupClassComplete27 {Orbit.centre27} {identity} {flip} same = refl
groupClassComplete27 {Orbit.centre27} {flip} {identity} same = refl
groupClassComplete27 {Orbit.centre27} {flip} {flip} same = refl
groupClassComplete27 {Orbit.firstPositive27 b c} {identity} {identity} same = refl
groupClassComplete27 {Orbit.firstPositive27 b c} {identity} {flip} ()
groupClassComplete27 {Orbit.firstPositive27 b c} {flip} {identity} ()
groupClassComplete27 {Orbit.firstPositive27 b c} {flip} {flip} same = refl
groupClassComplete27 {Orbit.secondPositive27 c} {identity} {identity} same = refl
groupClassComplete27 {Orbit.secondPositive27 c} {identity} {flip} ()
groupClassComplete27 {Orbit.secondPositive27 c} {flip} {identity} ()
groupClassComplete27 {Orbit.secondPositive27 c} {flip} {flip} same = refl
groupClassComplete27 {Orbit.thirdPositive27} {identity} {identity} same = refl
groupClassComplete27 {Orbit.thirdPositive27} {identity} {flip} ()
groupClassComplete27 {Orbit.thirdPositive27} {flip} {identity} ()
groupClassComplete27 {Orbit.thirdPositive27} {flip} {flip} same = refl

chooseGroup27 : (orbit : Orbit.AntipodalClass27) -> Residual27 orbit -> C2
chooseGroup27 Orbit.centre27 tt = identity
chooseGroup27 (Orbit.firstPositive27 b c) Codec.direct = identity
chooseGroup27 (Orbit.firstPositive27 b c) Codec.counter = flip
chooseGroup27 (Orbit.secondPositive27 c) Codec.direct = identity
chooseGroup27 (Orbit.secondPositive27 c) Codec.counter = flip
chooseGroup27 Orbit.thirdPositive27 Codec.direct = identity
chooseGroup27 Orbit.thirdPositive27 Codec.counter = flip

chooseGroupRightInverse27 :
  (orbit : Orbit.AntipodalClass27)
  (residual : Residual27 orbit) ->
  groupClass27 orbit (chooseGroup27 orbit residual) ≡ residual
chooseGroupRightInverse27 Orbit.centre27 tt = refl
chooseGroupRightInverse27 (Orbit.firstPositive27 b c) Codec.direct = refl
chooseGroupRightInverse27 (Orbit.firstPositive27 b c) Codec.counter = refl
chooseGroupRightInverse27 (Orbit.secondPositive27 c) Codec.direct = refl
chooseGroupRightInverse27 (Orbit.secondPositive27 c) Codec.counter = refl
chooseGroupRightInverse27 Orbit.thirdPositive27 Codec.direct = refl
chooseGroupRightInverse27 Orbit.thirdPositive27 Codec.counter = refl

ternary27StabilizerResidualPresentation :
  Generic.StabilizerResidualPresentation ternary27OrbitPresentation
ternary27StabilizerResidualPresentation =
  Generic.stabilizerResidualPresentation
    Residual27
    groupClass27
    groupClassSound27
    groupClassComplete27
    chooseGroup27
    chooseGroupRightInverse27

genericOrbitResidualReopens27 :
  (state : Orbit.TritTriple) ->
  Generic.reopenOrbitResidual ternary27StabilizerResidualPresentation
    (Orbit.classifyAntipodal27 state)
    (Generic.orbitResidualOf ternary27StabilizerResidualPresentation state)
  ≡ state
genericOrbitResidualReopens27 =
  Generic.orbitResidualReopensExactly ternary27StabilizerResidualPresentation

record TernaryOrbitStabilizerResidualBoundary : Set where
  constructor ternaryOrbitStabilizerResidualBoundary
  field
    centreResidualIsSingleton : Bool
    noncentralResidualIsOrientationPair : Bool
    variableResidualIsExplainedByStabilizerType : Bool
    genericOrbitResidualReopensExactly : Bool
    antipodalQuotientAloneIsExactCode : Bool

canonicalTernaryOrbitStabilizerResidualBoundary :
  TernaryOrbitStabilizerResidualBoundary
canonicalTernaryOrbitStabilizerResidualBoundary =
  ternaryOrbitStabilizerResidualBoundary true true true true false
