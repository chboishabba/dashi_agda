module DASHI.Arithmetic.TwinPrimeTernary270IbrahimSurvivorCollisionExact where

------------------------------------------------------------------------
-- IN-SIEVE CONSUMER COLLISION: ORIGINAL IBRAHIM 3 x 5 PHASE QUOTIENT
--
-- Original exact finite structural owners:
--   Base369Ternary27HypervoxelFabricGeometryExact: T3 = 3 x 3 x 3
--   IbrahimMonsterTernary27PhasePreservingFiveOrbitReductionExact:
--     retain outer x, quotient inner antipodal pair y,z: 27 -> 15
--   IndexedRelationalHyperfabricSpineExact: ConsumerCollision
--   IntersectionalNonFactorability: nonFactorabilityWitness
--   TwinPrimeTernary270AffineCRTCodecExact: exact arithmetic code
--   TwinPrimeCertifiedEnumeratorExact: proof-bearing Nat primality
--
-- Unlike the earlier 5 vs 20 collision (outside the 2/3/5 wheel),
-- this collision uses TWO ACTUAL survivors within the same typed cube:
--     x=0, y=-1,z=+1  -> 59  (59,61 are both prime)
--     x=0, y=+1,z=-1  -> 209 (209=11*19 is composite).
-- These are the SAME Ibrahim inner-phase orbit at fixed x=0.
--
-- Thus even AFTER applying the finite wheel, the lossy 3 x 5
-- quotient cannot determine genuine twin-primality. The full 3 x 3 x 3
-- and its residual are required to preserve the arithmetic input.
-- Nothing asserts a Monster 3B same-object identification.
--
-- Source-written, kernel-pending. Original Ibrahim prior ownership,
-- Conway/Guy and classical arithmetic authorship unchanged.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Agda.Builtin.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (trans; sym)

import DASHI.Foundations.SSPTritCarrier as T
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Wikimedia.IbrahimMonsterTernary27PhasePreservingFiveOrbitReductionExact as Ibrahim
import DASHI.Arithmetic.TwinPrimeTernary270AffineCRTCodecExact as Codec
import DASHI.Arithmetic.TwinPrimeTernary270SurvivorCoverageExact as Wheel
import DASHI.Arithmetic.SignedSSPOrientationTwinClassifierNoGoExact as Certified
import DASHI.Core.IndexedRelationalHyperfabricSpineExact as Core
import DASHI.Core.IntersectionalNonFactorability as NF

realTwinCubePoint : Geometry.Ternary27Point
realTwinCubePoint =
  Geometry.ternary27Point
    T.sspZero T.sspNegOne T.sspPosOne

compositeTwinCubePoint : Geometry.Ternary27Point
compositeTwinCubePoint =
  Geometry.ternary27Point
    T.sspZero T.sspPosOne T.sspNegOne

realTwinCubeCodes59 :
  Codec.cubeToWheel270 realTwinCubePoint ≡ 59
realTwinCubeCodes59 = refl

compositeTwinCubeCodes209 :
  Codec.cubeToWheel270 compositeTwinCubePoint ≡ 209
compositeTwinCubeCodes209 = refl

-- These are not merely arbitrary numbers sharing a quotient:
-- both are local survivors of every selected sieve prime.
realTwinCubePassesWheel : Wheel.Wheel270Survives 59
realTwinCubePassesWheel =
  ((λ ()) , (λ ())) ,
  (((λ ()) , (λ ())) ,
    (((λ ()) , (λ ())) , tt))

compositeTwinCubePassesWheel : Wheel.Wheel270Survives 209
compositeTwinCubePassesWheel =
  ((λ ()) , (λ ())) ,
  (((λ ()) , (λ ())) ,
    (((λ ()) , (λ ())) , tt))

-- Ibrahim's own same-outer-coordinate inner antipode, not an
-- invented Monster or modular-arithmetic group action.
sameIbrahimOrbitInsideWheel :
  Ibrahim.reduce27ToPhaseOrbit15 realTwinCubePoint
  ≡ Ibrahim.reduce27ToPhaseOrbit15 compositeTwinCubePoint
sameIbrahimOrbitInsideWheel =
  sym (Ibrahim.reduce27InnerInversionInvariant realTwinCubePoint)

-- Exactly the proof-bearing two-prime decider from the previous
-- repo owner (ultimately stdlib Prime); no phase-based oracle.
realTwinStartOnCube : Geometry.Ternary27Point → Bool
realTwinStartOnCube p =
  Certified.twinStartBool (Codec.cubeToWheel270 p)

realTwin59IsTrue :
  realTwinStartOnCube realTwinCubePoint ≡ true
realTwin59IsTrue = refl

composite209IsNotTwin :
  realTwinStartOnCube compositeTwinCubePoint ≡ false
composite209IsNotTwin = refl

trueCannotEqualFalse : true ≡ false → ⊥
trueCannotEqualFalse ()

differentTwinAnswersInsideWheel :
  realTwinStartOnCube realTwinCubePoint
  ≡ realTwinStartOnCube compositeTwinCubePoint → ⊥
differentTwinAnswersInsideWheel same =
  trueCannotEqualFalse
    (trans
      (sym realTwin59IsTrue)
      (trans same composite209IsNotTwin))

ibrahimFifteenFailsActualTwinConsumerWithinWheel :
  Core.ConsumerCollision
    Ibrahim.reduce27ToPhaseOrbit15 realTwinStartOnCube
ibrahimFifteenFailsActualTwinConsumerWithinWheel =
  NF.nonFactorabilityWitness
    realTwinCubePoint compositeTwinCubePoint
    sameIbrahimOrbitInsideWheel differentTwinAnswersInsideWheel

noTwinClassifierFromBareIbrahimPhaseWithinWheel :
  Core.ConsumerSufficient
    Ibrahim.reduce27ToPhaseOrbit15 realTwinStartOnCube → ⊥
noTwinClassifierFromBareIbrahimPhaseWithinWheel =
  Core.collisionRefutesSufficiency
    ibrahimFifteenFailsActualTwinConsumerWithinWheel
