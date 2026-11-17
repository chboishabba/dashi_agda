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
open import Agda.Builtin.Maybe using (Maybe)
open import Data.Nat.DivMod using (_%_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Agda.Builtin.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (trans; sym)

import DASHI.Foundations.SSPTritCarrier as T
import DASHI.Foundations.BalancedTernaryAntipodalOrbitExact as Orbit
import DASHI.Arithmetic.TwinPrime369IbrahimQuotientBoundaryExact as OriginalCubeBridge
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Wikimedia.IbrahimMonsterTernary27PhasePreservingFiveOrbitReductionExact as Ibrahim
import DASHI.Arithmetic.TwinPrimeTernary270AffineCRTCodecExact as Codec
import DASHI.Arithmetic.TwinPrimeTernary270SurvivorCoverageExact as Wheel
import DASHI.Arithmetic.SignedSSPOrientationTwinClassifierNoGoExact as Certified
import DASHI.Arithmetic.FiniteTwinSieveFactorableLiftExact as Factor
import Data.Nat.Primality as NatPrime
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

------------------------------------------------------------------------
-- STRONGER NO-GO: the GLOBAL 14-class C2 quotient also collides.
--
-- The input pair 59/209 belongs to the same *global* antipodal
-- 3x3x3 orbit (x=0 is fixed; y,z flip). Original 27->14 owner
-- remains untouched. PR #1244 owns the independent arbitrary-depth
-- T^(n+1)/S3 vs T^n/C2 word-normalisation theorem; the general
-- equivalence is not imported from an unmerged branch.
------------------------------------------------------------------------

globalAntipodeSends59To209 :
  Codec.cube270GlobalAntipode realTwinCubePoint
    ≡ compositeTwinCubePoint
globalAntipodeSends59To209 = refl

globalFourteenClass :
  Geometry.Ternary27Point → Orbit.AntipodalClass27
globalFourteenClass p =
  Orbit.classifyAntipodal27
    (OriginalCubeBridge.geometryAsTritTriple p)

sameGlobalFourteenOrbitInsideWheel :
  globalFourteenClass realTwinCubePoint
    ≡ globalFourteenClass compositeTwinCubePoint
sameGlobalFourteenOrbitInsideWheel = refl

globalFourteenOrbitLosesTwinConsumer :
  Core.ConsumerCollision globalFourteenClass realTwinStartOnCube
globalFourteenOrbitLosesTwinConsumer =
  NF.nonFactorabilityWitness
    realTwinCubePoint compositeTwinCubePoint
    sameGlobalFourteenOrbitInsideWheel
    differentTwinAnswersInsideWheel

noTwinClassifierFromBareGlobalFourteenOrbit :
  Core.ConsumerSufficient globalFourteenClass
    realTwinStartOnCube → ⊥
noTwinClassifierFromBareGlobalFourteenOrbit =
  Core.collisionRefutesSufficiency
    globalFourteenOrbitLosesTwinConsumer

------------------------------------------------------------------------
-- STRONGEST FINITE CODE NO-GO: even the FULL 27-cell wheel point is
-- not the whole integer. It remembers n mod 270, not the quotient.
--
-- 59 and 329 are the SAME residue/cube point:
-- 329 = 59 + 270 = 7 * 47, yet 59 and 61 are both prime.
-- No classifier on the 27 cube states can decide all Nat twin starts.
-- This is an arithmetic consumer collision, not a distribution claim.
------------------------------------------------------------------------

wholeNatToWheelCube : Nat → Maybe Geometry.Ternary27Point
wholeNatToWheelCube n = Codec.wheel270ToCube (n % 270)

fiftyNineAndThreeTwentyNineSameFullCube :
  wholeNatToWheelCube 59 ≡ wholeNatToWheelCube 329
fiftyNineAndThreeTwentyNineSameFullCube = refl

threeTwentyNineIsComposite : NatPrime.Composite 329
threeTwentyNineIsComposite =
  Factor.twoNontrivialFactorsAreComposite 329
    (Factor.twoNontrivialFactors 5 45 refl)

trueTwin59 : Certified.twinStartBool 59 ≡ true
trueTwin59 = refl

notTwin329 : Certified.twinStartBool 329 ≡ false
notTwin329 = refl

natTwinConsumerDistinguishes59And329 :
  Certified.twinStartBool 59 ≡ Certified.twinStartBool 329 → ⊥
natTwinConsumerDistinguishes59And329 same =
  trueCannotEqualFalse
    (trans (sym trueTwin59) (trans same notTwin329))

wholeCubeResidueLosesTwinConsumer :
  Core.ConsumerCollision wholeNatToWheelCube Certified.twinStartBool
wholeCubeResidueLosesTwinConsumer =
  NF.nonFactorabilityWitness
    59 329
    fiftyNineAndThreeTwentyNineSameFullCube
    natTwinConsumerDistinguishes59And329

noUniversalTwinClassifierFromFiniteWholeCube :
  Core.ConsumerSufficient wholeNatToWheelCube
    Certified.twinStartBool → ⊥
noUniversalTwinClassifierFromFiniteWholeCube =
  Core.collisionRefutesSufficiency
    wholeCubeResidueLosesTwinConsumer

-- The correction is a quotient/residual code retaining the unbounded
-- period index, not an arithmetic-primality claim from orbit counts.
-- Any true Nat->(residue,period) lift must prove an exact arithmetic
-- round trip and retain enough information for the prime decider.
