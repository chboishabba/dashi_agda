module DASHI.Arithmetic.TwinPrimeConsumerParetoObserverExact where

------------------------------------------------------------------------
-- PR #1407 CROSS-POLLINATION; NO BRANCH-ONLY IMPORT.
--
-- IMPORTANT: PR #1407's 27-mode carrier is NOT 27 unstructured labels:
--    (x,y,z) in {-1,0,+1} x {-1,0,+1} x {-1,0,+1},
--    exactly THREE independent ternary coordinates, 3 x 3 x 3 = 27.
--    Two ordered input cubes form SIX coordinates, 3^6 = 729.
-- The existing Base369Ternary27HypervoxelFabricGeometryExact owner
-- already proves the three-axis structure. Reuse, never flatten.
-- This geometry is a representation/observer, NOT prime divisibility.
--
-- Source-written donor in chboishabba/dashi_agda PR #1407:
--   R2P227729FourGridRetainedQuadraticParetoExact
--     shows a coarse N=4 observation adequate for *retained* output
--     while N=5 is required for the declared full output;
--   R2P2369WaveOpticalCombInformationCutExact
--     uses the preexisting ConsumerCollision and exact residual coding.
--
-- THIS MODULE REUSES the older, default-branch theorem owners:
--   Core.IndexedRelationalHyperfabricSpineExact
--   Core.IntersectionalNonFactorability
--   Foundations.Base369WaveContinuousSymbolicCodingExact
--   Biology.SignedSSPFRACTRANWeaveExact
--   Arithmetic.SignedSSPOrientationTwinClassifierNoGoExact
--   Arithmetic.CertifiedPrimePairModulusExact
--
-- This is consumer-specific sufficiency, not an imported physics or
-- Fourier theorem, a Monster 3B/4B same-object representation, or a
-- prime-distribution estimate. Preserve Ibrahim prior proof ownership.
--
-- CONCRETE CUT: 5 and 35 have the same residue modulo 6, yet only
-- 5 starts a genuine twin pair (5,7); 35 is composite (35,37).
-- Thus the finite six-wheel observation CANNOT determine TwinPrimeAt.
-- No postprocessing of that lost residue can repair the collision.
-- A richer symbolic (trit + exact Nat residual) code DOES retain
-- the arithmetic twin-prime consumer, using the preexisting codec.
--
-- Source-written Agda; do not claim kernel-verified typechecking.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (_%_)
open import Data.Empty using (⊥; ⊥-elim)
open import Agda.Builtin.List using (List)
open import Relation.Nullary using (yes; no)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Core.IndexedRelationalHyperfabricSpineExact as Core
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.BalancedTernaryAntipodalOrbitExact as Antipodal
import DASHI.Foundations.Base369WaveContinuousSymbolicCodingExact as Wave
import DASHI.Arithmetic.SignedSSPOrientationTwinClassifierNoGoExact as Twin
import DASHI.Arithmetic.CertifiedPrimePairModulusExact as Pair
import DASHI.Arithmetic.CertifiedPrimePairPeriodExact as Period

------------------------------------------------------------------------
-- THREE AXES, NOT TWENTY-SEVEN UNRELATED LABELS.
-- Reuse the original x/y/z ternary-point carrier and its count theorem.
-- The ordered pair is two *typed* 3x3x3 cubes (six trit coordinates).
--
-- Do not identify this with an arithmetic prime modulus, CRT triple,
-- a Monster class, or the physical Fourier operator of PR #1407.
------------------------------------------------------------------------

ThreeByThreeByThree : Set
ThreeByThreeByThree = Geometry.Ternary27Point

toThreeCoordinates :
  ThreeByThreeByThree →
  SSP.SSPTrit × (SSP.SSPTrit × SSP.SSPTrit)
toThreeCoordinates point =
  Geometry.x point , (Geometry.y point , Geometry.z point)

fromThreeCoordinates :
  SSP.SSPTrit × (SSP.SSPTrit × SSP.SSPTrit) →
  ThreeByThreeByThree
fromThreeCoordinates (x , (y , z)) =
  Geometry.ternary27Point x y z

threeCoordinateDecodeEncode :
  (point : ThreeByThreeByThree) →
  fromThreeCoordinates (toThreeCoordinates point) ≡ point
threeCoordinateDecodeEncode (Geometry.ternary27Point x y z) = refl

threeCoordinateEncodeDecode :
  (coords : SSP.SSPTrit × (SSP.SSPTrit × SSP.SSPTrit)) →
  toThreeCoordinates (fromThreeCoordinates coords) ≡ coords
threeCoordinateEncodeDecode (x , (y , z)) = refl

threeAxisCountIsThree :
  Geometry.axisCount ≡ 3
threeAxisCountIsThree = refl

threeAxisCapacityIsThreeTimesThreeTimesThree :
  Geometry.hypervoxelStateCount ≡ 3 * 3 * 3
threeAxisCapacityIsThreeTimesThreeTimesThree = refl

threeAxisCapacityIsTwentySeven :
  Geometry.hypervoxelStateCount ≡ 27
threeAxisCapacityIsTwentySeven =
  Geometry.hypervoxelStateCountIs27

-- The *same* underlying 3x3x3 geometry has a strict C2 antipode.
-- Under that action, the unique all-zero centre is fixed and 26 other
-- points form 13 sign-opposite pairs. Reuse the existing source owner;
-- a class count is NOT a primality predicate or a lossless code.
threeAxisCapacityIsCentrePlusThirteenAntipodalPairs :
  Geometry.hypervoxelStateCount ≡ 1 + 13 * 2
threeAxisCapacityIsCentrePlusThirteenAntipodalPairs =
  Antipodal.ternaryCubeCountDecomposesAsCentrePlusThirteenPairs

threeAxisAntipodalOrbitCountIsFourteen :
  Antipodal.antipodalClass27Count ≡ 14
threeAxisAntipodalOrbitCountIsFourteen =
  Antipodal.antipodalClass27CountIsFourteen

OrderedThreeCubePair : Set
OrderedThreeCubePair = ThreeByThreeByThree × ThreeByThreeByThree

orderedPairAxisCountIsSix :
  Geometry.axisCount + Geometry.axisCount ≡ 6
orderedPairAxisCountIsSix = refl

orderedPairCapacityIsSevenHundredTwentyNine :
  Geometry.hypervoxelStateCount * Geometry.hypervoxelStateCount ≡ 729
orderedPairCapacityIsSevenHundredTwentyNine = refl

sixWheelObservation : Nat → Nat
sixWheelObservation n = n % 6

fiveAndThirtyFiveSameSixWheel :
  sixWheelObservation 5 ≡ sixWheelObservation 35
fiveAndThirtyFiveSameSixWheel = refl

twinAtThirtyFiveIsFalse : Twin.twinStartBool 35 ≡ false
twinAtThirtyFiveIsFalse = refl

fiveAndThirtyFiveTwinAnswersDiffer :
  Twin.twinStartBool 5 ≡ Twin.twinStartBool 35 → ⊥
fiveAndThirtyFiveTwinAnswersDiffer equality =
  Twin.trueNotFalse
    (trans
      (sym Twin.twinAtFiveIsTrue)
      (trans equality twinAtThirtyFiveIsFalse))

-- Reuse the existing GENERIC collision theorem, not a local duplicate.
wheelTwinCollision :
  Core.ConsumerCollision sixWheelObservation Twin.twinStartBool
wheelTwinCollision =
  NF.nonFactorabilityWitness
    5 35
    fiveAndThirtyFiveSameSixWheel
    fiveAndThirtyFiveTwinAnswersDiffer

wheelCannotDecideActualTwins :
  Core.ConsumerSufficient sixWheelObservation Twin.twinStartBool → ⊥
wheelCannotDecideActualTwins =
  Core.collisionRefutesSufficiency wheelTwinCollision

-- If an SSP/369 chart stores only the wheel class, renaming it or
-- applying any function cannot recover actual arithmetic primality.
postprocessedWheelStillCannotDecideTwins :
  ∀ {Chart : Set} →
  (rechart : Nat → Chart) →
  Core.ConsumerSufficient
    (λ n → rechart (sixWheelObservation n))
    Twin.twinStartBool → ⊥
postprocessedWheelStillCannotDecideTwins rechart =
  Core.collisionSurvivesRechart rechart wheelTwinCollision

-- A small symbolic quotient may be lossy, but is useful for queries
-- declared at its own resolution. For actual twin-prime results, keep
-- the full arithmetic source state as the residual alongside its trit.
tritFromModThree : Nat → SSP.SSPTrit
tritFromModThree n with n % 3
... | zero = SSP.sspZero
... | suc zero = SSP.sspPosOne
... | suc (suc k) = SSP.sspNegOne

primeSieveSymbolicCoding : Wave.SymbolicCoding Nat
primeSieveSymbolicCoding = Wave.symbolicCoding tritFromModThree

exactTwinQueryCode :
  Nat → Wave.EncodedState primeSieveSymbolicCoding
exactTwinQueryCode = Wave.encode primeSieveSymbolicCoding

exactTwinQueryCodeRoundTrip :
  (n : Nat) →
  Wave.decode (exactTwinQueryCode n) ≡ n
exactTwinQueryCodeRoundTrip =
  Wave.decodeAfterEncode primeSieveSymbolicCoding

-- This is a genuine sufficient representation of the true twin
-- consumer, but retaining all of Nat adds no analytical information.
exactTwinQueryCodeIsConsumerSufficient :
  Core.ConsumerSufficient exactTwinQueryCode Twin.twinStartBool
exactTwinQueryCodeIsConsumerSufficient =
  NF.factorsThrough
    (λ code → Twin.twinStartBool (Wave.decode code))
    (λ n →
      sym (cong Twin.twinStartBool (exactTwinQueryCodeRoundTrip n)))

------------------------------------------------------------------------
-- FINITE SIEVE QUERY: an explicit Boolean is a sufficient OBSERVATION
-- for the Boolean finite-survival query (not for Prime(n)).
-- Existing CertifiedPrimePairModulusExact supplies the proof-carrying
-- decision, and CertifiedPrimePairPeriodExact proves periodicity.
------------------------------------------------------------------------

finiteSieveBit : List Pair.CertifiedPrimeAxis → Nat → Bool
finiteSieveBit axes n with Pair.allPairSurvive? axes n
... | yes _ = true
... | no _ = false

sieveBitIsSufficientForFiniteSieveQuery :
  (axes : List Pair.CertifiedPrimeAxis) →
  Core.ConsumerSufficient (finiteSieveBit axes) (finiteSieveBit axes)
sieveBitIsSufficientForFiniteSieveQuery axes =
  NF.factorsThrough (λ result → result) (λ n → refl)

-- In contrast to the full arithmetic twin predicate, this finite
-- screening result is periodic in the product of its prime moduli.
-- The two impossible cases are eliminated by the pre-existing
-- TWO-WAY transport of genuine AllPairSurvive certificates.
finiteSieveBitPeriodic :
  (axes : List Pair.CertifiedPrimeAxis) →
  (n : Nat) →
  finiteSieveBit axes n
    ≡ finiteSieveBit axes (n + Period.modulusProduct axes)
finiteSieveBitPeriodic axes n
  with Pair.allPairSurvive? axes n
     | Pair.allPairSurvive? axes (n + Period.modulusProduct axes)
... | yes valid | yes shifted = refl
... | yes valid | no invalidShifted =
  ⊥-elim (invalidShifted (Period.allPairProductPeriodic axes n valid))
... | no invalid | yes validShifted =
  ⊥-elim (invalid (Period.allPairProductPeriodicBack axes n validShifted))
... | no invalid | no invalidShifted = refl
