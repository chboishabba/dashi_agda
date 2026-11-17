module DASHI.Arithmetic.TwinPrime369IbrahimQuotientBoundaryExact where

------------------------------------------------------------------------
-- REUSE: 3x3x3, 3x5=15, global C2 quotient 14, 14 PRIMEGAME rules.
--
-- Original source owners (NO edits):
--   Base369Ternary27HypervoxelFabricGeometryExact.Ternary27Point
--   BalancedTernaryAntipodalOrbitExact: 27=1+13*2, 14 global classes
--   BalancedTernaryAntipodalResidualCodecExact: exact 27 <-> 14+sign
--   IbrahimMonsterTernary27PhasePreservingFiveOrbitReductionExact:
--     phase-preserving 27 -> 3 x 5 = 15 via INNER antipodal quotient
--   IbrahimMonster42dFifteenFourteenPhaseCarrierExact:
--     a DIFFERENT 15 -> 14 residual-lane carrier
--   PrimegameSSP15CarrierFactorisationExact: 14 Guy FRACTRAN rules,
--     10 distinct used typed prime factors of the SSP15 Ogg atlas
--
-- NEW: an explicit collision showing the 3x5=15 inner quotient
-- erases the sign of an inner axis. A residual-preserving 27<->14
-- code, inherited from the original owner, DOES round-trip the
-- complete x/y/z state. These are comparisons between distinct
-- carriers and *not* equal-object Monster representations or an
-- arithmetic twin-primality theorem.
--
-- External: Conway 1987, Guy 1983 FRACTRAN prior art; Serre 1977
-- finite group orbit theory. Ibrahim prior Monster 3B proof ownership
-- remains unchanged. No numeric coincidence is promoted to physics.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (sym)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import Data.Product using (_×_; _,_)

import DASHI.Foundations.SSPTritCarrier as Trit
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369AddressSymmetryAndBranchGeometryExact as Branch
import DASHI.Foundations.BalancedTernaryAntipodalOrbitExact as Orbit
import DASHI.Foundations.BalancedTernaryAntipodalResidualCodecExact as Codec
import DASHI.Wikimedia.IbrahimMonsterTernary27PhasePreservingFiveOrbitReductionExact as Ibrahim
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SSP
import DASHI.Arithmetic.PrimegameSSP15CarrierFactorisationExact as Guy
import DASHI.Arithmetic.TwinPrimeThreeAxisLocalThreeOrbitExact as LocalThree
import DASHI.Arithmetic.SignedSSPOrientationTwinClassifierNoGoExact as Twin

import DASHI.Foundations.Base369NDimParetoChartExact as NineAxes
import DASHI.Core.IndexedRelationalHyperfabricSpineExact as Core
import DASHI.Core.IntersectionalNonFactorability as NF

-- Keep the product decomposition, not merely the numeral 27.
typedCubeCapacity : Geometry.hypervoxelStateCount ≡ 3 * 3 * 3
typedCubeCapacity = refl

innerNineOrbitCountIsFive :
  Ibrahim.innerOrbitCount ≡ 5
innerNineOrbitCountIsFive = refl

phasePreservingThreeTimesFiveIsFifteen :
  Ibrahim.phaseOrbitStateCount ≡ 3 * 5
phasePreservingThreeTimesFiveIsFifteen = refl

phasePreservingFifteen :
  Ibrahim.phaseOrbitStateCount ≡ 15
phasePreservingFifteen = Ibrahim.phaseOrbitStateCountIsFifteen

strictGlobalAntipodalFourteen :
  Orbit.antipodalClass27Count ≡ 14
strictGlobalAntipodalFourteen =
  Orbit.antipodalClass27CountIsFourteen

historicalGuyFourteenRules :
  SSP.listCount Guy.guyFourteenTyped ≡ 14
historicalGuyFourteenRules =
  Guy.guyProgrammeRuleCountIsFourteen

originalOggFifteenPrimes :
  SSP.listCount SSP.canonicalSSPPrimes ≡ 15
originalOggFifteenPrimes =
  SSP.canonicalSSPPrimeCountIsFifteen

primegameUsesTenPrimes :
  SSP.listCount Guy.primegameSupportInsideSSP15 ≡ 10
primegameUsesTenPrimes =
  Guy.primegameUsesTenTypedCarriers

-- The inner-axis C2 involution identifies these distinct y signs.
-- Its equality is already supplied by the original Ibrahim owner.
positiveInnerPoint : Geometry.Ternary27Point
positiveInnerPoint =
  Geometry.ternary27Point
    Trit.sspZero Trit.sspPosOne Trit.sspZero

negativeInnerPoint : Geometry.Ternary27Point
negativeInnerPoint =
  Geometry.ternary27Point
    Trit.sspZero Trit.sspNegOne Trit.sspZero

sameThreeTimesFivePhaseOrbit :
  Ibrahim.reduce27ToPhaseOrbit15 positiveInnerPoint
    ≡ Ibrahim.reduce27ToPhaseOrbit15 negativeInnerPoint
sameThreeTimesFivePhaseOrbit = refl

innerYCoordinateDiffers :
  Geometry.y positiveInnerPoint ≡ Geometry.y negativeInnerPoint → ⊥
innerYCoordinateDiffers ()

-- Explicit generic consumer collision: the 3x5 quotient CANNOT
-- answer the full signed y-axis query. It has deliberately lost it.
phaseOrbitYCollision :
  Core.ConsumerCollision
    Ibrahim.reduce27ToPhaseOrbit15 Geometry.y
phaseOrbitYCollision =
  NF.nonFactorabilityWitness
    positiveInnerPoint negativeInnerPoint
    sameThreeTimesFivePhaseOrbit innerYCoordinateDiffers

phaseOrbitCannotRecoverSignedY :
  Core.ConsumerSufficient
    Ibrahim.reduce27ToPhaseOrbit15 Geometry.y → ⊥
phaseOrbitCannotRecoverSignedY =
  Core.collisionRefutesSufficiency phaseOrbitYCollision

-- Exact 27 -> global antipodal class + DEPENDENT orientation residual:
-- this original source-owned codec does preserve all three axes.
geometryAsTritTriple :
  Geometry.Ternary27Point → Orbit.TritTriple
geometryAsTritTriple (Geometry.ternary27Point x y z) =
  Branch.triple x y z

tritTripleAsGeometry :
  Orbit.TritTriple → Geometry.Ternary27Point
tritTripleAsGeometry (Branch.triple x y z) =
  Geometry.ternary27Point x y z

tripleGeometryRoundTrip :
  (point : Geometry.Ternary27Point) →
  tritTripleAsGeometry (geometryAsTritTriple point) ≡ point
tripleGeometryRoundTrip (Geometry.ternary27Point x y z) = refl

geometryTripleRoundTrip :
  (triple : Orbit.TritTriple) →
  geometryAsTritTriple (tritTripleAsGeometry triple) ≡ triple
geometryTripleRoundTrip (Branch.triple x y z) = refl

fullSignedCubeCode :
  Geometry.Ternary27Point → Codec.AntipodalCode27
fullSignedCubeCode point =
  Codec.encode27 (geometryAsTritTriple point)

decodeFullSignedCubeCode :
  Codec.AntipodalCode27 → Geometry.Ternary27Point
decodeFullSignedCubeCode code =
  tritTripleAsGeometry (Codec.decode27 code)

fullSignedCubeRoundTrip :
  (point : Geometry.Ternary27Point) →
  decodeFullSignedCubeCode (fullSignedCubeCode point) ≡ point
fullSignedCubeRoundTrip point =
  trans
    (cong tritTripleAsGeometry
      (Codec.decodeAfterEncode27 (geometryAsTritTriple point)))
    (tripleGeometryRoundTrip point)

-- A source-faithful table of equal CARDINALITIES, not identification
-- of 14 FRACTRAN instructions with 14 Monster/Ogg orbits.
countComparisonIsNotATypedEquivalence :
  (Ibrahim.phaseOrbitStateCount ≡ 15)
    × (Orbit.antipodalClass27Count ≡ 14)
    × (SSP.listCount Guy.guyFourteenTyped ≡ 14)
countComparisonIsNotATypedEquivalence =
  phasePreservingFifteen ,
  (strictGlobalAntipodalFourteen , historicalGuyFourteenRules)

------------------------------------------------------------------------
-- NUMERICAL CROSS-POLLINATION MUST RETAIN ITS OPERATION.
-- Three Cartesian triples produce NINE ternary axes: 3^(3+3+3),
-- not a proof that 3^5 and 5^3 are the same object.
------------------------------------------------------------------------

nineAxisGroupingIsThreeCartesianCubes :
  NineAxes.ternaryNineAxisProfileCount
    ≡ (3 * 3 * 3) * (3 * 3 * 3) * (3 * 3 * 3)
nineAxisGroupingIsThreeCartesianCubes = refl

threeToFifthIs243 :
  3 * 3 * 3 * 3 * 3 ≡ 243
threeToFifthIs243 = refl

fiveCubedIs125 :
  5 * 5 * 5 ≡ 125
fiveCubedIs125 = refl

threeToFifthDoesNotEqualFiveCubed :
  (3 * 3 * 3 * 3 * 3 ≡ 5 * 5 * 5) → ⊥
threeToFifthDoesNotEqualFiveCubed ()

-- No same-object Monster character identity, D4 module equivalence,
-- all-prime emitter, or prime correlation follows from these counts.

------------------------------------------------------------------------
-- STRONG ARITHMETIC COUNTEREXAMPLE TO THE 3x5=15 QUOTIENT.
--
-- In the actual prime-3 slice (outer trit x=-1), the inner pair
-- (-1,+1) encodes 5, and its antipode (+1,-1) encodes 20.
-- The quotient identifies them, but twin-primality is different:
-- Prime(5) × Prime(7) is inhabited; Prime(20) is not.
------------------------------------------------------------------------

twinFivePoint : Geometry.Ternary27Point
twinFivePoint =
  Geometry.ternary27Point
    Trit.sspNegOne Trit.sspNegOne Trit.sspPosOne

nonTwinTwentyPoint : Geometry.Ternary27Point
nonTwinTwentyPoint =
  Geometry.ternary27Point
    Trit.sspNegOne Trit.sspPosOne Trit.sspNegOne

twinFivePointRepresentsFive :
  LocalThree.centeredPrimeThreeResidue
    (Geometry.y twinFivePoint) (Geometry.z twinFivePoint) ≡ 5
twinFivePointRepresentsFive = refl

nonTwinTwentyPointRepresentsTwenty :
  LocalThree.centeredPrimeThreeResidue
    (Geometry.y nonTwinTwentyPoint) (Geometry.z nonTwinTwentyPoint)
    ≡ 20
nonTwinTwentyPointRepresentsTwenty = refl

samePhaseOrbitForFiveAndTwenty :
  Ibrahim.reduce27ToPhaseOrbit15 twinFivePoint
    ≡ Ibrahim.reduce27ToPhaseOrbit15 nonTwinTwentyPoint
samePhaseOrbitForFiveAndTwenty = refl

-- The total observer below extends the true arithmetic query from
-- the x=-1 slice. The collision uses two actual x=-1 members.
sliceTwinPredicate : Geometry.Ternary27Point → Bool
sliceTwinPredicate p =
  Twin.twinStartBool
    (LocalThree.centeredPrimeThreeResidue
      (Geometry.y p) (Geometry.z p))

twinFiveSliceIsTrue : sliceTwinPredicate twinFivePoint ≡ true
twinFiveSliceIsTrue = Twin.twinAtFiveIsTrue

nonTwinTwentySliceIsFalse :
  sliceTwinPredicate nonTwinTwentyPoint ≡ false
nonTwinTwentySliceIsFalse = refl

distinctTrueTwinAnswers :
  sliceTwinPredicate twinFivePoint
    ≡ sliceTwinPredicate nonTwinTwentyPoint → ⊥
distinctTrueTwinAnswers same =
  Twin.trueNotFalse
    (trans
      (sym twinFiveSliceIsTrue)
      (trans same nonTwinTwentySliceIsFalse))

ibrahimPhaseOrbitLosesTwinPrimeAnswer :
  Core.ConsumerCollision
    Ibrahim.reduce27ToPhaseOrbit15 sliceTwinPredicate
ibrahimPhaseOrbitLosesTwinPrimeAnswer =
  NF.nonFactorabilityWitness
    twinFivePoint nonTwinTwentyPoint
    samePhaseOrbitForFiveAndTwenty distinctTrueTwinAnswers

cannotDecideTwinFromThreeTimesFivePhaseAlone :
  Core.ConsumerSufficient
    Ibrahim.reduce27ToPhaseOrbit15 sliceTwinPredicate → ⊥
cannotDecideTwinFromThreeTimesFivePhaseAlone =
  Core.collisionRefutesSufficiency
    ibrahimPhaseOrbitLosesTwinPrimeAnswer
