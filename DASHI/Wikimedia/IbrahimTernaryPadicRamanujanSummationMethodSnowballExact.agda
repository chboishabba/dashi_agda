module DASHI.Wikimedia.IbrahimTernaryPadicRamanujanSummationMethodSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimTernaryGeometricPartialSumRegularisationOEISSnowballExact as Geo
import DASHI.Wikimedia.IbrahimA003462BalancedTernaryResidualCodecSnowballExact as CodecSnowball
import DASHI.Moonshine.RamanujanTauHecke23Exact
import DASHI.Physics.Closure.RogersRamanujanP5Receipt
import DASHI.Mathematics.NumberTheory.PartitionHardyRamanujanErdosBridgeExact

------------------------------------------------------------------------
-- TERNARY GEOMETRIC SERIES: METHOD/TOPLOGY-SENSITIVE VALUE DISCIPLINE
--
-- Keep the following distinct:
--
--   S_n = 1 + 3 + ... + 3^(n-1) = (3^n - 1)/2  [finite, A003462]
--   sum_{k>=0} 3^k over R                           [diverges]
--   rational-function continuation 1/(1-x)|_{x=3}  [-1/2]
--   3-adic geometric sum in Q_3                     [-1/2]
--
-- The equality of the last two values does not identify the methods.
-- In Q_3, |3|_3 < 1, so the geometric series genuinely converges there.
--
-- Index shift remains explicit:
--
--   1 + 3 + 9 + ...  -> -1/2 in Q_3
--   3 + 9 + 27 + ... -> -3/2 in Q_3.
--
-- Ramanujan-related DASHI lanes are separately typed:
--   * Ramanujan tau / Hecke / moonshine,
--   * Rogers--Ramanujan prime-5 q-series,
--   * Hardy--Ramanujan partition asymptotics.
-- None of these names the 3-adic convergence theorem by itself.
------------------------------------------------------------------------

data SummationMethod : Set where
  ordinaryRealLimit : SummationMethod
  rationalFunctionContinuation : SummationMethod
  threeAdicLimit : SummationMethod
  ramanujanSummation : SummationMethod
  abelSummation : SummationMethod
  cesaroSummation : SummationMethod

record MethodValueReceipt : Set where
  constructor method-value-receipt
  field
    displayedSeries : String
    method : SummationMethod
    assignedValue : String
    convergesInMethodTopology : Bool
    sameAsOrdinaryRealSum : Bool
    sourceStatus : String
open MethodValueReceipt public

realFromZero : MethodValueReceipt
realFromZero = method-value-receipt
  "1 + 3 + 9 + 27 + ..."
  ordinaryRealLimit
  "no finite value"
  false
  false
  "ordinary real partial sums diverge"

rationalContinuationFromZero : MethodValueReceipt
rationalContinuationFromZero = method-value-receipt
  "1 + 3 + 9 + 27 + ..."
  rationalFunctionContinuation
  "-1/2"
  false
  false
  "existing Geo owner encodes 1/(1-x) evaluated at x=3 outside the real disk of convergence"

threeAdicFromZero : MethodValueReceipt
threeAdicFromZero = method-value-receipt
  "1 + 3 + 9 + 27 + ..."
  threeAdicLimit
  "-1/2"
  true
  false
  "source-established p-adic geometric-series theorem: |3|_3 < 1, hence the series converges in Q_3 to 1/(1-3)"

threeAdicFromOne : MethodValueReceipt
threeAdicFromOne = method-value-receipt
  "3 + 9 + 27 + 81 + ..."
  threeAdicLimit
  "-3/2"
  true
  false
  "index-shifted p-adic geometric sum 3/(1-3)"

------------------------------------------------------------------------
-- Existing finite/OEIS carrier is reused exactly.
------------------------------------------------------------------------

partial0 : Geo.partialSum3 0 ≡ 0
partial0 = refl

partial1 : Geo.partialSum3 1 ≡ 1
partial1 = refl

partial3 : Geo.partialSum3 3 ≡ 13
partial3 = refl

partial6 : Geo.partialSum3 6 ≡ 364
partial6 = refl

partial9 : Geo.partialSum3 9 ≡ 9841
partial9 = refl

balancedTernaryNineTritBound : CodecSnowball.balancedTernaryMaxMagnitude 9 ≡ 9841
balancedTernaryNineTritBound = CodecSnowball.nineTritMax

------------------------------------------------------------------------
-- Ramanujan lane taxonomy: same surname/source tradition != same theorem.
------------------------------------------------------------------------

data RamanujanLane : Set where
  tauHeckeMoonshine : RamanujanLane
  rogersRamanujanPrimeFive : RamanujanLane
  hardyRamanujanPartitions : RamanujanLane
  divergentSeriesSummation : RamanujanLane

record RamanujanLaneReceipt : Set where
  constructor ramanujan-lane-receipt
  field
    lane : RamanujanLane
    repoOwner : String
    objectClass : String
    identifiesThreeAdicGeometricSum : Bool
open RamanujanLaneReceipt public

tauLane : RamanujanLaneReceipt
tauLane = ramanujan-lane-receipt
  tauHeckeMoonshine
  "DASHI/Moonshine/RamanujanTauHecke23Exact.agda"
  "Ramanujan tau / Hecke / modular-form arithmetic"
  false

rogersLane : RamanujanLaneReceipt
rogersLane = ramanujan-lane-receipt
  rogersRamanujanPrimeFive
  "DASHI/Physics/Closure/RogersRamanujanP5Receipt.agda"
  "Rogers--Ramanujan q-series / prime-5 diagnostic"
  false

partitionLane : RamanujanLaneReceipt
partitionLane = ramanujan-lane-receipt
  hardyRamanujanPartitions
  "DASHI/Mathematics/NumberTheory/PartitionHardyRamanujanErdosBridgeExact.agda"
  "partition asymptotics / generating-function analysis"
  false

------------------------------------------------------------------------
-- External coordinates and primary/reference source roles.
------------------------------------------------------------------------

record PadicRamanujanExternalCoordinates : Set where
  constructor padic-ramanujan-external-coordinates
  field
    powersOfThreeOEIS : String
    ternaryRepunitOEIS : String
    ternaryRenderingOEIS : String
    pAdicNumberQid : String
    geometricSeriesQid : String
    divergentSeriesQid : String
    ramanujanSummationQid : String
    serreArithmeticDOI : String
    robertPadicDOI : String
    hardyDivergentSeriesReference : String
    oeisCreatesSummationMethod : Bool
    qidCreatesPadicConvergenceProof : Bool
open PadicRamanujanExternalCoordinates public

canonicalPadicRamanujanExternalCoordinates : PadicRamanujanExternalCoordinates
canonicalPadicRamanujanExternalCoordinates = padic-ramanujan-external-coordinates
  "A000244"
  "A003462"
  "A007089"
  "Q311627"
  "Q1306887"
  "Q906520"
  "Ramanujan-summation QID unresolved in this owner"
  "10.1007/978-1-4684-9884-4"
  "10.1007/978-1-4757-3254-2"
  "G. H. Hardy, Divergent Series (1949)"
  false
  false

------------------------------------------------------------------------
-- BIDI / WrongType boundaries.
------------------------------------------------------------------------

data SameAssignedValueIdentifiesSummationMethod : Set where
data RationalContinuationCreatesPadicConvergence : Set where
data PadicConvergenceCreatesRealConvergence : Set where
data RamanujanNameCreatesRamanujanSummation : Set where
data A003462CreatesInfiniteSumValue : Set where

differentMethodsMayShareValue : SameAssignedValueIdentifiesSummationMethod → ⊥
differentMethodsMayShareValue ()

continuationDoesNotCreatePadicProof : RationalContinuationCreatesPadicConvergence → ⊥
continuationDoesNotCreatePadicProof ()

padicDoesNotCreateRealConvergence : PadicConvergenceCreatesRealConvergence → ⊥
padicDoesNotCreateRealConvergence ()

ramanujanSurnameDoesNotCreateSummationMethod : RamanujanNameCreatesRamanujanSummation → ⊥
ramanujanSurnameDoesNotCreateSummationMethod ()

oeisFiniteFamilyDoesNotCreateInfiniteValue : A003462CreatesInfiniteSumValue → ⊥
oeisFiniteFamilyDoesNotCreateInfiniteSumValue ()

record TernaryPadicRamanujanFrontier : Set where
  constructor ternary-padic-ramanujan-frontier
  field
    finiteA003462CarrierPaid : Bool
    rationalContinuationMinusHalfPaid : Bool
    threeAdicMinusHalfSourceEstablished : Bool
    threeAdicMinusHalfKernelDerivedHere : Bool
    shiftedThreeAdicMinusThreeHalvesSourceEstablished : Bool
    realConvergenceAtRatioThree : Bool
    ramanujanTauLaneSeparated : Bool
    rogersRamanujanLaneSeparated : Bool
    hardyRamanujanLaneSeparated : Bool
    ramanujanSummationOfThisExactSeriesPaid : Bool
    nextResidual : String
open TernaryPadicRamanujanFrontier public

currentTernaryPadicRamanujanFrontier : TernaryPadicRamanujanFrontier
currentTernaryPadicRamanujanFrontier = ternary-padic-ramanujan-frontier
  true true true false true false true true true false
  "next, bind an actual Q_3 carrier (or an existing p-adic API) and prove the partial sums S_n=(3^n-1)/2 converge to -1/2 in the 3-adic metric. Keep that theorem distinct from rational continuation and from any Ramanujan/Abel/Cesaro summation interface. Then cross-pollinate A003462 with the finite balanced-ternary reconstruction theorem and the 3-adic address/cylinder topology."
