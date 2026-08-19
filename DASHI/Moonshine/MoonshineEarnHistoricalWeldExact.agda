module DASHI.Moonshine.MoonshineEarnHistoricalWeldExact where

------------------------------------------------------------------------
-- HISTORICAL SOURCE / MODERN AUTHORITY WELD
--
-- Repository PR #1 (2026-03), file MoonshineEarn.agda, introduced the exact
-- finite arithmetic chain
--
--   7 * 11 * 23
--      -- 47/23, 59/7, 71/11 -->
--   47 * 59 * 71 = 196883
--
-- and then checked 196883 + 1 = 196884.
--
-- The arithmetic is genuine; the historical comments promoted it too far by
-- calling the chain itself a proof/explanation of Monstrous Moonshine.
--
-- MODERN PRIMARY SOURCES / CONTEXT
--
-- John H. Conway and Simon P. Norton,
-- "Monstrous Moonshine", Bull. London Math. Soc. 11 (1979), 308--339.
-- DOI: 10.1112/blms/11.3.308.
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem", J. Number Theory 161 (2016), 230--239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- John H. Conway, Robert T. Curtis, Simon P. Norton, Richard A. Parker,
-- Robert A. Wilson,
-- "Atlas of Finite Groups", Oxford University Press, 1985.
-- No DOI asserted here.
--
-- DASHI CONTRIBUTION
--
-- Recover the old finite chain under the modern theorem boundaries.
-- We prove independently that every source/target prime in the chain
--
--   {7,11,23} -> {47,59,71}
--
-- (1) divides the actual published Monster order, and
-- (2) lies on the repository's independently computed Fricke-genus-zero
--     control locus.
--
-- Separately, the endpoint 196883 + 1 = 196884 is welded to the modern
-- JCoefficientCharacterBridge.  No implication from the FRACTRAN chain to
-- VOA construction, McKay--Thompson series, Hauptmodul status, Conway--Norton,
-- or the Monster representation is inferred.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat.Divisibility using (_∣_; divides)

import MoonshineEarn as Earn
import DASHI.Moonshine.JCoefficientCharacterBridge as J
import DASHI.Moonshine.MonsterOrderDivisibilityExact as Monster
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.PrimeFrickeGenusControlExact as Fricke

------------------------------------------------------------------------
-- Historical arithmetic is retained exactly, not re-derived under new names.
------------------------------------------------------------------------

historicalPerfProduct : 7 * 11 * 23 ≡ 1771
historicalPerfProduct = Earn.perf-product

historicalEarnChain :
  (((7 * 11 * 23) / 23 * 47) / 7 * 59) / 11 * 71 ≡ 196883
historicalEarnChain = Earn.chain

historicalTargetProduct : 47 * 59 * 71 ≡ 196883
historicalTargetProduct = Earn.moonshine-product

historicalEndpointPlusOne : 47 * 59 * 71 + 1 ≡ 196884
historicalEndpointPlusOne = Earn.observer

modernFirstCoefficientArithmetic : 196884 ≡ 1 + 196883
modernFirstCoefficientArithmetic = J.firstCoefficientArithmetic

------------------------------------------------------------------------
-- Exact divisibility by the ACTUAL Monster order, with no MonsterPrimeLane
-- enumeration imported.
------------------------------------------------------------------------

sevenDividesMonsterOrder : Monster.PrimeDividesMonsterOrder 7
sevenDividesMonsterOrder =
  divides 115431060684930410840922843565958679572250624000000000 refl

elevenDividesMonsterOrder : Monster.PrimeDividesMonsterOrder 11
elevenDividesMonsterOrder =
  divides 73456129526773897807859991360155523364159488000000000 refl

twentyThreeDividesMonsterOrder : Monster.PrimeDividesMonsterOrder 23
twentyThreeDividesMonsterOrder =
  divides 35131192382370125038541734998335250304598016000000000 refl

fortySevenDividesMonsterOrder : Monster.PrimeDividesMonsterOrder 47
fortySevenDividesMonsterOrder =
  divides 17191860102010912252903402233227888446930944000000000 refl

fiftyNineDividesMonsterOrder : Monster.PrimeDividesMonsterOrder 59
fiftyNineDividesMonsterOrder =
  divides 13695210589737506370956947541723911135690752000000000 refl

seventyOneDividesMonsterOrder : Monster.PrimeDividesMonsterOrder 71
seventyOneDividesMonsterOrder =
  divides 11380527109781871491358590210728320521207808000000000 refl

------------------------------------------------------------------------
-- Independent finite Fricke-control cross-check.  These six rows are all
-- genus zero.  This does not replace the later table-free published selector;
-- it verifies that the historical chain happens entirely inside the same
-- Ogg/Fricke locus on the finite control deck.
------------------------------------------------------------------------

source7FrickeGenusZero :
  Fricke.genusX0Plus (Fricke.frickeRow Matrix.prime7) ≡ 0
source7FrickeGenusZero = refl

source11FrickeGenusZero :
  Fricke.genusX0Plus (Fricke.frickeRow Matrix.prime11) ≡ 0
source11FrickeGenusZero = refl

source23FrickeGenusZero :
  Fricke.genusX0Plus (Fricke.frickeRow Matrix.prime23) ≡ 0
source23FrickeGenusZero = refl

target47FrickeGenusZero :
  Fricke.genusX0Plus (Fricke.frickeRow Matrix.prime47) ≡ 0
target47FrickeGenusZero = refl

target59FrickeGenusZero :
  Fricke.genusX0Plus (Fricke.frickeRow Matrix.prime59) ≡ 0
target59FrickeGenusZero = refl

target71FrickeGenusZero :
  Fricke.genusX0Plus (Fricke.frickeRow Matrix.prime71) ≡ 0
target71FrickeGenusZero = refl

------------------------------------------------------------------------
-- Proof-relevant role separation for the six historical primes.
------------------------------------------------------------------------

data EarnPrimeRole : Set where
  source7 source11 source23 target47 target59 target71 : EarnPrimeRole

earnPrime : EarnPrimeRole → Nat
earnPrime source7 = 7
earnPrime source11 = 11
earnPrime source23 = 23
earnPrime target47 = 47
earnPrime target59 = 59
earnPrime target71 = 71

earnPrimeDividesMonsterOrder :
  (role : EarnPrimeRole) →
  Monster.PrimeDividesMonsterOrder (earnPrime role)
earnPrimeDividesMonsterOrder source7 = sevenDividesMonsterOrder
earnPrimeDividesMonsterOrder source11 = elevenDividesMonsterOrder
earnPrimeDividesMonsterOrder source23 = twentyThreeDividesMonsterOrder
earnPrimeDividesMonsterOrder target47 = fortySevenDividesMonsterOrder
earnPrimeDividesMonsterOrder target59 = fiftyNineDividesMonsterOrder
earnPrimeDividesMonsterOrder target71 = seventyOneDividesMonsterOrder

------------------------------------------------------------------------
-- The exact modern reading of the historical coincidence.
------------------------------------------------------------------------

record MoonshineEarnModernBoundary : Set where
  field
    pr1FractranArithmeticRecovered : Bool
    endpointProductIs196883 : Bool
    endpointPlusOneIs196884 : Bool
    modernFirstCoefficientArithmeticReused : Bool
    allSixPrimesDivideActualMonsterOrder : Bool
    allSixPrimesOnFiniteFrickeGenusZeroControl : Bool

    fractranChainProvesMonsterRepresentation : Bool
    fractranChainProvesJModularity : Bool
    fractranChainProvesConwayNorton : Bool
    plusOneIdentifiedAsExternalObserver : Bool
    plusOneCanInsteadBeTypedByModernVOAGradeSemantics : Bool

canonicalMoonshineEarnModernBoundary : MoonshineEarnModernBoundary
canonicalMoonshineEarnModernBoundary = record
  { pr1FractranArithmeticRecovered = true
  ; endpointProductIs196883 = true
  ; endpointPlusOneIs196884 = true
  ; modernFirstCoefficientArithmeticReused = true
  ; allSixPrimesDivideActualMonsterOrder = true
  ; allSixPrimesOnFiniteFrickeGenusZeroControl = true
  ; fractranChainProvesMonsterRepresentation = false
  ; fractranChainProvesJModularity = false
  ; fractranChainProvesConwayNorton = false
  ; plusOneIdentifiedAsExternalObserver = false
  ; plusOneCanInsteadBeTypedByModernVOAGradeSemantics = true
  }
