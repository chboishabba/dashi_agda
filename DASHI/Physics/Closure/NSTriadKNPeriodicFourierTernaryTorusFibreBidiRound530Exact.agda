module DASHI.Physics.Closure.NSTriadKNPeriodicFourierTernaryTorusFibreBidiRound530Exact where

------------------------------------------------------------------------
-- ROUND530 / PERIODIC T^3 FOURIER FIBRE -> EXACT C3^3 SIGN-QUOTIENT TORUS
--
-- R526 kept a necessary notation firewall between the physical continuous
-- torus and the finite Base369 27-point cube.  The broader repository already
-- contains a stronger intermediate fact that R526 did not consume:
--
--   * periodic Navier--Stokes uses the exact integer Fourier carrier Z^3;
--   * R529 maps Z^3 onto {-1,0,+1}^3 by coordinate sign;
--   * Base369PeriodicTernaryTorusPathRestrictionBidiExact equips that SAME
--     27-point carrier with periodic C3^3 wraparound adjacency;
--   * three such voxels are the SAME nine-trit hyperfabric carrier C3^9.
--
-- This module makes that factorisation exact.  It proves that every ternary-27
-- point has an integer Fourier representative, so the finite periodic torus is
-- an exact sign-quotient/retract of the Z^3 Fourier fibre.  It then lifts a
-- physical triad to the existing nine-trit hyperfabric carrier.
--
-- This does NOT identify the continuum manifold point-set with 27 points.  The
-- exact equality/reuse is at the quotient/fibre carrier and periodic adjacency
-- level.  The R^3/T^3 measure bridge and literal R406 transport remain open.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)
open import Data.Integer.Base using (ℤ; +_; -[1+_])

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as G
import DASHI.Moonshine.Base369PeriodicTernaryTorusPathRestrictionBidiExact as Periodic
import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNTorusEuclideanTernary27IntersectionRound526Exact as R526
import DASHI.Physics.Closure.NSTriadKNTorusEuclideanR406MeasureBridgeBoundaryRound528Exact as R528
import DASHI.Physics.Closure.NSTriadKNPeriodicIntegerTernary27SignChartRound529Exact as R529

------------------------------------------------------------------------
-- 1. Every balanced trit has an exact integer Fourier representative.
------------------------------------------------------------------------

tritIntegerRepresentative530 : SSP.SSPTrit → ℤ
tritIntegerRepresentative530 SSP.sspNegOne = -[1+ zero ]
tritIntegerRepresentative530 SSP.sspZero = + zero
tritIntegerRepresentative530 SSP.sspPosOne = + 1

tritRepresentativeSection530 :
  (t : SSP.SSPTrit) →
  R529.integerSign529 (tritIntegerRepresentative530 t) ≡ t
tritRepresentativeSection530 SSP.sspNegOne = refl
tritRepresentativeSection530 SSP.sspZero = refl
tritRepresentativeSection530 SSP.sspPosOne = refl

------------------------------------------------------------------------
-- 2. Exact section of the Z^3 -> ternary-27 sign observation.
------------------------------------------------------------------------

periodicModeRepresentative530 : G.Ternary27Point → Z3.FourierMode
periodicModeRepresentative530 (G.ternary27Point x y z) =
  Z3.mode
    (tritIntegerRepresentative530 x)
    (tritIntegerRepresentative530 y)
    (tritIntegerRepresentative530 z)

periodicSignObservationSection530 :
  (p : G.Ternary27Point) →
  R529.observePeriodicMode529 (periodicModeRepresentative530 p) ≡ p
periodicSignObservationSection530 (G.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne) = refl
periodicSignObservationSection530 (G.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspZero) = refl
periodicSignObservationSection530 (G.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne) = refl
periodicSignObservationSection530 (G.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspNegOne) = refl
periodicSignObservationSection530 (G.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspZero) = refl
periodicSignObservationSection530 (G.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspPosOne) = refl
periodicSignObservationSection530 (G.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne) = refl
periodicSignObservationSection530 (G.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspZero) = refl
periodicSignObservationSection530 (G.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne) = refl
periodicSignObservationSection530 (G.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspNegOne) = refl
periodicSignObservationSection530 (G.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspZero) = refl
periodicSignObservationSection530 (G.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspPosOne) = refl
periodicSignObservationSection530 (G.ternary27Point SSP.sspZero SSP.sspZero SSP.sspNegOne) = refl
periodicSignObservationSection530 (G.ternary27Point SSP.sspZero SSP.sspZero SSP.sspZero) = refl
periodicSignObservationSection530 (G.ternary27Point SSP.sspZero SSP.sspZero SSP.sspPosOne) = refl
periodicSignObservationSection530 (G.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspNegOne) = refl
periodicSignObservationSection530 (G.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspZero) = refl
periodicSignObservationSection530 (G.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspPosOne) = refl
periodicSignObservationSection530 (G.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne) = refl
periodicSignObservationSection530 (G.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspZero) = refl
periodicSignObservationSection530 (G.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne) = refl
periodicSignObservationSection530 (G.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspNegOne) = refl
periodicSignObservationSection530 (G.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero) = refl
periodicSignObservationSection530 (G.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspPosOne) = refl
periodicSignObservationSection530 (G.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne) = refl
periodicSignObservationSection530 (G.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspZero) = refl
periodicSignObservationSection530 (G.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne) = refl

------------------------------------------------------------------------
-- 3. Quotient relation: two Fourier modes are observationally the same exactly
-- when they land on the same ternary sign point.
------------------------------------------------------------------------

SamePeriodicSignFibre530 : Z3.FourierMode → Z3.FourierMode → Set
SamePeriodicSignFibre530 k l =
  R529.observePeriodicMode529 k ≡ R529.observePeriodicMode529 l

representativeRecoversObservedFibre530 :
  (k : Z3.FourierMode) →
  SamePeriodicSignFibre530
    (periodicModeRepresentative530 (R529.observePeriodicMode529 k))
    k
representativeRecoversObservedFibre530 (Z3.mode (+ zero) (+ zero) (+ zero)) = refl
representativeRecoversObservedFibre530 (Z3.mode x y z) =
  periodicSignObservationSection530 (R529.observePeriodicMode529 (Z3.mode x y z))

------------------------------------------------------------------------
-- 4. The finite sign quotient already carries exact periodic C3^3 adjacency.
------------------------------------------------------------------------

PeriodicTernaryTorusVoxel530 : Set
PeriodicTernaryTorusVoxel530 = G.Ternary27Point

PeriodicTernaryTorusAdjacent530 :
  PeriodicTernaryTorusVoxel530 → PeriodicTernaryTorusVoxel530 → Set
PeriodicTernaryTorusAdjacent530 = Periodic.TorusVoxelAdjacent

periodicWraparound530 :
  PeriodicTernaryTorusAdjacent530
    (G.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero)
    (G.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspZero)
periodicWraparound530 = Periodic.torusAdjacentX Periodic.posToNegWrap

------------------------------------------------------------------------
-- 5. A physical Fourier triad lands on the SAME nine-trit hyperfabric carrier
-- that the periodic C3^9 owner equips with torus adjacency.
------------------------------------------------------------------------

observePeriodicTriadHyperformal530 :
  R526.Triad526 Z3.FourierMode → G.TernaryHyperformalPoint
observePeriodicTriadHyperformal530 triad =
  R526.triadSignatureToThreeCubeShape526
    (R526.observeTriad526 R529.periodicFrequencySignChart529 triad)

PeriodicTriadHyperformalAdjacent530 :
  G.TernaryHyperformalPoint → G.TernaryHyperformalPoint → Set
PeriodicTriadHyperformalAdjacent530 = Periodic.TorusHyperformalAdjacent

sameNineTritCarrier530 : Bool
sameNineTritCarrier530 =
  Periodic.PeriodicPathRestrictionBoundary.sameNineTritCarrier
    Periodic.canonicalPeriodicPathRestrictionBoundary

sameNineTritCarrier530IsTrue : sameNineTritCarrier530 ≡ true
sameNineTritCarrier530IsTrue = refl

------------------------------------------------------------------------
-- 6. Introspective correction of the R526 wording.
--
-- There are three distinct statements:
--   (a) continuum physical torus point-set = finite 27-point set        [not claimed]
--   (b) periodic Z^3 Fourier sign quotient has carrier Ternary27Point  [proved]
--   (c) that same carrier supports exact periodic C3^3 torus adjacency [proved]
--
-- Thus the useful "physical T3 = Base369 ternary T3" reading is exact only at
-- the Fourier-sign-quotient/fibre presentation, not as raw manifold cardinality.
------------------------------------------------------------------------

record PeriodicTorusTernaryFibreReceipt530 : Set₁ where
  constructor periodic-torus-ternary-fibre-receipt-530
  field
    physicalPeriodicFourierCarrier : Set
    finitePeriodicTorusCarrier : Set
    observePhysicalFibre : physicalPeriodicFourierCarrier → finitePeriodicTorusCarrier
    chooseIntegerRepresentative : finitePeriodicTorusCarrier → physicalPeriodicFourierCarrier
    observationSection :
      (p : finitePeriodicTorusCarrier) →
      observePhysicalFibre (chooseIntegerRepresentative p) ≡ p
    finiteCarrierHasPeriodicAdjacency :
      finitePeriodicTorusCarrier → finitePeriodicTorusCarrier → Set
    triadLandsOnNineTritHyperformalCarrier : Bool
    continuumPointSetEqualityClaimed : Bool
    measureTransportClaimed : Bool

periodicTorusTernaryFibreReceipt530 : PeriodicTorusTernaryFibreReceipt530
periodicTorusTernaryFibreReceipt530 =
  periodic-torus-ternary-fibre-receipt-530
    Z3.FourierMode
    G.Ternary27Point
    R529.observePeriodicMode529
    periodicModeRepresentative530
    periodicSignObservationSection530
    Periodic.TorusVoxelAdjacent
    true
    false
    false

------------------------------------------------------------------------
-- 7. BIDI frontier.
------------------------------------------------------------------------

data Round530Residual : Set where
  missingEuclideanContinuumSignFibre530 : Round530Residual
  missingLatticeContinuumMeasureTransport530 : Round530Residual
  missingLiteralR406SameObjectTransport530 : Round530Residual

firstRound530Residual : Round530Residual
firstRound530Residual = missingEuclideanContinuumSignFibre530

round530PeriodicZ3SignQuotientOnto27Closed : Bool
round530PeriodicZ3SignQuotientOnto27Closed = true
round530PeriodicC3CubedTorusAdjacencyClosed : Bool
round530PeriodicC3CubedTorusAdjacencyClosed = true
round530TriadC3NinthHyperformalCarrierClosed : Bool
round530TriadC3NinthHyperformalCarrierClosed = true
round530ContinuumMeasureBridgeClosed : Bool
round530ContinuumMeasureBridgeClosed = false
round530ClayPromotion : Bool
round530ClayPromotion = false

round530PeriodicZ3SignQuotientOnto27ClosedIsTrue :
  round530PeriodicZ3SignQuotientOnto27Closed ≡ true
round530PeriodicZ3SignQuotientOnto27ClosedIsTrue = refl
round530PeriodicC3CubedTorusAdjacencyClosedIsTrue :
  round530PeriodicC3CubedTorusAdjacencyClosed ≡ true
round530PeriodicC3CubedTorusAdjacencyClosedIsTrue = refl
round530TriadC3NinthHyperformalCarrierClosedIsTrue :
  round530TriadC3NinthHyperformalCarrierClosed ≡ true
round530TriadC3NinthHyperformalCarrierClosedIsTrue = refl
round530ContinuumMeasureBridgeClosedIsFalse :
  round530ContinuumMeasureBridgeClosed ≡ false
round530ContinuumMeasureBridgeClosedIsFalse = refl
round530ClayPromotionIsFalse : round530ClayPromotion ≡ false
round530ClayPromotionIsFalse = refl
