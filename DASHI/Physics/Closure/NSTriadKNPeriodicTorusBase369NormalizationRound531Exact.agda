module DASHI.Physics.Closure.NSTriadKNPeriodicTorusBase369NormalizationRound531Exact where

------------------------------------------------------------------------
-- ROUND531 / NORMALIZE THE PHYSICAL T^3 <-> BASE369 TERNARY-TORUS STATEMENT
--
-- R530 already proves the strong fibre statement that the earlier R526 wording
-- did not exploit:
--
--   physical periodic Fourier carrier Z^3
--       -> coordinate-sign quotient
--       -> SAME Base369 Ternary27Point carrier
--       -> SAME periodic C3^3 wraparound adjacency.
--
-- Therefore the useful equality is not raw manifold-point equality.  It is the
-- exact finite Fourier-sign fibre presentation:
--
--   Z^3 / same-sign-fibre  ~=  C3^3 = {-1,0,+1}^3,
--
-- with an explicit section already supplied by R530.  Three physical Fourier
-- modes land on the existing C3^9 nine-trit hyperfabric carrier.
--
-- This module makes that normalization the canonical NS-side statement and
-- rewrites the R528 scheduler accordingly: the periodic chart coordinate is
-- already paid; the next representation coordinate is the Euclidean continuum
-- sign fibre, followed by measure/cutoff/same-object R406 transport.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as G
import DASHI.Moonshine.Base369PeriodicTernaryTorusPathRestrictionBidiExact as Periodic
import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPeriodicIntegerTernary27SignChartRound529Exact as R529
import DASHI.Physics.Closure.NSTriadKNPeriodicFourierTernaryTorusFibreBidiRound530Exact as R530
import DASHI.Physics.Closure.NSTriadKNTorusEuclideanR406MeasureBridgeBoundaryRound528Exact as R528

------------------------------------------------------------------------
-- 1. Canonical normalized carriers.
------------------------------------------------------------------------

PhysicalPeriodicFourierCarrier531 : Set
PhysicalPeriodicFourierCarrier531 = Z3.FourierMode

Base369PeriodicTorusCarrier531 : Set
Base369PeriodicTorusCarrier531 = G.Ternary27Point

observePhysicalPeriodicFibre531 :
  PhysicalPeriodicFourierCarrier531 -> Base369PeriodicTorusCarrier531
observePhysicalPeriodicFibre531 = R529.observePeriodicMode529

choosePhysicalRepresentative531 :
  Base369PeriodicTorusCarrier531 -> PhysicalPeriodicFourierCarrier531
choosePhysicalRepresentative531 = R530.periodicModeRepresentative530

physicalPeriodicObservationSection531 :
  (p : Base369PeriodicTorusCarrier531) ->
  observePhysicalPeriodicFibre531 (choosePhysicalRepresentative531 p) ≡ p
physicalPeriodicObservationSection531 = R530.periodicSignObservationSection530

SamePhysicalPeriodicFibre531 :
  PhysicalPeriodicFourierCarrier531 -> PhysicalPeriodicFourierCarrier531 -> Set
SamePhysicalPeriodicFibre531 = R530.SamePeriodicSignFibre530

------------------------------------------------------------------------
-- 2. The quotient target carries the existing periodic C3^3 adjacency.
------------------------------------------------------------------------

Base369PeriodicTorusAdjacent531 :
  Base369PeriodicTorusCarrier531 -> Base369PeriodicTorusCarrier531 -> Set
Base369PeriodicTorusAdjacent531 = Periodic.TorusVoxelAdjacent

periodicWraparoundLivesOnNormalizedCarrier531 :
  Base369PeriodicTorusAdjacent531
    (G.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero)
    (G.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspZero)
periodicWraparoundLivesOnNormalizedCarrier531 = R530.periodicWraparound530

------------------------------------------------------------------------
-- 3. Introspective correction of the old notation collision.
------------------------------------------------------------------------

data TorusEqualityReading531 : Set where
  rawManifoldPointEquality531 : TorusEqualityReading531
  fourierSignFibreEquality531 : TorusEqualityReading531

data TorusEqualityStatus531 : Set where
  established531 : TorusEqualityStatus531
  notClaimed531 : TorusEqualityStatus531

statusForTorusEqualityReading531 : TorusEqualityReading531 -> TorusEqualityStatus531
statusForTorusEqualityReading531 rawManifoldPointEquality531 = notClaimed531
statusForTorusEqualityReading531 fourierSignFibreEquality531 = established531

fourierFibreEqualityIsEstablished531 :
  statusForTorusEqualityReading531 fourierSignFibreEquality531 ≡ established531
fourierFibreEqualityIsEstablished531 = refl

rawManifoldEqualityIsNotClaimed531 :
  statusForTorusEqualityReading531 rawManifoldPointEquality531 ≡ notClaimed531
rawManifoldEqualityIsNotClaimed531 = refl

------------------------------------------------------------------------
-- 4. Feed the stronger R530 result back into the R528 scheduler.
------------------------------------------------------------------------

-- R528 started before R529/R530 and therefore listed the periodic chart first.
-- That coordinate is now closed.  The next representation seam is Euclidean.
afterPeriodicFibreNormalization531 : R528.DomainBridgeState528
afterPeriodicFibreNormalization531 =
  R528.domain-bridge-state-528
    R528.missingEuclideanSignChart528
    R528.instantiateEuclideanFrequencyChart528
    refl

------------------------------------------------------------------------
-- 5. Status ledger.
------------------------------------------------------------------------

round531PeriodicFourierSignQuotientIsBase369Carrier : Bool
round531PeriodicFourierSignQuotientIsBase369Carrier = true

round531PeriodicAdjacencyReusedExactly : Bool
round531PeriodicAdjacencyReusedExactly = true

round531RawManifoldPointEqualityClaimed : Bool
round531RawManifoldPointEqualityClaimed = false

round531PeriodicChartResidualStillOpen : Bool
round531PeriodicChartResidualStillOpen = false

round531EuclideanContinuumSignFibreStillOpen : Bool
round531EuclideanContinuumSignFibreStillOpen = true

round531MeasureTransportClosed : Bool
round531MeasureTransportClosed = false

round531ClayPromotion : Bool
round531ClayPromotion = false

round531PeriodicFourierSignQuotientIsBase369CarrierIsTrue :
  round531PeriodicFourierSignQuotientIsBase369Carrier ≡ true
round531PeriodicFourierSignQuotientIsBase369CarrierIsTrue = refl

round531RawManifoldPointEqualityClaimedIsFalse :
  round531RawManifoldPointEqualityClaimed ≡ false
round531RawManifoldPointEqualityClaimedIsFalse = refl

round531ClayPromotionIsFalse : round531ClayPromotion ≡ false
round531ClayPromotionIsFalse = refl
