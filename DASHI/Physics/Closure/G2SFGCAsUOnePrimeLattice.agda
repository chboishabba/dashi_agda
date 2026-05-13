module DASHI.Physics.Closure.G2SFGCAsUOnePrimeLattice where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Geometry.PrimeLattice as PL
import DASHI.Physics.Closure.G2DiscreteCurvatureCarrier as G2DCC
import DASHI.Physics.Closure.G2PrimeLatticeCoefficientBridge as G2PLCB
import DASHI.Physics.Closure.G2SFGCPrimeLatticeOrbit as G2ORBIT
import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
import DASHI.Physics.ShiftFiniteGaugeCoupling as SFGC
import DASHI.Physics.ShiftPhaseTableInterference as SPTI4

------------------------------------------------------------------------
-- Option B diagnostic.
--
-- This avoids the rejected ShiftPressurePoint -> FactorVec embedding.  The
-- only shared surface is coefficient-level: Phase4 has the same d2=0 law
-- required by the standalone prime lattice, and SFGC has a definitional
-- vacuum-zero link field.  The current repo still does not expose an actual
-- U(1) connection/field-strength interface for SFGC.

data G2SFGCAsUOnePrimeLatticeStatus : Set where
  phase4VacuumAndD2AvailableButNoUOneCurvatureCarrier :
    G2SFGCAsUOnePrimeLatticeStatus

data G2SFGCAsUOnePrimeLatticeMissing : Set where
  missingActualUOneConnectionCarrier :
    G2SFGCAsUOnePrimeLatticeMissing

  missingUOneConnectionToDiscrete1Form :
    G2SFGCAsUOnePrimeLatticeMissing

  missingNondegenerateSFGCPlaquetteGeometry :
    G2SFGCAsUOnePrimeLatticeMissing

  missingUOneFieldStrengthFromCurvature :
    G2SFGCAsUOnePrimeLatticeMissing

phase4VacuumGaugeFieldZero :
  (s : SPTI.ShiftPressurePoint) →
  SFGC.vacuumGaugeField s ≡ SPTI4.φ0
phase4VacuumGaugeFieldZero s =
  refl

phase4PointLinkVacuumZero :
  (s : SPTI.ShiftPressurePoint) →
  G2DCC.connectionToPointLink1Form SFGC.vacuumGaugeField s
    ≡
  SPTI4.φ0
phase4PointLinkVacuumZero =
  G2DCC.vacuumPointLink1FormZero

phase4RightEdgeVacuumZero :
  (edge : G2DCC.SFGCShiftRightEdge) →
  G2DCC.connectionToShiftRightEdge1Form SFGC.vacuumGaugeField edge
    ≡
  SPTI4.φ0
phase4RightEdgeVacuumZero =
  G2DCC.vacuumShiftRightEdge1FormZero

phase4PrimeLatticeD2Zero :
  (f : PL.0Form SPTI4.Phase4) →
  (cell : PL.PrimeLattice2Cell) →
  PL.δ₁ G2PLCB.phase4PrimeLatticeCoefficientLaw
    (PL.δ₀ G2PLCB.phase4PrimeLatticeCoefficientLaw f)
    cell
    ≡
  SPTI4.φ0
phase4PrimeLatticeD2Zero =
  G2PLCB.phase4PrimeLatticeD2Zero

record G2SFGCAsUOnePrimeLatticeDiagnostic : Set₁ where
  field
    status :
      G2SFGCAsUOnePrimeLatticeStatus

    inspectedConnectionCarrier :
      Set

    inspectedConnectionCarrierIsSFGC :
      inspectedConnectionCarrier ≡ SFGC.GaugeField

    inspectedVacuumConnection :
      SFGC.GaugeField

    vacuumConnectionIsPhase4Zero :
      (s : SPTI.ShiftPressurePoint) →
      inspectedVacuumConnection s ≡ SPTI4.φ0

    coefficientCarrier :
      Set

    coefficientCarrierIsPhase4 :
      coefficientCarrier ≡ SPTI4.Phase4

    sharedPrimeLatticeCoefficientLaw :
      PL.PrimeLatticeCoefficientLaw SPTI4.Phase4

    sharedD2Zero :
      (f : PL.0Form SPTI4.Phase4) →
      (cell : PL.PrimeLattice2Cell) →
      PL.δ₁ sharedPrimeLatticeCoefficientLaw
        (PL.δ₀ sharedPrimeLatticeCoefficientLaw f)
        cell
        ≡
      SPTI4.φ0

    pointLinkBridge :
      G2DCC.SFGCPointLink1FormBridge

    pointLinkVacuumZero :
      (s : SPTI.ShiftPressurePoint) →
      G2DCC.SFGCPointLink1FormBridge.evaluate1 pointLinkBridge
        (G2DCC.SFGCPointLink1FormBridge.connectionTo1Form
          pointLinkBridge
          SFGC.vacuumGaugeField)
        s
        ≡
      SPTI4.φ0

    rightEdgeBridge :
      G2DCC.SFGCShiftRightEdgePrimeLattice1FormBridge

    rightEdgeVacuumZero :
      (edge : G2DCC.SFGCShiftRightEdge) →
      G2DCC.SFGCShiftRightEdgePrimeLattice1FormBridge.evaluatePrimeLattice1
        rightEdgeBridge
        (G2DCC.SFGCShiftRightEdgePrimeLattice1FormBridge.connectionToPrimeLattice1Form
          rightEdgeBridge
          SFGC.vacuumGaugeField)
        edge
        ≡
      SPTI4.φ0

    availableTwoStepReturnSurface :
      G2DCC.SFGCShiftRightEdgeTwoStepPlaquetteSurface

    priorNoFactorVecOrbitDiagnostic :
      G2ORBIT.G2SFGCPrimeLatticeOrbitDiagnostic

    firstMissingForOptionB :
      G2SFGCAsUOnePrimeLatticeMissing

    remainingMissingForOptionB :
      List G2SFGCAsUOnePrimeLatticeMissing

    exactMissingInterface :
      String

    nonPromotionBoundary :
      List String

canonicalG2SFGCAsUOnePrimeLatticeDiagnostic :
  G2SFGCAsUOnePrimeLatticeDiagnostic
canonicalG2SFGCAsUOnePrimeLatticeDiagnostic =
  record
    { status =
        phase4VacuumAndD2AvailableButNoUOneCurvatureCarrier
    ; inspectedConnectionCarrier =
        SFGC.GaugeField
    ; inspectedConnectionCarrierIsSFGC =
        refl
    ; inspectedVacuumConnection =
        SFGC.vacuumGaugeField
    ; vacuumConnectionIsPhase4Zero =
        phase4VacuumGaugeFieldZero
    ; coefficientCarrier =
        SPTI4.Phase4
    ; coefficientCarrierIsPhase4 =
        refl
    ; sharedPrimeLatticeCoefficientLaw =
        G2PLCB.phase4PrimeLatticeCoefficientLaw
    ; sharedD2Zero =
        phase4PrimeLatticeD2Zero
    ; pointLinkBridge =
        G2DCC.canonicalSFGCPointLink1FormBridge
    ; pointLinkVacuumZero =
        G2DCC.SFGCPointLink1FormBridge.vacuumZeroLaw
          G2DCC.canonicalSFGCPointLink1FormBridge
    ; rightEdgeBridge =
        G2DCC.canonicalSFGCShiftRightEdgePrimeLattice1FormBridge
    ; rightEdgeVacuumZero =
        G2DCC.SFGCShiftRightEdgePrimeLattice1FormBridge.vacuumRightEdgeZero
          G2DCC.canonicalSFGCShiftRightEdgePrimeLattice1FormBridge
    ; availableTwoStepReturnSurface =
        G2DCC.canonicalSFGCShiftRightEdgeTwoStepPlaquetteSurface
    ; priorNoFactorVecOrbitDiagnostic =
        G2ORBIT.canonicalG2SFGCPrimeLatticeOrbitDiagnostic
    ; firstMissingForOptionB =
        missingActualUOneConnectionCarrier
    ; remainingMissingForOptionB =
        missingActualUOneConnectionCarrier
        ∷ missingUOneConnectionToDiscrete1Form
        ∷ missingNondegenerateSFGCPlaquetteGeometry
        ∷ missingUOneFieldStrengthFromCurvature
        ∷ []
    ; exactMissingInterface =
        "Actual U(1) connection carrier for SFGC, with connectionToDiscrete1Form, vacuum-zero law into the chosen coefficient zero, nondegenerate plaquette/δ1 geometry, and fieldStrengthFromCurvature; Phase4/φ0 alone is only a finite C4 coefficient surface"
    ; nonPromotionBoundary =
        "Option B does not embed ShiftPressurePoint into FactorVec and does not require PrimeLatticeEdge -> ShiftPressurePoint"
        ∷ "SFGC.vacuumGaugeField is definitionally constant φ0, and the point-link/right-edge vacuum-zero laws are available"
        ∷ "Phase4 supplies the prime-lattice coefficient d2=0 law through G2PrimeLatticeCoefficientBridge"
        ∷ "The available SFGC plaquette surfaces are degenerate right-edge return surfaces, not an actual U(1) curvature geometry"
        ∷ "No DiscreteCurvatureCarrier SFGC.GaugeField is claimed here because Option B still lacks the actual U(1) connection/field-strength interface"
        ∷ []
    }

g2SFGCAsUOnePrimeLatticeFirstMissing :
  G2SFGCAsUOnePrimeLatticeDiagnostic.firstMissingForOptionB
    canonicalG2SFGCAsUOnePrimeLatticeDiagnostic
    ≡
  missingActualUOneConnectionCarrier
g2SFGCAsUOnePrimeLatticeFirstMissing =
  refl
