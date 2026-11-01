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

------------------------------------------------------------------------
-- Minimal U(1)-style system supported by the current SFGC API.
--
-- This is deliberately weaker than DiscreteCurvatureCarrier.  It records the
-- actual connection carrier, Phase4 coefficient laws, right-edge 1-form, the
-- available vacuum-zero law, and the available d²/return-boundary laws.  It
-- does not manufacture a nondegenerate plaquette or field strength.

record DiscreteUOneConnectionSystem (ConnectionCarrier : Set) : Set₁ where
  field
    Coefficient :
      Set

    zeroCoefficient :
      Coefficient

    coefficientLaw :
      G2DCC.AbelianCoefficientLawSurface Coefficient

    Site :
      Set

    Edge :
      Set

    Plaquette :
      Set

    Discrete0Form :
      Set

    Discrete1Form :
      Set

    Discrete2Form :
      Set

    edgeSource :
      Edge →
      Site

    edgeTarget :
      Edge →
      Site

    connectionToDiscrete1Form :
      ConnectionCarrier →
      Discrete1Form

    evaluate1 :
      Discrete1Form →
      Edge →
      Coefficient

    evaluate2 :
      Discrete2Form →
      Plaquette →
      Coefficient

    δ₀ :
      Discrete0Form →
      Discrete1Form

    δ₁ :
      Discrete1Form →
      Discrete2Form

    vacuumConnection :
      ConnectionCarrier

    vacuumConnectionZero :
      (edge : Edge) →
      evaluate1 (connectionToDiscrete1Form vacuumConnection) edge
        ≡
      zeroCoefficient

    phase4PrimeLatticeCoefficientD2Zero :
      (f : PL.0Form SPTI4.Phase4) →
      (cell : PL.PrimeLattice2Cell) →
      PL.δ₁ G2PLCB.phase4PrimeLatticeCoefficientLaw
        (PL.δ₀ G2PLCB.phase4PrimeLatticeCoefficientLaw f)
        cell
        ≡
      SPTI4.φ0

    availableDegeneratePlaquetteZero :
      (a : Discrete1Form) →
      (plaquette : Plaquette) →
      evaluate2 (δ₁ a) plaquette
        ≡
      zeroCoefficient

    availableDegenerateD2Zero :
      (f : Discrete0Form) →
      (plaquette : Plaquette) →
      evaluate2 (δ₁ (δ₀ f)) plaquette
        ≡
      zeroCoefficient

    firstMissingForDiscreteCurvatureCarrier :
      G2SFGCAsUOnePrimeLatticeMissing

    remainingMissingForDiscreteCurvatureCarrier :
      List G2SFGCAsUOnePrimeLatticeMissing

    interfaceBoundary :
      List String

canonicalSFGCDiscreteUOneConnectionSystem :
  DiscreteUOneConnectionSystem SFGC.GaugeField
canonicalSFGCDiscreteUOneConnectionSystem =
  record
    { Coefficient =
        SPTI4.Phase4
    ; zeroCoefficient =
        SPTI4.φ0
    ; coefficientLaw =
        G2DCC.phase4AbelianCoefficientLawSurface
    ; Site =
        SPTI.ShiftPressurePoint
    ; Edge =
        G2DCC.SFGCShiftRightEdge
    ; Plaquette =
        G2DCC.SFGCShiftRightEdgeTwoStepReturnPlaquette
    ; Discrete0Form =
        G2DCC.SFGCShiftRightEdge0Form
    ; Discrete1Form =
        G2DCC.SFGCShiftRightEdge1Form
    ; Discrete2Form =
        G2DCC.SFGCShiftRightEdgeTwoStep2Form
    ; edgeSource =
        G2DCC.sfgcShiftRightEdgeSource
    ; edgeTarget =
        G2DCC.sfgcShiftRightEdgeTarget
    ; connectionToDiscrete1Form =
        G2DCC.connectionToShiftRightEdge1Form
    ; evaluate1 =
        λ form edge → form edge
    ; evaluate2 =
        λ form plaquette → form plaquette
    ; δ₀ =
        G2DCC.sfgcShiftRightEdgeδ₀
    ; δ₁ =
        G2DCC.sfgcShiftRightEdgeTwoStepδ₁
    ; vacuumConnection =
        SFGC.vacuumGaugeField
    ; vacuumConnectionZero =
        G2DCC.vacuumShiftRightEdge1FormZero
    ; phase4PrimeLatticeCoefficientD2Zero =
        phase4PrimeLatticeD2Zero
    ; availableDegeneratePlaquetteZero =
        G2DCC.sfgcShiftRightEdgeTwoStepδ₁Zero
    ; availableDegenerateD2Zero =
        G2DCC.sfgcShiftRightEdgeTwoStepδ₁δ₀Zero
    ; firstMissingForDiscreteCurvatureCarrier =
        missingNondegenerateSFGCPlaquetteGeometry
    ; remainingMissingForDiscreteCurvatureCarrier =
        missingNondegenerateSFGCPlaquetteGeometry
        ∷ missingUOneFieldStrengthFromCurvature
        ∷ []
    ; interfaceBoundary =
        "This is the actual minimal U(1)-style system supported by the present SFGC API"
        ∷ "ConnectionCarrier is SFGC.GaugeField and connectionToDiscrete1Form is the right-edge sampler A edge"
        ∷ "Coefficient is Phase4 with zero φ0 and the local abelian coefficient law surface"
        ∷ "Vacuum-zero is definitional for SFGC.vacuumGaugeField on every right edge"
        ∷ "The available plaquette is the degenerate 1D two-step return boundary, whose δ1 and δ1δ0 both normalize to φ0"
        ∷ "This record is not a DiscreteCurvatureCarrier because it lacks a nondegenerate plaquette geometry and fieldStrengthFromCurvature"
        ∷ []
    }

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

    minimalDiscreteUOneConnectionSystem :
      DiscreteUOneConnectionSystem SFGC.GaugeField

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
    ; minimalDiscreteUOneConnectionSystem =
        canonicalSFGCDiscreteUOneConnectionSystem
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
