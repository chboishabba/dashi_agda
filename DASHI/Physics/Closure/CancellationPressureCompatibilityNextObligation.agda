module DASHI.Physics.Closure.CancellationPressureCompatibilityNextObligation where

-- W9n: narrow next-obligation surface for the cancellation-pressure seam.
--
-- This module is intentionally non-promoting.  It does not inhabit
-- CancellationPressureCompatibility.  It names the exact witness needed for
-- the existing route, and the extra identification needed before the
-- weighted-valuation route can replace that theorem-level assumption.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer using (ℤ; +_)
open import Data.Vec using (Vec)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Arithmetic.ArithmeticIntegerEmbedding as AIE
import DASHI.Arithmetic.ArithmeticIntegerEmbeddingBridge as AIEB
import DASHI.Arithmetic.WeightedValuationEnergy as WVE
import DASHI.Geometry.QuadraticForm as QF
import DASHI.Physics.QuadraticEmergenceShiftInstance as QES
import DASHI.Physics.Closure.ContractionForcesQuadraticStrong as CFQS
import DASHI.Physics.Closure.ContractionForcesQuadraticTheorem as CFQT
import DASHI.Physics.Closure.DeltaToQuadraticBridgeTheorem as DQ

data W9CompatibilityRoute : Set where
  dischargeExistingCancellationPressureCompatibility : W9CompatibilityRoute
  replaceWithWeightedValuationForwardCandidate : W9CompatibilityRoute
  diagnosticOnly : W9CompatibilityRoute

record ExistingCancellationPressureCompatibilityObligation
  (theorem : CFQT.ContractionForcesQuadraticTheorem)
  (dim≡15 :
    CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15) :
  Setω where
  field
    -- This is exactly the open argument of
    -- DQ.canonicalCancellationPressureCompatibility.
    pressureWitness :
      ∀ s →
        + (AIEB.embed-scalarCancellationPressure
            DQ.pairIntegerPressureBridge
            s)
        ≡
        DQ.contractionEnergy theorem
          (DQ.canonicalDeltaTransport theorem dim≡15 s)

  dischargesExisting :
    DQ.CancellationPressureCompatibility theorem dim≡15
  dischargesExisting =
    DQ.canonicalCancellationPressureCompatibility
      theorem
      dim≡15
      pressureWitness

record WeightedValuationReplacementObligation
  (theorem : CFQT.ContractionForcesQuadraticTheorem)
  (dim≡15 :
    CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15) :
  Setω where
  field
    input : DQ.WeightedInput

    candidateQuadratic :
      QF.QuadraticForm
        (QES.AdditiveVecℤ
          {CFQT.ContractionForcesQuadraticTheorem.dimension theorem})
        QES.ScalarFieldℤ

    candidateAdmissible :
      CFQS.AdmissibleFor
        (CFQT.ContractionForcesQuadraticTheorem.dimension theorem)
        (CFQT.ContractionForcesQuadraticTheorem.dynamicsMap theorem)
        candidateQuadratic

    valuationTransportCoherent :
      DQ.canonicalValuationTransport theorem dim≡15 (WVE.left input)
      ≡
      subst (Vec ℤ) (sym dim≡15)
        (WVE.valuationVecℤ (WVE.left input))

    weightedValuationTransportCoherent :
      DQ.canonicalWeightedValuationTransport theorem dim≡15 (WVE.left input)
      ≡
      subst (Vec ℤ) (sym dim≡15)
        (WVE.weightedValuationVecℤ (WVE.left input))

    weightedQuadraticTransportCoherent :
      DQ.canonicalWeightedQuadraticTransport theorem dim≡15 (WVE.left input)
      ≡
      subst (Vec ℤ) (sym dim≡15)
        (WVE.weightedQuadraticVecℤ (WVE.left input))

    weightedQuadraticEnergyMatchesCandidateQuadratic :
      + (WVE.weightedQuadraticEnergy (WVE.left input))
      ≡
      QF.QuadraticForm.Q
        candidateQuadratic
        (DQ.canonicalWeightedQuadraticTransport
          theorem
          dim≡15
          (WVE.left input))

    -- This is the missing replacement seam.  Without it, the weighted lane
    -- can produce a forward delta candidate, but it cannot replace the
    -- cancellation-pressure compatibility expected by current consumers.
    cancellationPressureIdentifiesWeightedQuadraticEnergy :
      + (AIE.deltaSum (WVE.left input) (WVE.right input))
      ≡
      + (WVE.weightedQuadraticEnergy (WVE.left input))

  weightedTransportCompatibility :
    DQ.WeightedValuationTransportCompatibility
      theorem
      dim≡15
      (WVE.left input)
  weightedTransportCompatibility =
    record
      { candidateQuadratic = candidateQuadratic
      ; candidateAdmissible = candidateAdmissible
      ; valuationTransportCoherent = valuationTransportCoherent
      ; weightedValuationTransportCoherent = weightedValuationTransportCoherent
      ; weightedQuadraticTransportCoherent = weightedQuadraticTransportCoherent
      ; weightedQuadraticEnergyMatchesCandidateQuadratic =
          weightedQuadraticEnergyMatchesCandidateQuadratic
      }

data W9MissingIngredient : Set where
  missingPressureWitness : W9MissingIngredient
  missingCancellationToWeightedQuadraticIdentification : W9MissingIngredient
  missingWeightedTransportCompatibility : W9MissingIngredient

record CancellationPressureCompatibilityNextObligation
  (theorem : CFQT.ContractionForcesQuadraticTheorem)
  (dim≡15 :
    CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15) :
  Setω where
  field
    selectedRoute : W9CompatibilityRoute
    missingIngredient : W9MissingIngredient
    existingRoute :
      ExistingCancellationPressureCompatibilityObligation theorem dim≡15 →
      DQ.CancellationPressureCompatibility theorem dim≡15
    weightedReplacementRoute :
      (replacement :
        WeightedValuationReplacementObligation theorem dim≡15) →
      DQ.WeightedValuationTransportCompatibility
        theorem
        dim≡15
        (WVE.left
          (WeightedValuationReplacementObligation.input replacement))

currentMissingIngredientDiagnostic :
  (theorem : CFQT.ContractionForcesQuadraticTheorem) →
  (dim≡15 :
    CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15) →
  CancellationPressureCompatibilityNextObligation theorem dim≡15
currentMissingIngredientDiagnostic theorem dim≡15 =
  record
    { selectedRoute = diagnosticOnly
    ; missingIngredient = missingPressureWitness
    ; existingRoute =
        ExistingCancellationPressureCompatibilityObligation.dischargesExisting
    ; weightedReplacementRoute =
        WeightedValuationReplacementObligation.weightedTransportCompatibility
    }

weightedReplacementStillNeedsCancellationIdentification :
  (theorem : CFQT.ContractionForcesQuadraticTheorem) →
  (dim≡15 :
    CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15) →
  Setω
weightedReplacementStillNeedsCancellationIdentification theorem dim≡15 =
  WeightedValuationReplacementObligation theorem dim≡15

existingRouteStillNeedsPressureWitness :
  (theorem : CFQT.ContractionForcesQuadraticTheorem) →
  (dim≡15 :
    CFQT.ContractionForcesQuadraticTheorem.dimension theorem ≡ 15) →
  Setω
existingRouteStillNeedsPressureWitness theorem dim≡15 =
  ExistingCancellationPressureCompatibilityObligation theorem dim≡15
