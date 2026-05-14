module DASHI.Physics.Closure.SchwarzschildLimitCandidate where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.DiscreteConnectionCandidateFromCRT as DCRT
import DASHI.Physics.Closure.DiscreteEinsteinTensorCandidate as DET
import DASHI.Physics.Closure.GRNonFlatScalarAlgebraSurface as NF

------------------------------------------------------------------------
-- Schwarzschild-limit candidate surface.
--
-- The repository currently has a flat Minkowski receipt and diagnostic-only
-- CRT/non-flat connection surfaces.  This module therefore records the exact
-- carrier primitives needed before a Schwarzschild limit can be promoted.
-- It does not construct a non-flat metric, Birkhoff theorem, W4 source, or
-- standard GR derivation.

data SchwarzschildLimitCandidateStatus : Set where
  requestSurfaceOnlyNoPromotion :
    SchwarzschildLimitCandidateStatus

data SchwarzschildLimitFirstMissingPrimitive : Set where
  missingRadialValuation :
    SchwarzschildLimitFirstMissingPrimitive
  missingSphericalSymmetryPredicate :
    SchwarzschildLimitFirstMissingPrimitive
  missingW4MassSource :
    SchwarzschildLimitFirstMissingPrimitive
  missingBirkhoffCarrierProof :
    SchwarzschildLimitFirstMissingPrimitive
  missingWeakFieldNewtonianPotential :
    SchwarzschildLimitFirstMissingPrimitive
  missingSchwarzschildMetricMatch :
    SchwarzschildLimitFirstMissingPrimitive

data SchwarzschildLimitUnsupportedClaim : Set where
  unsupportedPromotedNonFlatGR :
    SchwarzschildLimitUnsupportedClaim
  unsupportedStandardSchwarzschildDerivation :
    SchwarzschildLimitUnsupportedClaim
  unsupportedCarrierBirkhoffTheorem :
    SchwarzschildLimitUnsupportedClaim
  unsupportedW4MatterSideClosure :
    SchwarzschildLimitUnsupportedClaim
  unsupportedWeakFieldLimitRecovery :
    SchwarzschildLimitUnsupportedClaim

record SchwarzschildLimitCarrierRequest
  (scalarOps : NF.GRCarrierScalarOperations) : Set₁ where
  open NF.GRCarrierScalarOperations scalarOps

  field
    Carrier :
      Set

    SchwarzschildMetricCarrier :
      Set

    radialValuation :
      Carrier →
      CarrierScalar

    sphericalSymmetryPredicate :
      Carrier →
      Set

    w4MassSource :
      Carrier →
      CarrierScalar

    birkhoffCarrierProof :
      (x : Carrier) →
      sphericalSymmetryPredicate x →
      Set

    weakFieldNewtonianPotential :
      Carrier →
      CarrierScalar

    schwarzschildMetricAt :
      Carrier →
      SchwarzschildMetricCarrier

    metricMatch :
      (x : Carrier) →
      (symmetry : sphericalSymmetryPredicate x) →
      birkhoffCarrierProof x symmetry →
      Set

    requestBoundary :
      List String

record SchwarzschildLimitCandidateDiagnostic : Set₁ where
  field
    status :
      SchwarzschildLimitCandidateStatus

    scalarSurface :
      NF.GRCarrierScalarOperations

    flatEinsteinTensorDiagnostic :
      DET.DiscreteEinsteinTensorCandidateDiagnostic

    connectionFromCRTDiagnostic :
      DCRT.DiscreteConnectionCandidateFromCRTDiagnostic

    firstMissing :
      SchwarzschildLimitFirstMissingPrimitive

    exactMissingPrimitives :
      List SchwarzschildLimitFirstMissingPrimitive

    landedSurface :
      List String

    missingSurface :
      List String

    unsupportedClaims :
      List SchwarzschildLimitUnsupportedClaim

    noPromotionBoundary :
      List String

    nextAdmissibleReceipt :
      String

canonicalSchwarzschildLimitCandidateDiagnostic :
  SchwarzschildLimitCandidateDiagnostic
canonicalSchwarzschildLimitCandidateDiagnostic =
  record
    { status =
        requestSurfaceOnlyNoPromotion
    ; scalarSurface =
        NF.canonicalGRFiniteRCarrierScalarOperations
    ; flatEinsteinTensorDiagnostic =
        DET.canonicalDiscreteEinsteinTensorCandidateDiagnostic
    ; connectionFromCRTDiagnostic =
        DCRT.canonicalDiscreteConnectionCandidateFromCRTDiagnostic
    ; firstMissing =
        missingRadialValuation
    ; exactMissingPrimitives =
        missingRadialValuation
        ∷ missingSphericalSymmetryPredicate
        ∷ missingW4MassSource
        ∷ missingBirkhoffCarrierProof
        ∷ missingWeakFieldNewtonianPotential
        ∷ missingSchwarzschildMetricMatch
        ∷ []
    ; landedSurface =
        "Flat Minkowski quadratic receipt"
        ∷ "Discrete Einstein tensor diagnostic surface"
        ∷ "CRT-derived connection diagnostic with no non-flat connection promotion"
        ∷ "Finite-r carrier scalar operation surface"
        ∷ []
    ; missingSurface =
        "radialValuation : Carrier -> CarrierScalar"
        ∷ "sphericalSymmetryPredicate : Carrier -> Set"
        ∷ "w4MassSource : Carrier -> CarrierScalar"
        ∷ "birkhoffCarrierProof : (x : Carrier) -> sphericalSymmetryPredicate x -> Set"
        ∷ "weakFieldNewtonianPotential : Carrier -> CarrierScalar"
        ∷ "metricMatch : (x : Carrier) -> (symmetry : sphericalSymmetryPredicate x) -> birkhoffCarrierProof x symmetry -> Set"
        ∷ []
    ; unsupportedClaims =
        unsupportedPromotedNonFlatGR
        ∷ unsupportedStandardSchwarzschildDerivation
        ∷ unsupportedCarrierBirkhoffTheorem
        ∷ unsupportedW4MatterSideClosure
        ∷ unsupportedWeakFieldLimitRecovery
        ∷ []
    ; noPromotionBoundary =
        "This module is a Schwarzschild-limit candidate/request surface only"
        ∷ "No GR non-flat promotion is introduced here"
        ∷ "No standard Schwarzschild derivation is imported or claimed"
        ∷ "No W4 matter-side mass source is constructed here"
        ∷ "No Birkhoff theorem is constructed for the carrier"
        ∷ "No weak-field Newtonian limit or metric match theorem is constructed here"
        ∷ []
    ; nextAdmissibleReceipt =
        "SchwarzschildLimitCarrierRequest with radial valuation, spherical symmetry, W4 mass source, carrier Birkhoff proof, weak-field Newtonian potential, and metric match"
    }

schwarzschildLimitExactFirstMissing :
  SchwarzschildLimitCandidateDiagnostic.firstMissing
    canonicalSchwarzschildLimitCandidateDiagnostic
  ≡
  missingRadialValuation
schwarzschildLimitExactFirstMissing = refl

schwarzschildLimitStatusIsRequestOnly :
  SchwarzschildLimitCandidateDiagnostic.status
    canonicalSchwarzschildLimitCandidateDiagnostic
  ≡
  requestSurfaceOnlyNoPromotion
schwarzschildLimitStatusIsRequestOnly = refl
