module DASHI.Physics.Closure.DiscreteEinsteinTensorCandidate where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ)
open import Data.List.Base using (List; _∷_; [])
open import Data.Unit using (⊤; tt)

import DASHI.Physics.Closure.MinkowskiLimitReceipt as ML

------------------------------------------------------------------------
-- Diagnostic-only GR candidate surface.
--
-- MinkowskiLimitReceipt supplies an exact flat Lorentzian quadratic.  This
-- module records the weakest next surface for a discrete curvature /
-- Einstein-tensor attempt.  It does not construct a curved connection, Ricci
-- contraction, Einstein equation law, source coupling, continuum limit, or GR
-- promotion receipt.

record DiscreteEinsteinTensorCandidateSurface : Set₁ where
  field
    Carrier :
      Set

    metricQuadratic :
      Carrier → ℤ

    connectionOrShift :
      Carrier → Carrier

    curvature :
      Carrier → Carrier → Carrier

    ricciTrace :
      Carrier → Carrier

    einsteinTensor :
      Carrier → Carrier

    flatCurvatureCondition :
      Set

    bianchiFlatCondition :
      Set

    sourceCouplingCondition :
      Set

    continuumLimitCondition :
      Set

flatIdentityShift :
  ML.MinkowskiCarrier →
  ML.MinkowskiCarrier
flatIdentityShift x = x

flatZeroCurvature :
  ML.MinkowskiCarrier →
  ML.MinkowskiCarrier →
  ML.MinkowskiCarrier
flatZeroCurvature x _ = x

flatZeroTrace :
  ML.MinkowskiCarrier →
  ML.MinkowskiCarrier
flatZeroTrace x = x

flatZeroEinsteinTensor :
  ML.MinkowskiCarrier →
  ML.MinkowskiCarrier
flatZeroEinsteinTensor x = x

flatOnlyDiscreteEinsteinTensorCandidateSurface :
  DiscreteEinsteinTensorCandidateSurface
flatOnlyDiscreteEinsteinTensorCandidateSurface =
  record
    { Carrier =
        ML.MinkowskiCarrier
    ; metricQuadratic =
        ML.minkowskiQuadratic
    ; connectionOrShift =
        flatIdentityShift
    ; curvature =
        flatZeroCurvature
    ; ricciTrace =
        flatZeroTrace
    ; einsteinTensor =
        flatZeroEinsteinTensor
    ; flatCurvatureCondition =
        ⊤
    ; bianchiFlatCondition =
        ⊤
    ; sourceCouplingCondition =
        ⊤
    ; continuumLimitCondition =
        ⊤
    }

flatCandidateUsesLandedMinkowskiQuadratic :
  DiscreteEinsteinTensorCandidateSurface.metricQuadratic
    flatOnlyDiscreteEinsteinTensorCandidateSurface
  ≡
  ML.minkowskiQuadratic
flatCandidateUsesLandedMinkowskiQuadratic = refl

flatCandidateNoCurvedGRPromotion :
  ML.CarrierQuadraticIsMinkowski.noCurvedGRPromotion
    ML.minkowskiLimitReceipt
flatCandidateNoCurvedGRPromotion =
  ML.minkowskiLimitNoCurvedGRPromotion

------------------------------------------------------------------------
-- First-missing diagnostic for the curved / field-equation route.

data DiscreteEinsteinTensorFirstMissingCondition : Set where
  missingNonFlatConnectionOrShift :
    DiscreteEinsteinTensorFirstMissingCondition
  missingCurvatureToRicciContraction :
    DiscreteEinsteinTensorFirstMissingCondition
  missingEinsteinTensorLaw :
    DiscreteEinsteinTensorFirstMissingCondition
  missingStressEnergySourceCoupling :
    DiscreteEinsteinTensorFirstMissingCondition
  missingContinuumLimitReceipt :
    DiscreteEinsteinTensorFirstMissingCondition

data DiscreteEinsteinTensorCandidateStatus : Set where
  flatMetricCandidateOnly :
    DiscreteEinsteinTensorCandidateStatus

record DiscreteEinsteinTensorCandidateDiagnostic : Set₁ where
  field
    status :
      DiscreteEinsteinTensorCandidateStatus

    flatMetricReceipt :
      ML.CarrierQuadraticIsMinkowski

    flatCandidateSurface :
      DiscreteEinsteinTensorCandidateSurface

    firstMissing :
      DiscreteEinsteinTensorFirstMissingCondition

    orderedRemainingConditions :
      List DiscreteEinsteinTensorFirstMissingCondition

    diagnosticBoundary :
      List String

    noGRPromotionBoundary :
      List String

canonicalDiscreteEinsteinTensorCandidateDiagnostic :
  DiscreteEinsteinTensorCandidateDiagnostic
canonicalDiscreteEinsteinTensorCandidateDiagnostic =
  record
    { status =
        flatMetricCandidateOnly
    ; flatMetricReceipt =
        ML.minkowskiLimitReceipt
    ; flatCandidateSurface =
        flatOnlyDiscreteEinsteinTensorCandidateSurface
    ; firstMissing =
        missingNonFlatConnectionOrShift
    ; orderedRemainingConditions =
        missingNonFlatConnectionOrShift
        ∷ missingCurvatureToRicciContraction
        ∷ missingEinsteinTensorLaw
        ∷ missingStressEnergySourceCoupling
        ∷ missingContinuumLimitReceipt
        ∷ []
    ; diagnosticBoundary =
        "MinkowskiLimitReceipt supplies the exact flat Lorentzian quadratic"
        ∷ "The candidate surface here is flat and identity-shift only"
        ∷ "Known GR/QFT closure files require downstream curvature, stress-energy, and Einstein-equation consumer fields"
        ∷ "No concrete non-flat connection or shift-curvature operator is present in this module"
        ∷ []
    ; noGRPromotionBoundary =
        "This module does not prove curved GR recovery"
        ∷ "This module does not construct an Einstein field equation law"
        ∷ "This module does not construct stress-energy/source coupling"
        ∷ "This module does not construct a continuum-limit receipt"
        ∷ "This module does not construct a GRQFT closure-promotion receipt"
        ∷ []
    }

discreteEinsteinTensorExactFirstMissing :
  DiscreteEinsteinTensorCandidateDiagnostic.firstMissing
    canonicalDiscreteEinsteinTensorCandidateDiagnostic
  ≡
  missingNonFlatConnectionOrShift
discreteEinsteinTensorExactFirstMissing = refl

discreteEinsteinTensorFlatConditionWitness :
  DiscreteEinsteinTensorCandidateSurface.flatCurvatureCondition
    (DiscreteEinsteinTensorCandidateDiagnostic.flatCandidateSurface
      canonicalDiscreteEinsteinTensorCandidateDiagnostic)
discreteEinsteinTensorFlatConditionWitness = tt
