module DASHI.Physics.Closure.EinsteinEquationCandidate where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Unit using (⊤; tt)

import DASHI.Physics.Closure.DiscreteEinsteinTensorCandidate as DET
import DASHI.Physics.Closure.W4PhysicalCalibrationObligationSurface as W4

------------------------------------------------------------------------
-- Discrete Einstein-equation obligation surface.
--
-- Revised GR framing:
-- * the current flat-vacuum surface is correct;
-- * non-flat connection/source terms are not constructed here;
-- * any non-flat/source route is gated on W4 matter coupling;
-- * the target equation is only the obligation shape
--     G_mu_nu = 8pi T_mu_nu.
--
-- This module does not claim Bianchi, continuum limit, non-flat connection,
-- GR recovery, or promotion into a downstream GR/QFT closure receipt.

data EinsteinEquationCandidateStatus : Set where
  flatVacuumCorrectW4MatterCouplingNeeded :
    EinsteinEquationCandidateStatus

data EinsteinEquationFirstMissingField : Set where
  missingW4MatterCouplingReceipt :
    EinsteinEquationFirstMissingField
  missingW4SourcedNonFlatConnection :
    EinsteinEquationFirstMissingField
  missingW4StressEnergyTensor :
    EinsteinEquationFirstMissingField
  missingDiscreteEinsteinEquationLaw :
    EinsteinEquationFirstMissingField

data EinsteinEquationMatterCouplingQueueField : Set where
  missingW4AnchorReceipt :
    EinsteinEquationMatterCouplingQueueField
  missingW4CalibrationAuthority :
    EinsteinEquationMatterCouplingQueueField
  missingW4MatterField :
    EinsteinEquationMatterCouplingQueueField
  missingW4StressEnergyTensorFromMatterField :
    EinsteinEquationMatterCouplingQueueField
  missingDiscreteEinsteinEquationLawFromStressEnergy :
    EinsteinEquationMatterCouplingQueueField

canonicalEinsteinEquationFirstMissingFields :
  List EinsteinEquationFirstMissingField
canonicalEinsteinEquationFirstMissingFields =
  missingW4MatterCouplingReceipt
  ∷ missingW4SourcedNonFlatConnection
  ∷ missingW4StressEnergyTensor
  ∷ missingDiscreteEinsteinEquationLaw
  ∷ []

canonicalEinsteinEquationMatterCouplingQueue :
  List EinsteinEquationMatterCouplingQueueField
canonicalEinsteinEquationMatterCouplingQueue =
  missingW4AnchorReceipt
  ∷ missingW4CalibrationAuthority
  ∷ missingW4MatterField
  ∷ missingW4StressEnergyTensorFromMatterField
  ∷ missingDiscreteEinsteinEquationLawFromStressEnergy
  ∷ []

data EinsteinEquationUnsupportedClaim : Set where
  unsupportedBianchiClaim :
    EinsteinEquationUnsupportedClaim
  unsupportedContinuumLimitClaim :
    EinsteinEquationUnsupportedClaim
  unsupportedNonFlatConnectionClaim :
    EinsteinEquationUnsupportedClaim
  unsupportedGRRecoveryClaim :
    EinsteinEquationUnsupportedClaim

canonicalEinsteinEquationUnsupportedClaims :
  List EinsteinEquationUnsupportedClaim
canonicalEinsteinEquationUnsupportedClaims =
  unsupportedBianchiClaim
  ∷ unsupportedContinuumLimitClaim
  ∷ unsupportedNonFlatConnectionClaim
  ∷ unsupportedGRRecoveryClaim
  ∷ []

record EinsteinEquationCandidateObligationSurface : Setω where
  field
    status :
      EinsteinEquationCandidateStatus

    flatVacuumSurface :
      DET.DiscreteEinsteinTensorCandidateSurface

    flatVacuumCondition :
      DET.DiscreteEinsteinTensorCandidateSurface.flatCurvatureCondition
        flatVacuumSurface

    discreteEinsteinTensorDiagnostic :
      DET.DiscreteEinsteinTensorCandidateDiagnostic

    w4MatterCouplingGate :
      W4.W4PhysicalCalibrationObligationSurface

    w4AnchorName :
      String

    equationTargetLabel :
      String

    sourceTermLabel :
      String

    firstMissing :
      EinsteinEquationFirstMissingField

    orderedFirstMissingFields :
      List EinsteinEquationFirstMissingField

    matterCouplingQueue :
      List EinsteinEquationMatterCouplingQueueField

    nextMatterCouplingQueueField :
      EinsteinEquationMatterCouplingQueueField

    nextQueueFieldIsW4Anchor :
      nextMatterCouplingQueueField
      ≡
      missingW4AnchorReceipt

    firstMissingIsW4MatterCoupling :
      firstMissing
      ≡
      missingW4MatterCouplingReceipt

    unsupportedClaims :
      List EinsteinEquationUnsupportedClaim

    obligationBoundary :
      List String

    nonPromotionBoundary :
      List String

canonicalEinsteinEquationCandidateObligationSurface :
  EinsteinEquationCandidateObligationSurface
canonicalEinsteinEquationCandidateObligationSurface =
  record
    { status =
        flatVacuumCorrectW4MatterCouplingNeeded
    ; flatVacuumSurface =
        DET.flatOnlyDiscreteEinsteinTensorCandidateSurface
    ; flatVacuumCondition =
        tt
    ; discreteEinsteinTensorDiagnostic =
        DET.canonicalDiscreteEinsteinTensorCandidateDiagnostic
    ; w4MatterCouplingGate =
        W4.canonicalW4PhysicalCalibrationObligationSurface
    ; w4AnchorName =
        W4.W4PhysicalCalibrationObligationSurface.zPeakAnchorName
          W4.canonicalW4PhysicalCalibrationObligationSurface
    ; equationTargetLabel =
        "G_mu_nu = 8pi T_mu_nu"
    ; sourceTermLabel =
        "T_mu_nu must come from W4 matter coupling before a non-flat GR target can be consumed"
    ; firstMissing =
        missingW4MatterCouplingReceipt
    ; orderedFirstMissingFields =
        canonicalEinsteinEquationFirstMissingFields
    ; matterCouplingQueue =
        canonicalEinsteinEquationMatterCouplingQueue
    ; nextMatterCouplingQueueField =
        missingW4AnchorReceipt
    ; nextQueueFieldIsW4Anchor =
        refl
    ; firstMissingIsW4MatterCoupling =
        refl
    ; unsupportedClaims =
        canonicalEinsteinEquationUnsupportedClaims
    ; obligationBoundary =
        "Flat vacuum is the currently correct local GR surface"
        ∷ "The target equation is recorded only as G_mu_nu = 8pi T_mu_nu"
        ∷ "The first W4 gate is the W4 anchor receipt"
        ∷ "W4 calibration authority must follow the anchor before matter is available"
        ∷ "T_mu_nu is gated on a W4 matter field and stress-energy tensor"
        ∷ "Any non-flat connection must be sourced through the W4 matter-coupling queue"
        ∷ "The current W4 surface remains an obligation surface, not a supplied matter-coupling receipt"
        ∷ []
    ; nonPromotionBoundary =
        "This module does not construct a non-flat connection"
        ∷ "This module does not prove Bianchi"
        ∷ "This module does not prove a continuum limit"
        ∷ "This module does not prove GR recovery"
        ∷ "This module does not inhabit a GR/QFT closure-promotion receipt"
        ∷ []
    }

einsteinEquationCandidateExactFirstMissing :
  EinsteinEquationCandidateObligationSurface.firstMissing
    canonicalEinsteinEquationCandidateObligationSurface
  ≡
  missingW4MatterCouplingReceipt
einsteinEquationCandidateExactFirstMissing = refl

einsteinEquationCandidateStatusIsObligationOnly :
  EinsteinEquationCandidateObligationSurface.status
    canonicalEinsteinEquationCandidateObligationSurface
  ≡
  flatVacuumCorrectW4MatterCouplingNeeded
einsteinEquationCandidateStatusIsObligationOnly = refl
