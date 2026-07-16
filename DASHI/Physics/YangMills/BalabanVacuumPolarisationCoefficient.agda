module DASHI.Physics.YangMills.BalabanVacuumPolarisationCoefficient where

-- Exact source-facing seam for CMP 109 I, (5.42).  This module does not
-- pretend to evaluate a continuum beta coefficient: it records the finite
-- fluctuation effective action, its off-diagonal second variation, and the
-- coordinate-moment identity consumed by the cutoff coupling law.

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (ℕ; _<_)
open import Data.Empty using (⊥)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( SourceAuthorityId ; VerificationStatus ; balaban-cmp-109 ; openTarget )
open import DASHI.Physics.YangMills.BalabanEffectiveCouplingTrajectory using
  ( BalabanInverseSquareCouplingStep )
open import DASHI.Physics.YangMills.BalabanCutoffBetaLaw using
  ( BalabanVacuumPolarisationCoefficient )

record BalabanFiniteFluctuationOperatorPacket (K : ℕ) : Set₁ where
  field
    Background Fluctuation CoarseVariation : Set
    background : ℕ → Background
    fluctuationHessian : ℕ → Background → Fluctuation → Fluctuation
    constrainedCovariance : ℕ → Background → Fluctuation → Fluctuation
    linearisedBackgroundMap : ℕ → Background → CoarseVariation → Fluctuation
    regularBackgroundTube : Set

    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    noClayPromotion : clayYangMillsPromoted ≡ false

open BalabanFiniteFluctuationOperatorPacket public

record BalabanExactVacuumPolarisationCoefficient
    (K : ℕ)
    (step : BalabanInverseSquareCouplingStep) : Set₁ where
  field
    operators : BalabanFiniteFluctuationOperatorPacket K

    -- `fluctuationEffectiveAction k U` is the finite-lattice logarithmic
    -- fluctuation integral in the normalization of CMP 109 I, §2 and §5.
    fluctuationEffectiveAction :
      ℕ → Background operators → ℝ

    -- This carrier represents the source's off-diagonal second variation of
    -- that action.  Its exact coordinate representation and equality with
    -- the inverse-square correction live in the imported coefficient packet.
    secondVariationKernel : Set
    transversePlusThirdDerivativeRemainder : Set

    coefficient : BalabanVacuumPolarisationCoefficient K step

    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    noClayPromotion : clayYangMillsPromoted ≡ false

open BalabanExactVacuumPolarisationCoefficient public

actualBalabanExactVacuumPolarisationCoefficientAvailable : Set
actualBalabanExactVacuumPolarisationCoefficientAvailable = ⊥

currentBalabanVacuumPolarisationCoefficientStatus : VerificationStatus
currentBalabanVacuumPolarisationCoefficientStatus = openTarget
