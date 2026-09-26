{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650BadCollarSingleSelfMismatchRound678Exact where

------------------------------------------------------------------------
-- ROUND678 / ENTIRE R667 BAD-COLLAR RESIDUAL COLLAPSES TO ONE SELF-KERNEL/A3 MISMATCH
--
-- R676:
--
--   16 Q = 4 SelfMismatch + R (4 H_ext - FluxTangent).
--
-- R677:
--
--   4 H_ext - FluxTangent
--     = 4 (SelfKernelWork - SelfForcingFull).
--
-- R607 defines
--
--   SelfMismatch = R * SelfForcingFull - 4 * A3.
--
-- Therefore the SelfForcingFull terms cancel exactly:
--
--   16 Q
--     = 4 (R * SelfKernelWork - 4 * A3).
--
-- Equivalently,
--
--   4 Q = R * SelfKernelWork - 4 * A3.
--
-- This is the sharpest local exact recut currently available.  It shows that
-- the external-helicity/tangent channel and the R607 selected-self forcing
-- channel are not independent analytic obligations once kept signed and
-- combined.  The surviving scalar is one self-kernel/A3 mismatch.
--
-- No estimate, absolute value, positivity replacement, or new Clay leaf is
-- introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; Positive; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as R30
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedEndpointCompilerExact as Endpoint
import DASHI.Physics.Closure.NSTriadKNA3CenteredKernelNormalFormExact as Kernel
import DASHI.Physics.Closure.NSTriadKNR650HelicityTangentSelfCollapseRound677Exact as R677

F : C3.RealField _
F = Rational.rationalRealField

module LiveSingleMismatch
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf :
      (Time → ℚ) → (Time → ℚ) → Set)
    (projectedCross :
      R426.ProjectedCrossDerivativeCalculus Time VectorDerivativeOf)
    (vectorAlgebra :
      R425.VectorDerivativeAlgebra Time VectorDerivativeOf)
    (zeroCalculus :
      Endpoint.VectorZeroDerivative Time VectorDerivativeOf)
    (hermitianCalculus :
      R417.HermitianDerivativeCalculus
        Time VectorDerivativeOf ScalarDerivativeOf)
    (scalarScaleCalculus :
      R416.ScalarConstantDerivativeCalculus
        Time ScalarDerivativeOf)
    (FTC :
      R564.ScalarFundamentalTheorem564
        Time initialTime integrateTo ScalarDerivativeOf)
    (integrationLinearity :
      Energy.ScalarIntegrationLinearity Time integrateTo)
    (D :
      R408.LiteralDynamics.LiteralRHSTrajectoryData
        Time initialTime integrateTo VectorDerivativeOf) where

  module C = R677.LiveSelfCollapse
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus scalarScaleCalculus FTC integrationLinearity D

  module At
      (cutoff : Nat)
      (output : Z3.FourierMode)
      (time : Time)
      (viscosityPositive :
        Positive (R30.viscosity (C.C.N.End.physicalSystemAt cutoff time)))
      (outputNonzero : Z3.NonZeroMode output) where

    module Base = C.At
      cutoff output time viscosityPositive outputNonzero

    rateTotal : ℚ
    rateTotal = Base.Base.Base.Base.M.rateTotal

    signedA3 : ℚ
    signedA3 = Base.Base.Base.Base.M.signedA3

    selfKernelWork : ℚ
    selfKernelWork = Base.selfKernelWork

    selfForcingFull : ℚ
    selfForcingFull = Base.selfForcingFull

    residual : ℚ
    residual = Base.Base.residual

    selfMismatchMeaning :
      Base.Base.Base.Split.selfMismatch
      ≡ rateTotal * selfForcingFull - Kernel.four * signedA3
    selfMismatchMeaning = refl

    sixteenResidualIsSingleSelfKernelMismatch :
      (Kernel.four * Kernel.four) * residual
      ≡
      Kernel.four
        * (rateTotal * selfKernelWork - Kernel.four * signedA3)
    sixteenResidualIsSingleSelfKernelMismatch =
      trans
        Base.Base.sixteenResidualIsSelfPlusRateCombinedSigned
        (trans
          (cong
            (λ combined →
              Kernel.four * Base.Base.Base.Split.selfMismatch
                + rateTotal * combined)
            Base.combinedHelicityTangentIsSelfDiscrepancy)
          (trans
            (cong
              (λ selfMismatch →
                Kernel.four * selfMismatch
                  + rateTotal
                      * (Kernel.four
                          * (selfKernelWork - selfForcingFull)))
              selfMismatchMeaning)
            (solve
              ( Kernel.four
              ∷ rateTotal
              ∷ selfKernelWork
              ∷ selfForcingFull
              ∷ signedA3
              ∷ []))))


------------------------------------------------------------------------
-- Status / preferred local frontier.
------------------------------------------------------------------------

round678BadCollarResidualSingleSelfKernelMismatchClosed : Bool
round678BadCollarResidualSingleSelfKernelMismatchClosed = true

round678ExternalHelicityIndependentAnalyticLeafAfterSignedCollapse : Bool
round678ExternalHelicityIndependentAnalyticLeafAfterSignedCollapse = false

round678FluxTangentIndependentAnalyticLeafAfterSignedCollapse : Bool
round678FluxTangentIndependentAnalyticLeafAfterSignedCollapse = false

round678SelfForcingMismatchIndependentAnalyticLeafAfterSignedCollapse : Bool
round678SelfForcingMismatchIndependentAnalyticLeafAfterSignedCollapse = false

round678SingleSelfKernelA3QuantitativePaymentClosed : Bool
round678SingleSelfKernelA3QuantitativePaymentClosed = false

round678IntroducesEstimate : Bool
round678IntroducesEstimate = false

round678IntroducesNewClayLeaf : Bool
round678IntroducesNewClayLeaf = false

round678C2Closed : Bool
round678C2Closed = false

round678ClayPromotion : Bool
round678ClayPromotion = false

round678BadCollarResidualSingleSelfKernelMismatchClosedIsTrue :
  round678BadCollarResidualSingleSelfKernelMismatchClosed ≡ true
round678BadCollarResidualSingleSelfKernelMismatchClosedIsTrue = refl

round678ExternalHelicityIndependentAnalyticLeafAfterSignedCollapseIsFalse :
  round678ExternalHelicityIndependentAnalyticLeafAfterSignedCollapse ≡ false
round678ExternalHelicityIndependentAnalyticLeafAfterSignedCollapseIsFalse = refl

round678FluxTangentIndependentAnalyticLeafAfterSignedCollapseIsFalse :
  round678FluxTangentIndependentAnalyticLeafAfterSignedCollapse ≡ false
round678FluxTangentIndependentAnalyticLeafAfterSignedCollapseIsFalse = refl

round678SelfForcingMismatchIndependentAnalyticLeafAfterSignedCollapseIsFalse :
  round678SelfForcingMismatchIndependentAnalyticLeafAfterSignedCollapse ≡ false
round678SelfForcingMismatchIndependentAnalyticLeafAfterSignedCollapseIsFalse = refl

round678SingleSelfKernelA3QuantitativePaymentClosedIsFalse :
  round678SingleSelfKernelA3QuantitativePaymentClosed ≡ false
round678SingleSelfKernelA3QuantitativePaymentClosedIsFalse = refl

round678IntroducesEstimateIsFalse :
  round678IntroducesEstimate ≡ false
round678IntroducesEstimateIsFalse = refl

round678IntroducesNewClayLeafIsFalse :
  round678IntroducesNewClayLeaf ≡ false
round678IntroducesNewClayLeafIsFalse = refl

round678C2ClosedIsFalse :
  round678C2Closed ≡ false
round678C2ClosedIsFalse = refl

round678ClayPromotionIsFalse :
  round678ClayPromotion ≡ false
round678ClayPromotionIsFalse = refl
