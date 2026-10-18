{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650CombinedToLiteralR406Round726Exact where

------------------------------------------------------------------------
-- ROUND726 / ONE MISSING SAME-OBJECT SEAM: R723 COMBINED COMMUTATOR -> R406
--
-- R723 produces the exact cutoff-uniform payment on
--
--   IntegratedCombined_N(T) = 12 * R691.GlobalCommutator_N(T).
--
-- The canonical continuation spine, however, consumes the literal R406
-- remainder through R410/R414.  R652 couples R406 to the R568 forcing-full
-- square plus diagonal terms, but R687 explicitly prevents silently replacing
-- that forcing-full square by the R691 commutator.
--
-- Therefore the least-privilege downstream seam is one physical inequality:
--
--   literalR406Integral_N(T) <= IntegratedCombined_N(T).
--
-- This owner does NOT assert that inequality.  It names it as a single typed
-- transport theorem and proves that, once supplied together with the already
-- paid R723 combined bound, it constructs the existing R410 cancellation
-- object directly.  No parallel remainder consumer is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedEndpointCompilerExact as Endpoint
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNSignedTTStarCriticalCancellationTargetRound410Exact as R410
import DASHI.Physics.Closure.NSTriadKNOneCancellationPaysRemainderAndCriticalRound414Exact as R414
import DASHI.Physics.Closure.NSTriadKNR650C1R406DiagonalCouplingRound652Exact as R652
import DASHI.Physics.Closure.NSTriadKNR650RateLiftedR568ToC2CommutatorRound687Exact as R687
import DASHI.Physics.Closure.NSTriadKNR650CombinedSelfExternalSpacetimeRound723Exact as R723
import DASHI.Physics.Closure.NSTriadKNR650NestedFourHelicityTriadOrbitRound700Exact as R700

F : C3.RealField _
F = Rational.rationalRealField

module CombinedToR406
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
    (integrationTransport :
      R495.IntegrationTransportAuthority Time integrateTo)
    (D :
      R408.LiteralDynamics.LiteralRHSTrajectoryData
        Time initialTime integrateTo VectorDerivativeOf) where

  module Live = R408.LiteralDynamics
    Time initialTime integrateTo VectorDerivativeOf

  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo VectorDerivativeOf

  module Combined = R723.CombinedSpacetime
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus scalarScaleCalculus
    FTC integrationLinearity integrationTransport D

  module Unified = R414.Unified
    Time initialTime integrateTo VectorDerivativeOf

  module Target = R410.Target
    Time initialTime integrateTo VectorDerivativeOf

  T = Live.literalPhysicalTrajectory D

  record CombinedR406Transport
      (R : Support.LiteralNonzeroCutoffTrajectory T) : Set₁ where
    field
      literalR406BelowCombined :
        (cutoff : Nat) (terminal : Time) →
        Unified.literalRemainderIntegral T R cutoff terminal
        ≤ Combined.integratedCombinedSelfExternal cutoff terminal

  open CombinedR406Transport public

  combinedPaymentAndR406TransportBuildCancellation :
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Combined.CutoffUniformCombinedSelfExternalPayment →
    CombinedR406Transport R →
    Target.SignedCriticalCancellation T R
  combinedPaymentAndR406TransportBuildCancellation R P B = record
    { Target.cutoffIndependentRemainderBound =
        λ terminal →
          R700.twelve * Combined.cutoffIndependentBound P terminal
    ; Target.signedRemainderBudget =
        λ cutoff terminal →
          ℚP.≤-trans
            (literalR406BelowCombined B cutoff terminal)
            (Combined.combinedSelfExternalPayment P cutoff terminal)
    }

------------------------------------------------------------------------
-- Boundary / routing status.
------------------------------------------------------------------------

round726R652OnlyCouplesR406ToR568ForcingFull : Bool
round726R652OnlyCouplesR406ToR568ForcingFull =
  R652.round652PointwiseC1R406DiagonalCouplingClosed

round726R723AutomaticallyIsR568ForcingFull : Bool
round726R723AutomaticallyIsR568ForcingFull =
  R687.round687UnliftedR568BudgetControlsRateLiftedFull

round726SingleCombinedToR406TransportSufficesForR410 : Bool
round726SingleCombinedToR406TransportSufficesForR410 = true

round726CombinedToR406TransportClosed : Bool
round726CombinedToR406TransportClosed = false

round726IntroducesParallelR406Consumer : Bool
round726IntroducesParallelR406Consumer = false

round726IntroducesEstimate : Bool
round726IntroducesEstimate = false

round726ClayPromotion : Bool
round726ClayPromotion = false

round726R652OnlyCouplesR406ToR568ForcingFullIsTrue :
  round726R652OnlyCouplesR406ToR568ForcingFull ≡ true
round726R652OnlyCouplesR406ToR568ForcingFullIsTrue =
  R652.round652PointwiseC1R406DiagonalCouplingClosedIsTrue

round726R723AutomaticallyIsR568ForcingFullIsFalse :
  round726R723AutomaticallyIsR568ForcingFull ≡ false
round726R723AutomaticallyIsR568ForcingFullIsFalse =
  R687.round687UnliftedR568BudgetControlsRateLiftedFullIsFalse

round726SingleCombinedToR406TransportSufficesForR410IsTrue :
  round726SingleCombinedToR406TransportSufficesForR410 ≡ true
round726SingleCombinedToR406TransportSufficesForR410IsTrue = refl

round726CombinedToR406TransportClosedIsFalse :
  round726CombinedToR406TransportClosed ≡ false
round726CombinedToR406TransportClosedIsFalse = refl

round726IntroducesParallelR406ConsumerIsFalse :
  round726IntroducesParallelR406Consumer ≡ false
round726IntroducesParallelR406ConsumerIsFalse = refl

round726IntroducesEstimateIsFalse :
  round726IntroducesEstimate ≡ false
round726IntroducesEstimateIsFalse = refl

round726ClayPromotionIsFalse :
  round726ClayPromotion ≡ false
round726ClayPromotionIsFalse = refl
