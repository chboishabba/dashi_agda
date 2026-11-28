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
-- The previous least-privilege candidate was a zero-defect inequality:
--
--   literalR406Integral_N(T) <= IntegratedCombined_N(T).
--
-- 28 Nov physical-real source countercontrol: the raw signed difference has
-- BOTH signs on genuine C=1 Galerkin states and changes sign on a fixed
-- state when viscosity changes.  Therefore the unconditional comparison
-- is NOT an admissible universal physical estimate.  Its old conditional
-- compiler remains valid, but is no longer the prescribed endpoint route.
--
-- The NEW alternative retains the signed difference as a single SAME-SOURCE
-- physical time- and cutoff-indexed residual.  A cutoff-uniform terminal
-- ceiling for it, added to the existing R723 combined bound, builds R410
-- directly.  R652+R723 supply an exact physical signed-defect NUMERATOR,
-- so the residual is not an unrelated assumed scalar.  The quantitative
-- bound on this numerator remains a genuine OPEN physical proof obligation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Agda.Builtin.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

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
import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNFactoredFullCommutatorOnlyRound567Exact as R567
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

  ------------------------------------------------------------------------
  -- R652 AND R723 ACTUAL SAME-OBJECT SIGNED DEFECT NUMERATOR.
  --
  -- 2*(literal R406 - complete combined commutator)
  --   = 4*UNLIFTED R568 forcing
  --     - integrated self Gram - integrated self flux tangent
  --     - 2*R723 integrated combined commutator.
  --
  -- This is a genuine original physical-trajectory identity. It reduces
  -- R726's missing inequality to the sign/upper bound of a single
  -- physically generated integrated numerator. In particular, a positive
  -- rate-lifted Cauchy Gram does not set this numerator to zero.
  ------------------------------------------------------------------------

  module Source = R652.Coupling
    Time initialTime integrateTo DerivativeOf integrationTransport

  actualSignedDefectNumerator :
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (terminal : Time) → ℚ
  actualSignedDefectNumerator R cutoff terminal =
    R567.four567 *
      Source.Comm.integratedGlobalForcingFull
        T R cutoff terminal
      - integrateTo (Source.Live.selfGram T R cutoff) terminal
      - integrateTo (Source.Live.selfFluxTangent T R cutoff) terminal
      - R539.two * Combined.integratedCombinedSelfExternal cutoff terminal

  actualSignedDefectNumeratorIdentity :
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (terminal : Time) →
    R539.two *
      (Unified.literalRemainderIntegral T R cutoff terminal
        - Combined.integratedCombinedSelfExternal cutoff terminal)
    ≡ actualSignedDefectNumerator R cutoff terminal
  actualSignedDefectNumeratorIdentity R cutoff terminal =
    let
      r = Unified.literalRemainderIntegral T R cutoff terminal
      g = integrateTo (Source.Live.selfGram T R cutoff) terminal
      h = integrateTo (Source.Live.selfFluxTangent T R cutoff) terminal
      c = Combined.integratedCombinedSelfExternal cutoff terminal

      source : R567.four567 *
          Source.Comm.integratedGlobalForcingFull T R cutoff terminal
          ≡ R539.two * r + g + h
      source =
        Source.integratedFourForcingIsTwoR406PlusDiagonal
          T R cutoff terminal

      normal :
        R539.two * (r - c)
        ≡ (((R539.two * r + g + h) - g) - h)
            - R539.two * c
      normal = solve (r ∷ g ∷ h ∷ c ∷ [])
    in
    trans normal
      (sym
        (cong
          (λ x → (((x - g) - h) - R539.two * c))
          source))

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
  -- Signed COMPENSATED route, preserving the original R406 currency.
  --
  -- The old R726 transport insists literalR406 <= combined.  This is
  -- strictly stronger than the estimate needed by R410: a terminal
  -- signed defect bounded uniformly over the physical cutoff suffices.
  -- The original R723 time-only ceiling and the defect's time-only
  -- ceiling then sum WITHOUT replacing the unlifted R568 work by its
  -- rate-lifted R687 partner.
  --
  -- Neither the defect's signed bound nor the R723 physical bound is
  -- constructed in this algebraic compiler.  They are real analytic
  -- producers, not flags disguised as proof terms.
  ------------------------------------------------------------------------

  record CompensatedCombinedR406Transport
      (R : Support.LiteralNonzeroCutoffTrajectory T) : Set₁ where
    field
      signedDefectCeiling : Time → ℚ
      literalR406BelowCombinedPlusDefect :
        (cutoff : Nat) (terminal : Time) →
        Unified.literalRemainderIntegral T R cutoff terminal
        ≤ Combined.integratedCombinedSelfExternal cutoff terminal
          + signedDefectCeiling terminal

  open CompensatedCombinedR406Transport public

  compensatedCombinedBuildsExistingR410 :
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Combined.CutoffUniformCombinedSelfExternalPayment →
    CompensatedCombinedR406Transport R →
    Target.SignedCriticalCancellation T R
  compensatedCombinedBuildsExistingR410 R P D = record
    { Target.cutoffIndependentRemainderBound =
        λ terminal →
          R700.twelve * Combined.cutoffIndependentBound P terminal
            + signedDefectCeiling D terminal
    ; Target.signedRemainderBudget =
        λ cutoff terminal →
          ℚP.≤-trans
            (literalR406BelowCombinedPlusDefect D cutoff terminal)
            (ℚP.+-mono-≤
              (Combined.combinedSelfExternalPayment P cutoff terminal)
              ℚP.≤-refl)
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

-- A stronger original zero-defect receipt is OPTIONAL.  The compensated
-- compiler is theorem-bearing but its cutoff-uniform real physical signed
-- defect estimate remains an uninhabited producer.
round726ExactPhysicalRealSignedCountercontrolScriptInstalled : Bool
round726ExactPhysicalRealSignedCountercontrolScriptInstalled = true

round726NativeAlgebraicFieldCountercontrolInhabited : Bool
round726NativeAlgebraicFieldCountercontrolInhabited = false

round726SamePhysicalDefectNumeratorIdentityClosed : Bool
round726SamePhysicalDefectNumeratorIdentityClosed = true

round726CompensatedR406CompilerClosed : Bool
round726CompensatedR406CompilerClosed = true

round726CompensatedSignedDefectPhysicalPaymentClosed : Bool
round726CompensatedSignedDefectPhysicalPaymentClosed = false

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
