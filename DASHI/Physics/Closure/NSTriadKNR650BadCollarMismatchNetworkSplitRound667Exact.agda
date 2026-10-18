{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650BadCollarMismatchNetworkSplitRound667Exact where

------------------------------------------------------------------------
-- ROUND667 / BAD-COLLAR RESIDUAL = SELF MISMATCH + EXTERNAL NETWORK - TANGENT
--
-- R666 gives
--
--   4 * CanonicalMismatch
--     = R * FluxTangent + 16 * Q,
--
-- where Q is the live bad-collar residual
--
--   Q = SelfRate + PairDiff.
--
-- R607 gives on the SAME fixed output
--
--   CanonicalMismatch = SelfMismatch + ExternalNetwork.
--
-- Therefore exactly
--
--   16 Q
--     = 4 SelfMismatch
--       + 4 ExternalNetwork
--       - R FluxTangent.
--
-- This is the correct C1/C2 cross-pollinated local normal form.  It leaves
-- both physical channels explicit and does not promote either to a theorem.
-- In particular R611 already rules out treating the forcing/A3 mismatch as a
-- universal amplitude-scale-free identity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; Positive; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

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
import DASHI.Physics.Closure.NSTriadKNA3CauchyMismatchNetworkSplitRound607Exact as R607
import DASHI.Physics.Closure.NSTriadKNR604AmplitudeHomogeneityNoGoRound611Exact as R611
import DASHI.Physics.Closure.NSTriadKNR650EuclideanCollarRefinementRound656Exact as R656
import DASHI.Physics.Closure.NSTriadKNR650BadCollarCauchyCouplingRound666Exact as R666

F : C3.RealField _
F = Rational.rationalRealField

module LiveNetworkSplit
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

  module C = R666.LiveCoupling
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus scalarScaleCalculus FTC integrationLinearity D

  module End = Endpoint.Endpoint
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus scalarScaleCalculus FTC D

  module At
      (cutoff : Nat)
      (output : Z3.FourierMode)
      (time : Time)
      (viscosityPositive :
        Positive (R30.viscosity (End.physicalSystemAt cutoff time)))
      (outputNonzero : Z3.NonZeroMode output) where

    module Base = C.At cutoff output time viscosityPositive outputNonzero

    module Split = R607.FixedOutput
      (End.physicalSystemAt cutoff time)
      End.S
      C.K.L
      C.K.H
      (C.K.physicalHelicityAt cutoff time)
      viscosityPositive
      output
      outputNonzero

    residual : ℚ
    residual = Base.residual

    mismatchSplitSameObject :
      Base.M.rateTotal * Base.M.forcingFull
        - Kernel.four * Base.M.signedA3
      ≡
      Split.selfMismatch + Split.externalNetworkContribution
    mismatchSplitSameObject =
      Split.canonicalMismatchSplitsSelfExternal

    sixteenResidualIsSelfExternalMinusFluxTangent :
      (Kernel.four * Kernel.four) * residual
      ≡
      Kernel.four * Split.selfMismatch
        + Kernel.four * Split.externalNetworkContribution
        - Base.M.rateTotal * Base.M.fluxTangentFull
    sixteenResidualIsSelfExternalMinusFluxTangent =
      let
        coupled :
          (Kernel.four * Kernel.four) * residual
          ≡
          Base.M.rateTotal * (Kernel.four * Base.M.forcingFull)
            - Kernel.four * (Kernel.four * Base.M.signedA3)
            - Base.M.rateTotal * Base.M.fluxTangentFull
        coupled = Base.badCollarResidualAsCauchyMismatch

        mismatchScaled :
          Base.M.rateTotal * (Kernel.four * Base.M.forcingFull)
            - Kernel.four * (Kernel.four * Base.M.signedA3)
          ≡
          Kernel.four
            * (Split.selfMismatch + Split.externalNetworkContribution)
        mismatchScaled =
          trans
            (solve
              ( Base.M.rateTotal
              ∷ Base.M.forcingFull
              ∷ Base.M.signedA3
              ∷ Kernel.four
              ∷ []))
            (cong (Kernel.four *_) mismatchSplitSameObject)
      in
      trans coupled
        (trans
          (cong
            (λ mismatch →
              mismatch - Base.M.rateTotal * Base.M.fluxTangentFull)
            mismatchScaled)
          (solve
            ( Split.selfMismatch
            ∷ Split.externalNetworkContribution
            ∷ Base.M.rateTotal
            ∷ Base.M.fluxTangentFull
            ∷ Kernel.four
            ∷ [])))

    activeBadCollarNetworkSplit :
      (Kshell : Nat) →
      R656.badCollarPacket Kshell output ≡ true →
      (Kernel.four * Kernel.four) * residual
      ≡
      Kernel.four * Split.selfMismatch
        + Kernel.four * Split.externalNetworkContribution
        - Base.M.rateTotal * Base.M.fluxTangentFull
    activeBadCollarNetworkSplit Kshell active =
      sixteenResidualIsSelfExternalMinusFluxTangent

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round667BadCollarResidualSelfExternalNetworkSplitClosed : Bool
round667BadCollarResidualSelfExternalNetworkSplitClosed = true

round667SelectedSelfMismatchPaid : Bool
round667SelectedSelfMismatchPaid =
  R607.round607SelectedSelfMismatchClosed

round667ExternalNetworkContributionPaid : Bool
round667ExternalNetworkContributionPaid =
  R607.round607ExternalNetworkContributionClosed

round667UniversalScaleFreeForcingA3IdentityAdmissible : Bool
round667UniversalScaleFreeForcingA3IdentityAdmissible =
  R611.r604UniversalScaleFreeSameObjectIdentityAdmissible

round667IntroducesNewAnalyticEstimate : Bool
round667IntroducesNewAnalyticEstimate = false

round667IntroducesNewClayLeaf : Bool
round667IntroducesNewClayLeaf = false

round667C2Closed : Bool
round667C2Closed = false

round667ClayPromotion : Bool
round667ClayPromotion = false

round667BadCollarResidualSelfExternalNetworkSplitClosedIsTrue :
  round667BadCollarResidualSelfExternalNetworkSplitClosed ≡ true
round667BadCollarResidualSelfExternalNetworkSplitClosedIsTrue = refl

round667SelectedSelfMismatchPaidIsFalse :
  round667SelectedSelfMismatchPaid ≡ false
round667SelectedSelfMismatchPaidIsFalse =
  R607.round607SelectedSelfMismatchClosedIsFalse

round667ExternalNetworkContributionPaidIsFalse :
  round667ExternalNetworkContributionPaid ≡ false
round667ExternalNetworkContributionPaidIsFalse =
  R607.round607ExternalNetworkContributionClosedIsFalse

round667UniversalScaleFreeForcingA3IdentityAdmissibleIsFalse :
  round667UniversalScaleFreeForcingA3IdentityAdmissible ≡ false
round667UniversalScaleFreeForcingA3IdentityAdmissibleIsFalse =
  R611.r604UniversalScaleFreeSameObjectIdentityAdmissibleIsFalse

round667IntroducesNewAnalyticEstimateIsFalse :
  round667IntroducesNewAnalyticEstimate ≡ false
round667IntroducesNewAnalyticEstimateIsFalse = refl

round667IntroducesNewClayLeafIsFalse :
  round667IntroducesNewClayLeaf ≡ false
round667IntroducesNewClayLeafIsFalse = refl

round667C2ClosedIsFalse :
  round667C2Closed ≡ false
round667C2ClosedIsFalse = refl

round667ClayPromotionIsFalse :
  round667ClayPromotion ≡ false
round667ClayPromotionIsFalse = refl
