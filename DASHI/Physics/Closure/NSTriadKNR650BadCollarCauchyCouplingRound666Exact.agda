{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650BadCollarCauchyCouplingRound666Exact where

------------------------------------------------------------------------
-- ROUND666 / BAD-COLLAR RATE-WEIGHTED KERNEL <-> R598 CAUCHY/A3 MISMATCH
--
-- R665 gives on the live full output fibre
--
--   4 Q = n W(M,K_r),
--
-- where
--
--   Q = SelfRate + PairDiff.
--
-- R598 gives on the SAME literal physical fibre
--
--   R (4 F) - 4 (4 A3)
--     = R FluxTangent + 4 n W(M,K_r).
--
-- Substitution therefore yields the exact coupled normal form
--
--   R (4 F) - 16 A3
--     = R FluxTangent + 16 Q.
--
-- Equivalently,
--
--   16 Q
--     = R (4 F) - 16 A3 - R FluxTangent.
--
-- This is useful because the surviving local bad-collar C2 scalar now sits
-- directly inside the existing Cauchy/R567 forcing vocabulary used by C1.
-- It does NOT close C2: the R598 mismatch remains genuinely unpaid.  The point
-- is to remove a representation seam, not manufacture a sign or estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; Positive; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

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
import DASHI.Physics.Closure.NSTriadKNA3CauchyFluxTangentMismatchRound598Exact as R598
import DASHI.Physics.Closure.NSTriadKNR650EuclideanCollarRefinementRound656Exact as R656
import DASHI.Physics.Closure.NSTriadKNR650BadCollarRateWeightedKernelRound665Exact as R665

F : C3.RealField _
F = Rational.rationalRealField

module LiveCoupling
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

  module K = R665.LiveKernel
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus scalarScaleCalculus FTC integrationLinearity D

  module End = Endpoint.Endpoint
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus scalarScaleCalculus FTC D

  module Live = R408.LiteralDynamics
    Time initialTime integrateTo VectorDerivativeOf

  module At
      (cutoff : Nat)
      (output : Z3.FourierMode)
      (time : Time)
      (viscosityPositive :
        Positive
          (R30.viscosity (End.physicalSystemAt cutoff time)))
      (outputNonzero : Z3.NonZeroMode output) where

    system =
      End.physicalSystemAt cutoff time

    P =
      K.physicalHelicityAt cutoff time

    module M = R598.FixedOutput
      system End.S K.L K.H P viscosityPositive output outputNonzero

    residual : ℚ
    residual =
      K.Weighted.Sp.rateSelfWorkAt cutoff output time
      + K.Weighted.Sp.pairDifferenceWorkAt cutoff output time

    r665KernelIdentity :
      Kernel.four * residual
      ≡
      K.Weighted.Sp.fibreCardinality cutoff output
        * K.rateWeightedKernelWorkAt cutoff output time
    r665KernelIdentity =
      K.liveResidualIsRateWeightedKernel cutoff output time

    r598KernelWorkSameObject :
      M.weightedKernelWork
      ≡ K.rateWeightedKernelWorkAt cutoff output time
    r598KernelWorkSameObject = refl

    cauchyA3MismatchIsBadCollarResidual :
      M.rateTotal * (Kernel.four * M.forcingFull)
        - Kernel.four * (Kernel.four * M.signedA3)
      ≡
      M.rateTotal * M.fluxTangentFull
        + (Kernel.four * Kernel.four) * residual
    cauchyA3MismatchIsBadCollarResidual =
      trans
        M.cauchyA3MismatchNormalForm
        (trans
          (cong
            (M.rateTotal * M.fluxTangentFull +_)
            (cong
              (Kernel.four *_)
              (cong
                (K.Weighted.Sp.fibreCardinality cutoff output *_)
                r598KernelWorkSameObject)))
          (trans
            (cong
              (M.rateTotal * M.fluxTangentFull +_)
              (cong
                (Kernel.four *_)
                (sym r665KernelIdentity)))
            (solve
              ( M.rateTotal
              ∷ M.fluxTangentFull
              ∷ residual
              ∷ Kernel.four
              ∷ []))))

    badCollarResidualAsCauchyMismatch :
      (Kernel.four * Kernel.four) * residual
      ≡
      M.rateTotal * (Kernel.four * M.forcingFull)
        - Kernel.four * (Kernel.four * M.signedA3)
        - M.rateTotal * M.fluxTangentFull
    badCollarResidualAsCauchyMismatch
      rewrite cauchyA3MismatchIsBadCollarResidual =
      solve
        ( M.rateTotal
        ∷ M.forcingFull
        ∷ M.signedA3
        ∷ M.fluxTangentFull
        ∷ residual
        ∷ Kernel.four
        ∷ [])

    activeBadCollarCauchyCoupling :
      (Kshell : Nat) →
      R656.badCollarPacket Kshell output ≡ true →
      M.rateTotal * (Kernel.four * M.forcingFull)
        - Kernel.four * (Kernel.four * M.signedA3)
      ≡
      M.rateTotal * M.fluxTangentFull
        + (Kernel.four * Kernel.four) * residual
    activeBadCollarCauchyCoupling Kshell active =
      cauchyA3MismatchIsBadCollarResidual

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round666BadCollarResidualOnR598MismatchCarrier : Bool
round666BadCollarResidualOnR598MismatchCarrier = true

round666C1C2ShareRateWeightedKernelVocabulary : Bool
round666C1C2ShareRateWeightedKernelVocabulary = true

round666R598MismatchPaid : Bool
round666R598MismatchPaid = false

round666IntroducesNewAnalyticEstimate : Bool
round666IntroducesNewAnalyticEstimate = false

round666IntroducesNewClayLeaf : Bool
round666IntroducesNewClayLeaf = false

round666C2Closed : Bool
round666C2Closed = false

round666ClayPromotion : Bool
round666ClayPromotion = false

round666BadCollarResidualOnR598MismatchCarrierIsTrue :
  round666BadCollarResidualOnR598MismatchCarrier ≡ true
round666BadCollarResidualOnR598MismatchCarrierIsTrue = refl

round666C1C2ShareRateWeightedKernelVocabularyIsTrue :
  round666C1C2ShareRateWeightedKernelVocabulary ≡ true
round666C1C2ShareRateWeightedKernelVocabularyIsTrue = refl

round666R598MismatchPaidIsFalse :
  round666R598MismatchPaid ≡ false
round666R598MismatchPaidIsFalse = refl

round666IntroducesNewAnalyticEstimateIsFalse :
  round666IntroducesNewAnalyticEstimate ≡ false
round666IntroducesNewAnalyticEstimateIsFalse = refl

round666IntroducesNewClayLeafIsFalse :
  round666IntroducesNewClayLeaf ≡ false
round666IntroducesNewClayLeafIsFalse = refl

round666C2ClosedIsFalse :
  round666C2Closed ≡ false
round666C2ClosedIsFalse = refl

round666ClayPromotionIsFalse :
  round666ClayPromotion ≡ false
round666ClayPromotionIsFalse = refl
