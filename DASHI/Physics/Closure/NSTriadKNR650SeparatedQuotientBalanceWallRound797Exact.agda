{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SeparatedQuotientBalanceWallRound797Exact where

------------------------------------------------------------------------
-- ROUND797 / THE FULLY-SEPARATED CANCELLATION QUESTION IS NOW ONE BALANCE LAW
--
-- R796 proves exactly
--
--   D_sep = 9 B_sep - 2 Q_sep,
--
-- where
--   B_sep is the separated swap-paired R230 product-rule spectator fold, and
--   Q_sep is the single dyadic ordered-pair q-quotient production fold.
--
-- Therefore complete cancellation of the fully-separated W2 residual is
-- EQUIVALENT to the one physical same-object balance
--
--   2 Q_sep = 9 B_sep.
--
-- This owner deliberately does not assert that balance.  The finite C3/
-- dihedral orbit algebra is exhausted: the surviving seam compares two
-- different physical scalar constructions on the same separated carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _-_; _*_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedEndpointCompilerExact as Endpoint
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffModeCarrierExact as ModeCarrier
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as Fold
import DASHI.Physics.Closure.NSTriadKNR650CriticalProductionIncidenceCarrierRound744Exact as R744
import DASHI.Physics.Closure.NSTriadKNR650SeparatedResidualFactorTwentySevenRound793Exact as R793
import DASHI.Physics.Closure.NSTriadKNR650SeparatedResidualC3QuotientRound796Exact as R796

F : C3.RealField _
F = Rational.rationalRealField

module SeparatedBalanceWall
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
    (constantScaleCalculus :
      R416.ScalarConstantDerivativeCalculus
        Time ScalarDerivativeOf)
    (scalarDerivativeAlgebra :
      R412.ScalarDerivativeAlgebra Time ScalarDerivativeOf)
    (FTC :
      R564.ScalarFundamentalTheorem564
        Time initialTime integrateTo ScalarDerivativeOf)
    (integrationLinearity :
      Energy.ScalarIntegrationLinearity Time integrateTo)
    (integrationTransport :
      R495.IntegrationTransportAuthority Time integrateTo)
    (D :
      R408.LiteralDynamics.LiteralRHSTrajectoryData
        Time initialTime integrateTo VectorDerivativeOf)
    (C :
      ModeCarrier.LiteralModeCarrier.LiteralCutoffModeCarrier
        Time initialTime integrateTo VectorDerivativeOf
        (R408.LiteralDynamics.literalPhysicalTrajectory
          Time initialTime integrateTo VectorDerivativeOf D))
    (R :
      R405.LiteralCutoffSupport.LiteralNonzeroCutoffTrajectory
        Time initialTime integrateTo VectorDerivativeOf
        (R408.LiteralDynamics.literalPhysicalTrajectory
          Time initialTime integrateTo VectorDerivativeOf D)) where

  module Prev = R796.SeparatedC3Quotient
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Packet = Prev.Packet

  module At
      (cutoff : Nat)
      (time : Time)
      (S : Packet.LivePhysicalPacketStructure D C cutoff) where

    module P = Prev.At cutoff time S

    Dsep : ℚ
    Dsep = P.X.A.T.T.fullySeparatedFold

    Bsep : ℚ
    Bsep = P.pairedBaseFold

    Qsep : ℚ
    Qsep = P.quotientFold

    nine : ℚ
    nine = R793.twentySeven / R744.three

    separatedNormalForm :
      Dsep ≡ nine * Bsep - Fold.two * Qsep
    separatedNormalForm =
      P.separatedResidualFactorNine

    quotientBalanceImpliesSeparatedCancellation :
      Fold.two * Qsep ≡ nine * Bsep →
      Dsep ≡ 0ℚ
    quotientBalanceImpliesSeparatedCancellation balance =
      trans
        separatedNormalForm
        (trans
          (cong (nine * Bsep -_) balance)
          (solve (nine ∷ Bsep ∷ [])))

    separatedCancellationImpliesQuotientBalance :
      Dsep ≡ 0ℚ →
      Fold.two * Qsep ≡ nine * Bsep
    separatedCancellationImpliesQuotientBalance cancelled =
      let
        shifted =
          trans
            (sym separatedNormalForm)
            cancelled
      in
      trans
        (sym
          (solve
            ( Fold.two
            ∷ Qsep
            ∷ nine
            ∷ Bsep
            ∷ [])))
        (trans
          (cong
            (λ selected →
              Fold.two * Qsep + selected)
            shifted)
          (solve
            ( Fold.two
            ∷ Qsep
            ∷ nine
            ∷ Bsep
            ∷ [])))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round797SeparatedCancellationEquivalentToSingleQuotientBalance : Bool
round797SeparatedCancellationEquivalentToSingleQuotientBalance = true

round797OrbitClassificationStillOnCriticalPath : Bool
round797OrbitClassificationStillOnCriticalPath = false

round797ForeignC3CarrierIdentificationRequired : Bool
round797ForeignC3CarrierIdentificationRequired = false

round797QuotientBalanceClosed : Bool
round797QuotientBalanceClosed = false

round797IntroducesEstimate : Bool
round797IntroducesEstimate = false

round797W2Closed : Bool
round797W2Closed = false

round797ClayPromotion : Bool
round797ClayPromotion = false

round797SeparatedCancellationEquivalentToSingleQuotientBalanceIsTrue :
  round797SeparatedCancellationEquivalentToSingleQuotientBalance ≡ true
round797SeparatedCancellationEquivalentToSingleQuotientBalanceIsTrue = refl

round797OrbitClassificationStillOnCriticalPathIsFalse :
  round797OrbitClassificationStillOnCriticalPath ≡ false
round797OrbitClassificationStillOnCriticalPathIsFalse = refl

round797QuotientBalanceClosedIsFalse :
  round797QuotientBalanceClosed ≡ false
round797QuotientBalanceClosedIsFalse = refl

round797IntroducesEstimateIsFalse :
  round797IntroducesEstimate ≡ false
round797IntroducesEstimateIsFalse = refl

round797W2ClosedIsFalse :
  round797W2Closed ≡ false
round797W2ClosedIsFalse = refl

round797ClayPromotionIsFalse :
  round797ClayPromotion ≡ false
round797ClayPromotionIsFalse = refl
