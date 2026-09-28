{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SeparatedTwoCurrencyWallRound810Exact where

------------------------------------------------------------------------
-- ROUND810 / p=0 DEFECT ELIMINATED: THE SEPARATED WALL IS TWO PHYSICAL
--            SIGNED CURRENCIES AGAINST THE DYADIC QUOTIENT
--
-- R808:
--
--   D_sep
--     = 2 [
--         18 M_self
--       + 36 PZero
--       + 36 E_comm
--       - Q_sep ].
--
-- R809 proves on the SAME live physical system, using only all-mode
-- transversality and R436 zero-output algebra,
--
--   PZero = 0.
--
-- Hence exactly
--
--   D_sep
--     = 2 [ 18 M_self + 36 E_comm - Q_sep ],
--
-- and therefore
--
--   D_sep = 0
--     <->
--   Q_sep = 18 M_self + 36 E_comm.
--
-- The earlier apparent zero-mode provenance obligation is gone.  The remaining
-- separated problem compares only:
--
--   * the literal dyadic orderedPairPower q-quotient Q_sep,
--   * literal R625 four-helicity selected-self multiplier work M_self,
--   * literal R670 separated external commutator work E_comm.
--
-- No estimate, norm, absolute value, or canonical-u(0) assumption is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

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
import DASHI.Physics.Closure.NSTriadKNR650SeparatedPhysicalDefectNormalFormRound806Exact as R806
import DASHI.Physics.Closure.NSTriadKNR650SeparatedMultiplierCommutatorWallRound808Exact as R808
import DASHI.Physics.Closure.NSTriadKNR650SeparatedPZeroAlgebraicEliminationRound809Exact as R809

F : C3.RealField _
F = Rational.rationalRealField

module SeparatedTwoCurrencyWall
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

  module Prev =
    R808.SeparatedMultiplierCommutatorWall
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
    module Phys = P.P

    module PZeroKill =
      R809.SeparatedPZeroElimination
        Phys.physicalSystem
        Phys.helicalScalars
        Phys.projectorLaws
        Phys.halfCalibration
        Phys.transverse

    Dsep : ℚ
    Dsep = P.Dsep

    Qsep : ℚ
    Qsep = P.Qsep

    Mself : ℚ
    Mself = P.Mself

    Ecomm : ℚ
    Ecomm = P.Ecomm

    pZeroSamePhysicalCurrency :
      P.PZero ≡ PZeroKill.Sep.globalPZeroSelfDefectWork
    pZeroSamePhysicalCurrency = refl

    pZeroIsZero :
      P.PZero ≡ 0ℚ
    pZeroIsZero =
      trans
        pZeroSamePhysicalCurrency
        PZeroKill.globalPZeroSelfDefectWorkZero

    separatedTwoCurrencyNormalForm :
      Dsep
      ≡
      Fold.two *
        ( R806.eighteen * Mself
        + R806.thirtySix * Ecomm
        - Qsep )
    separatedTwoCurrencyNormalForm =
      trans
        P.separatedMultiplierCommutatorNormalForm
        (trans
          (cong
            (Fold.two *_)
            (cong
              (λ pZero →
                R806.eighteen * Mself
                + R806.thirtySix * pZero
                + R806.thirtySix * Ecomm
                - Qsep)
              pZeroIsZero))
          (solve
            ( Fold.two
            ∷ R806.eighteen
            ∷ Mself
            ∷ R806.thirtySix
            ∷ Ecomm
            ∷ Qsep
            ∷ [])))

    twoCurrencyBalanceImpliesSeparatedCancellation :
      Qsep
      ≡
      R806.eighteen * Mself
        + R806.thirtySix * Ecomm →
      Dsep ≡ 0ℚ
    twoCurrencyBalanceImpliesSeparatedCancellation balance =
      trans
        separatedTwoCurrencyNormalForm
        (trans
          (cong
            (Fold.two *_)
            (cong
              ( R806.eighteen * Mself
              + R806.thirtySix * Ecomm
              -_)
              balance))
          (solve
            ( Fold.two
            ∷ R806.eighteen
            ∷ Mself
            ∷ R806.thirtySix
            ∷ Ecomm
            ∷ [])))

    separatedCancellationImpliesTwoCurrencyBalance :
      Dsep ≡ 0ℚ →
      Qsep
      ≡
      R806.eighteen * Mself
        + R806.thirtySix * Ecomm
    separatedCancellationImpliesTwoCurrencyBalance cancelled =
      let
        old =
          P.separatedCancellationImpliesMultiplierCommutatorBalance
            cancelled
      in
      trans
        old
        (trans
          (cong
            (λ pZero →
              R806.eighteen * Mself
              + R806.thirtySix * pZero
              + R806.thirtySix * Ecomm)
            pZeroIsZero)
          (solve
            ( R806.eighteen
            ∷ Mself
            ∷ R806.thirtySix
            ∷ Ecomm
            ∷ [])))

round810PZeroDefectEliminated : Bool
round810PZeroDefectEliminated = true

round810SeparatedResidualOnTwoPhysicalCurrencies : Bool
round810SeparatedResidualOnTwoPhysicalCurrencies = true

round810CancellationEquivalentToQSelfExternalBalance : Bool
round810CancellationEquivalentToQSelfExternalBalance = true

round810CanonicalZeroModeProvenanceStillRequired : Bool
round810CanonicalZeroModeProvenanceStillRequired = false

round810IntroducesEstimate : Bool
round810IntroducesEstimate = false

round810TwoCurrencyBalanceClosed : Bool
round810TwoCurrencyBalanceClosed = false

round810W2Closed : Bool
round810W2Closed = false

round810ClayPromotion : Bool
round810ClayPromotion = false

round810PZeroDefectEliminatedIsTrue :
  round810PZeroDefectEliminated ≡ true
round810PZeroDefectEliminatedIsTrue = refl

round810CanonicalZeroModeProvenanceStillRequiredIsFalse :
  round810CanonicalZeroModeProvenanceStillRequired ≡ false
round810CanonicalZeroModeProvenanceStillRequiredIsFalse = refl

round810IntroducesEstimateIsFalse :
  round810IntroducesEstimate ≡ false
round810IntroducesEstimateIsFalse = refl

round810TwoCurrencyBalanceClosedIsFalse :
  round810TwoCurrencyBalanceClosed ≡ false
round810TwoCurrencyBalanceClosedIsFalse = refl

round810W2ClosedIsFalse :
  round810W2Closed ≡ false
round810W2ClosedIsFalse = refl

round810ClayPromotionIsFalse :
  round810ClayPromotion ≡ false
round810ClayPromotionIsFalse = refl
