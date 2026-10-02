{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SeparatedTwoCurrencyPhysicalWallRound808Exact where

------------------------------------------------------------------------
-- ROUND808 / ELIMINATE THE p=0 PROVENANCE BRANCH FROM R806
--
-- R806:
--
--   D_sep
--     = 2 [
--         18 M_self,sep
--         + 36 C_p=0,sep
--         + 36 C_ext,sep
--         - Q_sep
--       ].
--
-- R807 proves on the SAME physical system, using only zero-output resonance
-- plus all-mode transversality,
--
--   C_p=0,sep = 0.
--
-- Therefore exactly
--
--   D_sep
--     = 2 [
--         18 M_self,sep
--         + 36 C_ext,sep
--         - Q_sep
--       ],
--
-- and
--
--   D_sep = 0
--     <->
--   Q_sep = 18 M_self,sep + 36 C_ext,sep.
--
-- The separated W2 cancellation seam is now a TWO-CURRENCY physical balance:
--
--   * Q_sep: the literal dyadic ordered-pair q-quotient;
--   * M_self,sep: the literal R625 four-helicity selected-self multiplier work;
--   * C_ext,sep: the literal separated R599/R605 external-network work.
--
-- (The latter two are the two RHS currencies.)  No estimate is introduced.
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
import DASHI.Physics.Closure.NSTriadKNR650PZeroSelfDefectVanishesRound807Exact as R807

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
    R806.SeparatedPhysicalDefect
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

    module ZeroKill =
      R807.PZeroDefectVanishes
        P.physicalSystem
        P.helicalScalars
        P.projectorLaws
        P.halfCalibration
        P.transverse

    Dsep : ℚ
    Dsep = P.Dsep

    Qsep : ℚ
    Qsep = P.Qsep

    Mself : ℚ
    Mself = P.Mself

    External : ℚ
    External = P.External

    pZeroSameObject :
      P.PZero ≡ ZeroKill.Sep.globalPZeroSelfDefectWork
    pZeroSameObject = refl

    pZeroVanishes :
      P.PZero ≡ 0ℚ
    pZeroVanishes =
      trans
        pZeroSameObject
        ZeroKill.globalPZeroSelfDefectWorkIsZero

    separatedTwoCurrencyNormalForm :
      Dsep
      ≡
      Fold.two *
        ( R806.eighteen * Mself
        + R806.thirtySix * External
        - Qsep )
    separatedTwoCurrencyNormalForm =
      trans
        P.separatedPhysicalDefectNormalForm
        (trans
          (cong
            (λ pzero →
              Fold.two *
                ( R806.eighteen * Mself
                + R806.thirtySix * pzero
                + R806.thirtySix * External
                - Qsep ))
            pZeroVanishes)
          (solve
            ( Fold.two
            ∷ R806.eighteen
            ∷ R806.thirtySix
            ∷ Mself
            ∷ External
            ∷ Qsep
            ∷ [])))

    twoCurrencyBalanceImpliesSeparatedCancellation :
      Qsep
      ≡ R806.eighteen * Mself
        + R806.thirtySix * External →
      Dsep ≡ 0ℚ
    twoCurrencyBalanceImpliesSeparatedCancellation balance =
      trans
        separatedTwoCurrencyNormalForm
        (trans
          (cong
            (Fold.two *_)
            (cong
              ( R806.eighteen * Mself
              + R806.thirtySix * External
              -_)
              balance))
          (solve
            ( Fold.two
            ∷ R806.eighteen
            ∷ R806.thirtySix
            ∷ Mself
            ∷ External
            ∷ [])))

    separatedCancellationImpliesTwoCurrencyBalance :
      Dsep ≡ 0ℚ →
      Qsep
      ≡ R806.eighteen * Mself
        + R806.thirtySix * External
    separatedCancellationImpliesTwoCurrencyBalance cancelled =
      trans
        (P.separatedCancellationImpliesPhysicalBalance cancelled)
        (trans
          (cong
            (λ pzero →
              R806.eighteen * Mself
                + R806.thirtySix * pzero
                + R806.thirtySix * External)
            pZeroVanishes)
          (solve
            ( R806.eighteen
            ∷ R806.thirtySix
            ∷ Mself
            ∷ External
            ∷ [])))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round808PZeroDefectEliminatedExactly : Bool
round808PZeroDefectEliminatedExactly = true

round808SeparatedWallIsTwoCurrencyPhysicalBalance : Bool
round808SeparatedWallIsTwoCurrencyPhysicalBalance = true

round808CancellationEquivalentToQEquals18MPlus36External : Bool
round808CancellationEquivalentToQEquals18MPlus36External = true

round808IntroducesEstimate : Bool
round808IntroducesEstimate = false

round808ExternalNetworkBalanceClosed : Bool
round808ExternalNetworkBalanceClosed = false

round808W2Closed : Bool
round808W2Closed = false

round808ClayPromotion : Bool
round808ClayPromotion = false

round808PZeroDefectEliminatedExactlyIsTrue :
  round808PZeroDefectEliminatedExactly ≡ true
round808PZeroDefectEliminatedExactlyIsTrue = refl

round808SeparatedWallIsTwoCurrencyPhysicalBalanceIsTrue :
  round808SeparatedWallIsTwoCurrencyPhysicalBalance ≡ true
round808SeparatedWallIsTwoCurrencyPhysicalBalanceIsTrue = refl

round808CancellationEquivalentToQEquals18MPlus36ExternalIsTrue :
  round808CancellationEquivalentToQEquals18MPlus36External ≡ true
round808CancellationEquivalentToQEquals18MPlus36ExternalIsTrue = refl

round808IntroducesEstimateIsFalse :
  round808IntroducesEstimate ≡ false
round808IntroducesEstimateIsFalse = refl

round808ExternalNetworkBalanceClosedIsFalse :
  round808ExternalNetworkBalanceClosed ≡ false
round808ExternalNetworkBalanceClosedIsFalse = refl

round808W2ClosedIsFalse :
  round808W2Closed ≡ false
round808W2ClosedIsFalse = refl

round808ClayPromotionIsFalse :
  round808ClayPromotion ≡ false
round808ClayPromotionIsFalse = refl
