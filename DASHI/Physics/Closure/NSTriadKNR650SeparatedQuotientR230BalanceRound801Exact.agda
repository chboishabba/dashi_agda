{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SeparatedQuotientR230BalanceRound801Exact where

------------------------------------------------------------------------
-- ROUND801 / REPLACE THE ABSTRACT B_sep BALANCE BY A LITERAL R230 WORK BALANCE
--
-- R797:
--
--   D_sep = 9 B_sep - 2 Q_sep.
--
-- R800, instantiated on the SAME live R793 physical system:
--
--   B_sep = 8 C_sep,
--
-- where C_sep is the zero-output-safe sum over literal output modes of
--
--   W(M_k, masked-R230-commutator_k).
--
-- Therefore exactly
--
--   D_sep = 72 C_sep - 2 Q_sep
--         = 2 (36 C_sep - Q_sep),
--
-- and hence
--
--   D_sep = 0  <->  Q_sep = 36 C_sep.
--
-- The old product-rule spectator abstraction has therefore been eliminated
-- from the separated cancellation seam.  What remains is a direct comparison
-- between:
--
--   * the dyadic ordered-pair q-quotient Q_sep, and
--   * a literal masked R230 coherent-commutator work C_sep.
--
-- No estimate, norm, absolute value, or foreign-carrier identification enters.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; _/_; _-_; _*_)
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
import DASHI.Physics.Closure.NSTriadKNR650SeparatedQuotientBalanceWallRound797Exact as R797
import DASHI.Physics.Closure.NSTriadKNR650SeparatedPairedBaseCommutatorRound799Exact as R799
import DASHI.Physics.Closure.NSTriadKNR650SeparatedBaseGlobalCommutatorRound800Exact as R800

F : C3.RealField _
F = Rational.rationalRealField

thirtySix seventyTwo oneHalf : ℚ
thirtySix = 36
seventyTwo = 72
oneHalf = + 1 / 2

module SeparatedR230Balance
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

  module Wall = R797.SeparatedBalanceWall
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Packet = Wall.Packet

  module At
      (cutoff : Nat)
      (time : Time)
      (S : Packet.LivePhysicalPacketStructure D C cutoff) where

    module W = Wall.At cutoff time S
    module P = W.P
    module Live = P.P

    module PhysicalId =
      R800.GlobalSeparatedBaseCommutator
        Live.P.Base.Base.NestedAt.physicalSystem
        Wall.Prev.Prev.Residual.Average.Three.Two.Paired.Local.O.Combined.Nested.S
        Wall.Prev.Prev.Residual.Average.Three.Two.Paired.Local.O.Combined.Nested.L
        Wall.Prev.Prev.Residual.Average.Three.Two.Paired.Local.O.Combined.Nested.H
        Live.P.Base.Base.NestedAt.allModeTransverse

    Dsep : ℚ
    Dsep = W.Dsep

    Bsep : ℚ
    Bsep = W.Bsep

    Qsep : ℚ
    Qsep = W.Qsep

    Csep : ℚ
    Csep = PhysicalId.globalSeparatedCommutatorWork

    baseFoldSameObject :
      Bsep ≡ PhysicalId.separatedBaseFold
    baseFoldSameObject = refl

    baseFoldIsEightR230Work :
      Bsep ≡ R799.eight * Csep
    baseFoldIsEightR230Work =
      trans
        baseFoldSameObject
        PhysicalId.separatedBaseIsEightGlobalCommutatorWork

    separatedR230NormalForm :
      Dsep ≡ seventyTwo * Csep - Fold.two * Qsep
    separatedR230NormalForm =
      trans
        W.separatedNormalForm
        (trans
          (cong
            (λ base → W.nine * base - Fold.two * Qsep)
            baseFoldIsEightR230Work)
          (solve
            ( W.nine
            ∷ R799.eight
            ∷ seventyTwo
            ∷ Csep
            ∷ Fold.two
            ∷ Qsep
            ∷ [])))

    separatedR230FactorTwoNormalForm :
      Dsep ≡ Fold.two * (thirtySix * Csep - Qsep)
    separatedR230FactorTwoNormalForm =
      trans
        separatedR230NormalForm
        (solve
          ( seventyTwo
          ∷ Fold.two
          ∷ thirtySix
          ∷ Csep
          ∷ Qsep
          ∷ []))

    r230BalanceImpliesSeparatedCancellation :
      Qsep ≡ thirtySix * Csep →
      Dsep ≡ 0ℚ
    r230BalanceImpliesSeparatedCancellation balance =
      trans
        separatedR230FactorTwoNormalForm
        (trans
          (cong
            (Fold.two *_)
            (cong (thirtySix * Csep -_) balance))
          (solve (Fold.two ∷ thirtySix ∷ Csep ∷ [])))

    separatedCancellationImpliesR230Balance :
      Dsep ≡ 0ℚ →
      Qsep ≡ thirtySix * Csep
    separatedCancellationImpliesR230Balance cancelled =
      let
        oldBalance :
          Fold.two * Qsep ≡ W.nine * Bsep
        oldBalance =
          W.separatedCancellationImpliesQuotientBalance cancelled

        expanded :
          Fold.two * Qsep
          ≡ W.nine * (R799.eight * Csep)
        expanded =
          trans
            oldBalance
            (cong (W.nine *_) baseFoldIsEightR230Work)

        scaled =
          cong (oneHalf *_) expanded

        leftMeaning :
          oneHalf * (Fold.two * Qsep) ≡ Qsep
        leftMeaning =
          solve (Fold.two ∷ oneHalf ∷ Qsep ∷ [])

        rightMeaning :
          oneHalf * (W.nine * (R799.eight * Csep))
          ≡ thirtySix * Csep
        rightMeaning =
          solve
            ( oneHalf
            ∷ W.nine
            ∷ R799.eight
            ∷ thirtySix
            ∷ Csep
            ∷ [])
      in
      trans
        (sym leftMeaning)
        (trans scaled rightMeaning)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round801AbstractBsepEliminatedFromPhysicalWall : Bool
round801AbstractBsepEliminatedFromPhysicalWall = true

round801SeparatedResidualIs72R230Minus2Q : Bool
round801SeparatedResidualIs72R230Minus2Q = true

round801CancellationEquivalentToQEquals36R230Work : Bool
round801CancellationEquivalentToQEquals36R230Work = true

round801IntroducesEstimate : Bool
round801IntroducesEstimate = false

round801R230QuotientBalanceClosed : Bool
round801R230QuotientBalanceClosed = false

round801W2Closed : Bool
round801W2Closed = false

round801ClayPromotion : Bool
round801ClayPromotion = false

round801AbstractBsepEliminatedFromPhysicalWallIsTrue :
  round801AbstractBsepEliminatedFromPhysicalWall ≡ true
round801AbstractBsepEliminatedFromPhysicalWallIsTrue = refl

round801SeparatedResidualIs72R230Minus2QIsTrue :
  round801SeparatedResidualIs72R230Minus2Q ≡ true
round801SeparatedResidualIs72R230Minus2QIsTrue = refl

round801CancellationEquivalentToQEquals36R230WorkIsTrue :
  round801CancellationEquivalentToQEquals36R230Work ≡ true
round801CancellationEquivalentToQEquals36R230WorkIsTrue = refl

round801IntroducesEstimateIsFalse :
  round801IntroducesEstimate ≡ false
round801IntroducesEstimateIsFalse = refl

round801R230QuotientBalanceClosedIsFalse :
  round801R230QuotientBalanceClosed ≡ false
round801R230QuotientBalanceClosedIsFalse = refl

round801W2ClosedIsFalse :
  round801W2Closed ≡ false
round801W2ClosedIsFalse = refl

round801ClayPromotionIsFalse :
  round801ClayPromotion ≡ false
round801ClayPromotionIsFalse = refl
