{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SeparatedMultiplierCommutatorWallRound808Exact where

------------------------------------------------------------------------
-- ROUND808 / THE SEPARATED PHYSICAL WALL IS NOW MULTIPLIER + EXTERNAL
--            COMMUTATOR + THE EXPLICIT p=0 PROVENANCE BRANCH
--
-- R806 gives exactly
--
--   D_sep
--     = 2 [
--         18 M_self
--       + 36 PZero
--       + 36 External
--       - Q_sep ].
--
-- R807 identifies that SAME separated external work with coherent work against
-- the literal R670 weighted external COMMUTATOR fold:
--
--   External = E_comm.
--
-- Therefore
--
--   D_sep
--     = 2 [
--         18 M_self
--       + 36 PZero
--       + 36 E_comm
--       - Q_sep ],
--
-- and cancellation is equivalent to
--
--   Q_sep = 18 M_self + 36 PZero + 36 E_comm.
--
-- At this point every non-provenance term is on an existing signed physical
-- carrier:
--
--   Q_sep   : dyadic orderedPairPower q-quotient,
--   M_self  : R625 four-helicity multiplier-difference work,
--   E_comm  : R670 separated external commutator work.
--
-- The only deliberately noncanonical branch still visible is PZero, inherited
-- from the fact that a generic PhysicalFiniteComplex3GalerkinSystem does not
-- by itself force the off-support velocity lookup at zeroMode to be zero.
--
-- No estimate, norm, absolute value, or foreign-carrier identification enters.
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
import DASHI.Physics.Closure.NSTriadKNR650SeparatedExternalCommutatorRound807Exact as R807

F : C3.RealField _
F = Rational.rationalRealField

module SeparatedMultiplierCommutatorWall
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

    module Ext =
      R807.SeparatedExternalCommutator
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

    PZero : ℚ
    PZero = P.PZero

    Ecomm : ℚ
    Ecomm = Ext.globalExternalCommutatorWork

    externalSamePhysicalCurrency :
      P.External ≡ Ecomm
    externalSamePhysicalCurrency =
      Ext.globalExternalWorkIsCommutatorWork

    separatedMultiplierCommutatorNormalForm :
      Dsep
      ≡
      Fold.two *
        ( R806.eighteen * Mself
        + R806.thirtySix * PZero
        + R806.thirtySix * Ecomm
        - Qsep )
    separatedMultiplierCommutatorNormalForm =
      trans
        P.separatedPhysicalDefectNormalForm
        (cong
          (Fold.two *_)
          (cong
            (λ external →
              R806.eighteen * Mself
              + R806.thirtySix * PZero
              + R806.thirtySix * external
              - Qsep)
            externalSamePhysicalCurrency))

    multiplierCommutatorBalanceImpliesSeparatedCancellation :
      Qsep
      ≡
      R806.eighteen * Mself
        + R806.thirtySix * PZero
        + R806.thirtySix * Ecomm →
      Dsep ≡ 0ℚ
    multiplierCommutatorBalanceImpliesSeparatedCancellation balance =
      trans
        separatedMultiplierCommutatorNormalForm
        (trans
          (cong
            (Fold.two *_)
            (cong
              ( R806.eighteen * Mself
              + R806.thirtySix * PZero
              + R806.thirtySix * Ecomm
              -_)
              balance))
          (solve
            ( Fold.two
            ∷ R806.eighteen
            ∷ Mself
            ∷ R806.thirtySix
            ∷ PZero
            ∷ Ecomm
            ∷ [])))

    separatedCancellationImpliesMultiplierCommutatorBalance :
      Dsep ≡ 0ℚ →
      Qsep
      ≡
      R806.eighteen * Mself
        + R806.thirtySix * PZero
        + R806.thirtySix * Ecomm
    separatedCancellationImpliesMultiplierCommutatorBalance cancelled =
      trans
        (P.separatedCancellationImpliesPhysicalBalance cancelled)
        (cong
          (λ external →
            R806.eighteen * Mself
              + R806.thirtySix * PZero
              + R806.thirtySix * external)
          externalSamePhysicalCurrency)

round808ExternalR230ProductRulePlaceholderEliminated : Bool
round808ExternalR230ProductRulePlaceholderEliminated = true

round808NonProvenanceTermsOnMultiplierAndCommutatorCarriers : Bool
round808NonProvenanceTermsOnMultiplierAndCommutatorCarriers = true

round808PZeroProvenanceBranchStillExplicit : Bool
round808PZeroProvenanceBranchStillExplicit = true

round808CancellationEquivalentToMultiplierCommutatorBalance : Bool
round808CancellationEquivalentToMultiplierCommutatorBalance = true

round808IntroducesEstimate : Bool
round808IntroducesEstimate = false

round808PZeroDefectClosed : Bool
round808PZeroDefectClosed = false

round808MultiplierCommutatorBalanceClosed : Bool
round808MultiplierCommutatorBalanceClosed = false

round808W2Closed : Bool
round808W2Closed = false

round808ClayPromotion : Bool
round808ClayPromotion = false

round808ExternalR230ProductRulePlaceholderEliminatedIsTrue :
  round808ExternalR230ProductRulePlaceholderEliminated ≡ true
round808ExternalR230ProductRulePlaceholderEliminatedIsTrue = refl

round808NonProvenanceTermsOnMultiplierAndCommutatorCarriersIsTrue :
  round808NonProvenanceTermsOnMultiplierAndCommutatorCarriers ≡ true
round808NonProvenanceTermsOnMultiplierAndCommutatorCarriersIsTrue = refl

round808PZeroProvenanceBranchStillExplicitIsTrue :
  round808PZeroProvenanceBranchStillExplicit ≡ true
round808PZeroProvenanceBranchStillExplicitIsTrue = refl

round808CancellationEquivalentToMultiplierCommutatorBalanceIsTrue :
  round808CancellationEquivalentToMultiplierCommutatorBalance ≡ true
round808CancellationEquivalentToMultiplierCommutatorBalanceIsTrue = refl

round808IntroducesEstimateIsFalse :
  round808IntroducesEstimate ≡ false
round808IntroducesEstimateIsFalse = refl

round808PZeroDefectClosedIsFalse :
  round808PZeroDefectClosed ≡ false
round808PZeroDefectClosedIsFalse = refl

round808MultiplierCommutatorBalanceClosedIsFalse :
  round808MultiplierCommutatorBalanceClosed ≡ false
round808MultiplierCommutatorBalanceClosedIsFalse = refl

round808W2ClosedIsFalse :
  round808W2Closed ≡ false
round808W2ClosedIsFalse = refl

round808ClayPromotionIsFalse :
  round808ClayPromotion ≡ false
round808ClayPromotionIsFalse = refl
