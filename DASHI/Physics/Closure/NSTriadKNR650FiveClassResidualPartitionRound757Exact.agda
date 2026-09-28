{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650FiveClassResidualPartitionRound757Exact where

------------------------------------------------------------------------
-- ROUND757 / PARTITION THE ACTUAL R749 W2 NONLINEAR RESIDUAL BY THE
--            EXISTING TOTAL R25 PHYSICAL TRIAD CLASSIFIER
--
-- R749 has already put the nonlinear W2 residual on one local outer-incidence
-- cell:
--
--   D(beta) = 3 * NestedOrbit(beta) - PairedTwoDifference(beta).
--
-- Round25 already proves a total/unique physical triad classifier
--
--   LH / HL / HH / CC
--
-- and Round25Sum proves exact finite accounting for an arbitrary rational
-- triad functional.  Apply that existing theorem directly to D.
--
-- Thus, pointwise in time and cutoff,
--
--   sum_beta D(beta)
--     = D_LH + D_HL + D_CC + D_HH,
--
-- and the full R749 residual is exactly
--
--   D_LH + D_HL + D_CC + D_HH
--     + 3 (2 nu - delta) d_N.
--
-- No classwise estimate, sign, norm, absolute value, or dissipation allocation
-- is introduced.  This owner only exposes the four exact analytic channels
-- on the already-canonical R751 residual.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNLuoFiniteBonyFourClassAccountingExact as Four
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as R25
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSumRound25Exact as R25Sum
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
import DASHI.Physics.Closure.NSTriadKNR650CriticalProductionIncidenceCarrierRound744Exact as R744
import DASHI.Physics.Closure.NSTriadKNR650DyadicDifferenceAlignedW2Round749Exact as R749

F : C3.RealField _
F = Rational.rationalRealField

foldPowerIsTriadValueSum :
  (value : Physical.PhysicalTriadIncidence → ℚ) →
  (items : List Physical.PhysicalTriadIncidence) →
  R38.foldPower value items ≡ R25Sum.triadValueSum value items
foldPowerIsTriadValueSum value [] = refl
foldPowerIsTriadValueSum value (tau ∷ rest) =
  cong (value tau +_) (foldPowerIsTriadValueSum value rest)

module FiveClassResidual
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

  module Local = R749.DifferenceAligned
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Packet = Local.Packet

  module At
      (cutoff : Nat)
      (time : Time)
      (S : Packet.LivePhysicalPacketStructure D C cutoff) where

    module Base = Local.At cutoff time S

    items : List Physical.PhysicalTriadIncidence
    items = Physical.physicalTriadEnumeration cutoff

    taggedResidual :
      List Four.TaggedInteraction
    taggedResidual =
      R25Sum.tagClassifiedTriads
        Base.differenceAlignedCell
        (R25.classifyPhysicalTriads items)

    lowHighResidual : ℚ
    lowHighResidual =
      Four.lowHighSum taggedResidual

    highLowResidual : ℚ
    highLowResidual =
      Four.highLowSum taggedResidual

    comparableResidual : ℚ
    comparableResidual =
      Four.comparableSum taggedResidual

    highHighResidual : ℚ
    highHighResidual =
      Four.highHighToLowSum taggedResidual

    nonlinearResidualIsFourClassSum :
      Base.differenceAlignedFold
      ≡
      lowHighResidual
        + highLowResidual
        + comparableResidual
        + highHighResidual
    nonlinearResidualIsFourClassSum =
      trans
        (foldPowerIsTriadValueSum Base.differenceAlignedCell items)
        (trans
          (sym
            (R25Sum.physicalClassificationPreservesTotal
              Base.differenceAlignedCell items))
          (Four.fourClassPartitionExact taggedResidual))

    classResolvedResidual :
      ℚ → ℚ
    classResolvedResidual margin =
      lowHighResidual
        + highLowResidual
        + comparableResidual
        + highHighResidual
        + R744.three
            * Base.Base.retainedCoefficient margin
            * Local.O.W2.K.dissipationAt cutoff time

    classResolvedResidualIsR749 :
      (margin : ℚ) →
      classResolvedResidual margin
      ≡ Base.differenceAlignedResidual margin
    classResolvedResidualIsR749 margin =
      trans
        (cong
          (λ nonlinear →
            nonlinear
              + R744.three
                  * Base.Base.retainedCoefficient margin
                  * Local.O.W2.K.dissipationAt cutoff time)
          (sym nonlinearResidualIsFourClassSum))
        (solve
          ( Base.differenceAlignedFold
          ∷ R744.three
          ∷ Base.Base.retainedCoefficient margin
          ∷ Local.O.W2.K.dissipationAt cutoff time
          ∷ []))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round757ActualR749ResidualPartitionedByR25 : Bool
round757ActualR749ResidualPartitionedByR25 = true

round757ExactlyFourTriadicAnalyticChannels : Bool
round757ExactlyFourTriadicAnalyticChannels = true

round757ClassPartitionIntroducesEstimate : Bool
round757ClassPartitionIntroducesEstimate = false

round757ClasswiseSignsKnown : Bool
round757ClasswiseSignsKnown = false

round757DissipationAllocatedClasswise : Bool
round757DissipationAllocatedClasswise = false

round757ResidualNonnegativeClosed : Bool
round757ResidualNonnegativeClosed = false

round757ClayPromotion : Bool
round757ClayPromotion = false

round757ActualR749ResidualPartitionedByR25IsTrue :
  round757ActualR749ResidualPartitionedByR25 ≡ true
round757ActualR749ResidualPartitionedByR25IsTrue = refl

round757ExactlyFourTriadicAnalyticChannelsIsTrue :
  round757ExactlyFourTriadicAnalyticChannels ≡ true
round757ExactlyFourTriadicAnalyticChannelsIsTrue = refl

round757ClassPartitionIntroducesEstimateIsFalse :
  round757ClassPartitionIntroducesEstimate ≡ false
round757ClassPartitionIntroducesEstimateIsFalse = refl

round757ClasswiseSignsKnownIsFalse :
  round757ClasswiseSignsKnown ≡ false
round757ClasswiseSignsKnownIsFalse = refl

round757DissipationAllocatedClasswiseIsFalse :
  round757DissipationAllocatedClasswise ≡ false
round757DissipationAllocatedClasswiseIsFalse = refl

round757ResidualNonnegativeClosedIsFalse :
  round757ResidualNonnegativeClosed ≡ false
round757ResidualNonnegativeClosedIsFalse = refl

round757ClayPromotionIsFalse :
  round757ClayPromotion ≡ false
round757ClayPromotionIsFalse = refl
