{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650FullySeparatedQOrbitAverageRound788Exact where

------------------------------------------------------------------------
-- ROUND788 / EXACT THREE-POSITION q-ORBIT AVERAGE OF THE SEPARATED RESIDUAL
--
-- R787 proves the fully-separated mask is qEnergyLeg-invariant, and corrected
-- R38 proves qEnergyLeg is a permutation of the complete physical enumeration.
-- Therefore the masked fold is unchanged by one or two q-shifts.
--
-- Define the local three-position orbit scalar
--
--   C(beta) = Dsep(beta) + Dsep(q beta) + Dsep(q^2 beta).
--
-- Then globally, exactly,
--
--   sum C = 3 * sum Dsep.
--
-- On every nonzero separated cell R786 identifies these three positions with
-- one LH, one HL and one HH profile.  Thus this is the exact signed carrier on
-- which a three-profile cancellation/payment theorem should be tested.
--
-- No estimate, norm or absolute value is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
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
import DASHI.Physics.Closure.NSTriadKNR650FullySeparatedThreeProfileResidualRound783Exact as R783
import DASHI.Physics.Closure.NSTriadKNR650CCTouchedQInvariantRound787Exact as R787

F : C3.RealField _
F = Rational.rationalRealField

module QOrbitAverage
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

  module Three = R783.ThreeProfileResidual
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Packet = Three.Packet

  module At
      (cutoff : Nat)
      (time : Time)
      (S : Packet.LivePhysicalPacketStructure D C cutoff) where

    module T = Three.At cutoff time S

    items : List Physical.PhysicalTriadIncidence
    items = T.T.P.items

    q1Cell : Physical.PhysicalTriadIncidence → ℚ
    q1Cell beta =
      T.T.fullySeparatedCell (Orbit.qEnergyLeg beta)

    q2Cell : Physical.PhysicalTriadIncidence → ℚ
    q2Cell beta =
      T.T.fullySeparatedCell
        (Orbit.qEnergyLeg (Orbit.qEnergyLeg beta))

    cycleCell : Physical.PhysicalTriadIncidence → ℚ
    cycleCell beta =
      T.T.fullySeparatedCell beta + q1Cell beta + q2Cell beta

    q1Fold : ℚ
    q1Fold = R38.foldPower q1Cell items

    q2Fold : ℚ
    q2Fold = R38.foldPower q2Cell items

    cycleFold : ℚ
    cycleFold = R38.foldPower cycleCell items

    foldQInvariant :
      (value : Physical.PhysicalTriadIncidence → ℚ) →
      R38.foldPower (λ beta → value (Orbit.qEnergyLeg beta)) items
      ≡ R38.foldPower value items
    foldQInvariant value =
      trans
        (sym (R38.foldMap value Orbit.qEnergyLeg items))
        (R38.foldPermutationInvariant value
          (R38.qEnergyLegEnumerationPermutation cutoff))

    q1FoldIsBase :
      q1Fold ≡ T.T.fullySeparatedFold
    q1FoldIsBase =
      foldQInvariant T.T.fullySeparatedCell

    q2FoldIsBase :
      q2Fold ≡ T.T.fullySeparatedFold
    q2FoldIsBase =
      trans
        (foldQInvariant q1Cell)
        q1FoldIsBase

    cycleFoldSplits :
      cycleFold
      ≡ T.T.fullySeparatedFold + q1Fold + q2Fold
    cycleFoldSplits =
      go items
      where
      go :
        (xs : List Physical.PhysicalTriadIncidence) →
        R38.foldPower cycleCell xs
        ≡
        R38.foldPower T.T.fullySeparatedCell xs
          + R38.foldPower q1Cell xs
          + R38.foldPower q2Cell xs
      go [] = refl
      go (beta ∷ rest) =
        trans
          (cong (cycleCell beta +_) (go rest))
          (solve
            ( T.T.fullySeparatedCell beta
            ∷ q1Cell beta
            ∷ q2Cell beta
            ∷ R38.foldPower T.T.fullySeparatedCell rest
            ∷ R38.foldPower q1Cell rest
            ∷ R38.foldPower q2Cell rest
            ∷ []))

    cycleFoldIsThreeSeparatedFold :
      cycleFold
      ≡ R744.three * T.T.fullySeparatedFold
    cycleFoldIsThreeSeparatedFold =
      trans
        cycleFoldSplits
        (trans
          (cong
            (λ selected →
              T.T.fullySeparatedFold + selected + q2Fold)
            q1FoldIsBase)
          (trans
            (cong
              (λ selected →
                T.T.fullySeparatedFold
                  + T.T.fullySeparatedFold
                  + selected)
              q2FoldIsBase)
            (solve
              (R744.three ∷ T.T.fullySeparatedFold ∷ []))))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round788SeparatedFoldQReindexInvariant : Bool
round788SeparatedFoldQReindexInvariant = true

round788ThreePositionOrbitAverageExact : Bool
round788ThreePositionOrbitAverageExact = true

round788CycleFoldIsThreeSeparatedFold : Bool
round788CycleFoldIsThreeSeparatedFold = true

round788UsesNoEstimate : Bool
round788UsesNoEstimate = true

round788CycleCancellationClosed : Bool
round788CycleCancellationClosed = false

round788W2Closed : Bool
round788W2Closed = false

round788ClayPromotion : Bool
round788ClayPromotion = false

round788SeparatedFoldQReindexInvariantIsTrue :
  round788SeparatedFoldQReindexInvariant ≡ true
round788SeparatedFoldQReindexInvariantIsTrue = refl

round788ThreePositionOrbitAverageExactIsTrue :
  round788ThreePositionOrbitAverageExact ≡ true
round788ThreePositionOrbitAverageExactIsTrue = refl

round788CycleFoldIsThreeSeparatedFoldIsTrue :
  round788CycleFoldIsThreeSeparatedFold ≡ true
round788CycleFoldIsThreeSeparatedFoldIsTrue = refl

round788UsesNoEstimateIsTrue :
  round788UsesNoEstimate ≡ true
round788UsesNoEstimateIsTrue = refl

round788CycleCancellationClosedIsFalse :
  round788CycleCancellationClosed ≡ false
round788CycleCancellationClosedIsFalse = refl

round788W2ClosedIsFalse :
  round788W2Closed ≡ false
round788W2ClosedIsFalse = refl

round788ClayPromotionIsFalse :
  round788ClayPromotion ≡ false
round788ClayPromotionIsFalse = refl
