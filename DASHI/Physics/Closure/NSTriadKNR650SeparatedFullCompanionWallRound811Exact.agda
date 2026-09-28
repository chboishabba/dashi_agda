{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SeparatedFullCompanionWallRound811Exact where

------------------------------------------------------------------------
-- ROUND811 / DIRECT SI-STYLE COLLAPSE TO ONE FULL SEPARATED R438 COMPANION
--
-- R801 gives the exact physical normal form
--
--   D_sep = 2 (36 C_sep - Q_sep),
--
-- where C_sep is coherent work against the fully-separated weighted R230
-- commutator fold.
--
-- R438 already proves, on an arbitrary swap-invariant R294 weight and with the
-- p=0 branch handled internally,
--
--   2 * weighted R230 commutator fold
--     = exhaustive weighted forcing-slot companion fold.
--
-- Specialize R438 to R798's literal fully-separated 0/1 weight.  After the
-- same output-zero selection used by R800 and coherent-work linearity:
--
--   F_sep = 2 C_sep,
--
-- where F_sep is the global coherent work against the literal exhaustive R438
-- separated companion.
--
-- Therefore exactly
--
--   D_sep = 2 (18 F_sep - Q_sep),
--
-- and
--
--   D_sep = 0  <->  Q_sep = 18 F_sep.
--
-- This is strictly shorter than the R802--R810 self/external decomposition.
-- Those owners remain useful provenance/decomposition receipts, but no longer
-- lie on the preferred exact separated-wall path.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
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
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNWeightedProjectedForcingOuterFoldRound438Exact as R438
import DASHI.Physics.Closure.NSTriadKNR650SeparatedR230WeightRound798Exact as R798
import DASHI.Physics.Closure.NSTriadKNR650SeparatedQuotientR230BalanceRound801Exact as R801
import DASHI.Physics.Closure.NSTriadKNR650SeparatedPhysicalDefectNormalFormRound806Exact as R806

F : C3.RealField _
F = Rational.rationalRealField

module SeparatedFullCompanionWall
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

  module Base =
    R801.SeparatedR230Balance
      Time initialTime integrateTo
      VectorDerivativeOf ScalarDerivativeOf
      projectedCross vectorAlgebra zeroCalculus
      hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
      FTC integrationLinearity integrationTransport D C R

  module Packet = Base.Packet

  module At
      (cutoff : Nat)
      (time : Time)
      (S : Packet.LivePhysicalPacketStructure D C cutoff) where

    module B = Base.At cutoff time S
    module Id = B.PhysicalId.Id

    physicalSystem = B.Live.P.Base.Base.NestedAt.physicalSystem
    system = Field30.finiteSystem physicalSystem

    helicalScalars =
      Base.Wall.Prev.Prev.Residual.Average.Three.Two.Paired.Local.O.Combined.Nested.S

    transverse = B.Live.P.Base.Base.NestedAt.allModeTransverse

    W = R798.separatedWeight F

    Dsep : ℚ
    Dsep = B.Dsep

    Qsep : ℚ
    Qsep = B.Qsep

    Csep : ℚ
    Csep = B.Csep

    companionFold :
      Z3.FourierMode → C3.Complex3 F
    companionFold output =
      R438.foldExhaustiveWeightedCompanion
        W helicalScalars system
        (Output.physicalOutputFiber cutoff output)

    doubleCommutatorFoldIsCompanion :
      (output : Z3.FourierMode) →
      C3.complex3Add
        (Id.commutatorFold output)
        (Id.commutatorFold output)
      ≡ companionFold output
    doubleCommutatorFoldIsCompanion output =
      let
        fibre = Output.physicalOutputFiber cutoff output
        weighted =
          R438.weightedProjectedForcingCell
            W helicalScalars system
      in
      trans
        (sym (R230.foldAdd weighted weighted fibre))
        (R438.fixedOutputDoubleWeightedR294FoldIsQuadraticCompanion
          W system transverse output)

    outputCompanionWork : Z3.FourierMode → ℚ
    outputCompanionWork output
      with Output.modeEqual output Z3.zeroMode
    ... | true = 0ℚ
    ... | false =
      Work.coherentWork
        (Id.mixedFold output)
        (companionFold output)

    outputCompanionWorkIsDoubleCommutatorWork :
      (output : Z3.FourierMode) →
      outputCompanionWork output
      ≡ Fold.two * B.PhysicalId.outputCommutatorWork output
    outputCompanionWorkIsDoubleCommutatorWork output
      with Output.modeEqual output Z3.zeroMode
    ... | true = solve (Fold.two ∷ [])
    ... | false =
      trans
        (cong
          (Work.coherentWork (Id.mixedFold output))
          (sym (doubleCommutatorFoldIsCompanion output)))
        (trans
          (Work.workAddRight
            (Id.mixedFold output)
            (Id.commutatorFold output)
            (Id.commutatorFold output))
          (solve
            ( Fold.two
            ∷ Work.coherentWork
                (Id.mixedFold output)
                (Id.commutatorFold output)
            ∷ [])))

    sumCompanionWork : List Z3.FourierMode → ℚ
    sumCompanionWork [] = 0ℚ
    sumCompanionWork (output ∷ rest) =
      outputCompanionWork output + sumCompanionWork rest

    globalCompanionWork : ℚ
    globalCompanionWork =
      sumCompanionWork (Cube.cutoffModes cutoff)

    sumCompanionWorkIsDoubleCommutatorWork :
      (outputs : List Z3.FourierMode) →
      sumCompanionWork outputs
      ≡
      Fold.two * B.PhysicalId.sumOutputCommutatorWork outputs
    sumCompanionWorkIsDoubleCommutatorWork [] =
      solve (Fold.two ∷ [])
    sumCompanionWorkIsDoubleCommutatorWork (output ∷ rest) =
      trans
        (cong
          (outputCompanionWork output +_)
          (sumCompanionWorkIsDoubleCommutatorWork rest))
        (trans
          (cong
            (_+ Fold.two * B.PhysicalId.sumOutputCommutatorWork rest)
            (outputCompanionWorkIsDoubleCommutatorWork output))
          (solve
            ( Fold.two
            ∷ B.PhysicalId.outputCommutatorWork output
            ∷ B.PhysicalId.sumOutputCommutatorWork rest
            ∷ [])))

    globalCompanionWorkIsDoubleCsep :
      globalCompanionWork ≡ Fold.two * Csep
    globalCompanionWorkIsDoubleCsep =
      sumCompanionWorkIsDoubleCommutatorWork
        (Cube.cutoffModes cutoff)

    eighteenCompanionIsThirtySixCsep :
      R806.eighteen * globalCompanionWork
      ≡ R806.thirtySix * Csep
    eighteenCompanionIsThirtySixCsep =
      trans
        (cong (R806.eighteen *_) globalCompanionWorkIsDoubleCsep)
        (solve
          ( R806.eighteen
          ∷ Fold.two
          ∷ R806.thirtySix
          ∷ Csep
          ∷ []))

    separatedFullCompanionNormalForm :
      Dsep
      ≡
      Fold.two *
        (R806.eighteen * globalCompanionWork - Qsep)
    separatedFullCompanionNormalForm =
      trans
        B.separatedR230FactorTwoNormalForm
        (cong
          (Fold.two *_)
          (cong
            (_- Qsep)
            (sym eighteenCompanionIsThirtySixCsep)))

    fullCompanionBalanceImpliesSeparatedCancellation :
      Qsep ≡ R806.eighteen * globalCompanionWork →
      Dsep ≡ 0ℚ
    fullCompanionBalanceImpliesSeparatedCancellation balance =
      trans
        separatedFullCompanionNormalForm
        (trans
          (cong
            (Fold.two *_)
            (cong
              (R806.eighteen * globalCompanionWork -_)
              balance))
          (solve
            ( Fold.two
            ∷ R806.eighteen
            ∷ globalCompanionWork
            ∷ [])))

    separatedCancellationImpliesFullCompanionBalance :
      Dsep ≡ 0ℚ →
      Qsep ≡ R806.eighteen * globalCompanionWork
    separatedCancellationImpliesFullCompanionBalance cancelled =
      trans
        (B.separatedCancellationImpliesR230Balance cancelled)
        (sym eighteenCompanionIsThirtySixCsep)

round811R438DirectSameObjectCollapseClosed : Bool
round811R438DirectSameObjectCollapseClosed = true

round811GlobalCompanionWorkIsDoubleR230Work : Bool
round811GlobalCompanionWorkIsDoubleR230Work = true

round811SeparatedResidualIs2Times18CompanionMinusQ : Bool
round811SeparatedResidualIs2Times18CompanionMinusQ = true

round811CancellationEquivalentToQEquals18FullCompanion : Bool
round811CancellationEquivalentToQEquals18FullCompanion = true

round811SelfExternalDecompositionRequiredOnPreferredPath : Bool
round811SelfExternalDecompositionRequiredOnPreferredPath = false

round811IntroducesEstimate : Bool
round811IntroducesEstimate = false

round811FullCompanionBalanceClosed : Bool
round811FullCompanionBalanceClosed = false

round811W2Closed : Bool
round811W2Closed = false

round811ClayPromotion : Bool
round811ClayPromotion = false

round811R438DirectSameObjectCollapseClosedIsTrue :
  round811R438DirectSameObjectCollapseClosed ≡ true
round811R438DirectSameObjectCollapseClosedIsTrue = refl

round811SelfExternalDecompositionRequiredOnPreferredPathIsFalse :
  round811SelfExternalDecompositionRequiredOnPreferredPath ≡ false
round811SelfExternalDecompositionRequiredOnPreferredPathIsFalse = refl

round811IntroducesEstimateIsFalse :
  round811IntroducesEstimate ≡ false
round811IntroducesEstimateIsFalse = refl

round811FullCompanionBalanceClosedIsFalse :
  round811FullCompanionBalanceClosed ≡ false
round811FullCompanionBalanceClosedIsFalse = refl

round811W2ClosedIsFalse :
  round811W2Closed ≡ false
round811W2ClosedIsFalse = refl

round811ClayPromotionIsFalse :
  round811ClayPromotion ≡ false
round811ClayPromotionIsFalse = refl
