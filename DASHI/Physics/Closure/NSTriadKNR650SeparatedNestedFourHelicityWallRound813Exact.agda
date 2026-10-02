{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SeparatedNestedFourHelicityWallRound813Exact where

------------------------------------------------------------------------
-- ROUND813 / THE PREFERRED SEPARATED WALL ON THE LIVE R573/R571
--            FOUR-HELICITY MULTIPLIER CARRIER
--
-- R811:
--
--   D_sep = 2 (18 F_sep - Q_sep),
--
-- with F_sep the global coherent work against the exhaustive separated R438
-- forcing-slot companion.
--
-- R812 specialises R573 to the SAME R798 separated mask before expansion and
-- proves on arbitrary physical incidence lists
--
--   NestedFourSignFold = 2 CompanionFold.
--
-- Push that identity through the same output-zero selection and coherent-work
-- aggregation used by R811:
--
--   N_sep = 2 F_sep.
--
-- Therefore
--
--   D_sep = 2 (9 N_sep - Q_sep),
--
-- and
--
--   D_sep = 0  <->  Q_sep = 9 N_sep.
--
-- N_sep is now literally coherent work against R573.nestedWeightedCompanionCell
-- with W = R798.separatedWeight.  Internally, each nonzero-p outer cell folds
-- R572.fourSignInner over the COMPLETE physical output fibre at p, and every
-- fourSignInner is the four exact R571 multiplier-difference vectors.
--
-- Thus the remaining wall is no longer "R438 companion vs q quotient".  It is
-- directly:
--
--   q-quotient orderedPairPower scalar
--       vs
--   masked nested four-helicity multiplier-difference slot work.
--
-- No norm, absolute value, self/external split, division, estimate, or new
-- helicity premise is introduced.
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
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
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
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNR650SeparatedPhysicalDefectNormalFormRound806Exact as R806
import DASHI.Physics.Closure.NSTriadKNR650SeparatedFullCompanionWallRound811Exact as R811
import DASHI.Physics.Closure.NSTriadKNR650SeparatedR438FourHelicityRound812Exact as R812

F : C3.RealField _
F = Rational.rationalRealField

nine : ℚ
nine = 9

module SeparatedNestedFourHelicityWall
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
    R811.SeparatedFullCompanionWall
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

    module Four =
      R812.SeparatedFourHelicity
        P.physicalSystem
        P.helicalScalars
        P.projectorLaws
        P.halfCalibration
        P.transverse

    Dsep : ℚ
    Dsep = P.Dsep

    Qsep : ℚ
    Qsep = P.Qsep

    Fsep : ℚ
    Fsep = P.globalCompanionWork

    nestedFold :
      Z3.FourierMode → C3.Complex3 F
    nestedFold output =
      Four.nestedFourHelicityFold
        (Output.physicalOutputFiber cutoff output)

    outputNestedWork : Z3.FourierMode → ℚ
    outputNestedWork output
      with Output.modeEqual output Z3.zeroMode
    ... | true = 0ℚ
    ... | false =
      Work.coherentWork
        (P.Id.mixedFold output)
        (nestedFold output)

    outputNestedWorkIsDoubleCompanionWork :
      (output : Z3.FourierMode) →
      outputNestedWork output
      ≡ Fold.two * P.outputCompanionWork output
    outputNestedWorkIsDoubleCompanionWork output
      with Output.modeEqual output Z3.zeroMode
    ... | true = solve (Fold.two ∷ [])
    ... | false =
      let
        items = Output.physicalOutputFiber cutoff output
        M = P.Id.mixedFold output
        Cfold = P.companionFold output
        Nfold = nestedFold output

        doubleFold :
          C3.complex3Add Cfold Cfold ≡ Nfold
        doubleFold =
          Four.doubleCompanionFoldIsNested items
      in
      trans
        (cong
          (Work.coherentWork M)
          (sym doubleFold))
        (trans
          (Work.workAddRight M Cfold Cfold)
          (solve
            ( Fold.two
            ∷ Work.coherentWork M Cfold
            ∷ [])))

    sumNestedWork : List Z3.FourierMode → ℚ
    sumNestedWork [] = 0ℚ
    sumNestedWork (output ∷ rest) =
      outputNestedWork output + sumNestedWork rest

    globalNestedFourHelicityWork : ℚ
    globalNestedFourHelicityWork =
      sumNestedWork (Cube.cutoffModes cutoff)

    sumNestedWorkIsDoubleCompanion :
      (outputs : List Z3.FourierMode) →
      sumNestedWork outputs
      ≡ Fold.two * P.sumCompanionWork outputs
    sumNestedWorkIsDoubleCompanion [] =
      solve (Fold.two ∷ [])
    sumNestedWorkIsDoubleCompanion (output ∷ rest) =
      trans
        (cong
          (outputNestedWork output +_)
          (sumNestedWorkIsDoubleCompanion rest))
        (trans
          (cong
            (_+ Fold.two * P.sumCompanionWork rest)
            (outputNestedWorkIsDoubleCompanionWork output))
          (solve
            ( Fold.two
            ∷ P.outputCompanionWork output
            ∷ P.sumCompanionWork rest
            ∷ [])))

    globalNestedWorkIsDoubleFsep :
      globalNestedFourHelicityWork ≡ Fold.two * Fsep
    globalNestedWorkIsDoubleFsep =
      sumNestedWorkIsDoubleCompanion (Cube.cutoffModes cutoff)

    nineNestedIsEighteenCompanion :
      nine * globalNestedFourHelicityWork
      ≡ R806.eighteen * Fsep
    nineNestedIsEighteenCompanion =
      trans
        (cong (nine *_) globalNestedWorkIsDoubleFsep)
        (solve
          ( nine
          ∷ Fold.two
          ∷ R806.eighteen
          ∷ Fsep
          ∷ []))

    separatedNestedFourHelicityNormalForm :
      Dsep
      ≡
      Fold.two *
        (nine * globalNestedFourHelicityWork - Qsep)
    separatedNestedFourHelicityNormalForm =
      trans
        P.separatedFullCompanionNormalForm
        (cong
          (Fold.two *_)
          (cong
            (_- Qsep)
            (sym nineNestedIsEighteenCompanion)))

    nestedFourHelicityBalanceImpliesSeparatedCancellation :
      Qsep ≡ nine * globalNestedFourHelicityWork →
      Dsep ≡ 0ℚ
    nestedFourHelicityBalanceImpliesSeparatedCancellation balance =
      trans
        separatedNestedFourHelicityNormalForm
        (trans
          (cong
            (Fold.two *_)
            (cong
              (nine * globalNestedFourHelicityWork -_)
              balance))
          (solve
            ( Fold.two
            ∷ nine
            ∷ globalNestedFourHelicityWork
            ∷ [])))

    separatedCancellationImpliesNestedFourHelicityBalance :
      Dsep ≡ 0ℚ →
      Qsep ≡ nine * globalNestedFourHelicityWork
    separatedCancellationImpliesNestedFourHelicityBalance cancelled =
      trans
        (P.separatedCancellationImpliesFullCompanionBalance cancelled)
        (sym nineNestedIsEighteenCompanion)

round813LiveSeparatedCompanionExpandedThroughR573 : Bool
round813LiveSeparatedCompanionExpandedThroughR573 = true

round813SeparatedMaskPreservedBeforeFourHelicityExpansion : Bool
round813SeparatedMaskPreservedBeforeFourHelicityExpansion = true

round813GlobalNestedWorkIsDoubleR811CompanionWork : Bool
round813GlobalNestedWorkIsDoubleR811CompanionWork = true

round813SeparatedResidualIs2Times9NestedMinusQ : Bool
round813SeparatedResidualIs2Times9NestedMinusQ = true

round813CancellationEquivalentToQEquals9NestedFourHelicityWork : Bool
round813CancellationEquivalentToQEquals9NestedFourHelicityWork = true

round813NewLocalHelicityEstimateRequired : Bool
round813NewLocalHelicityEstimateRequired = false

round813QToNestedMultiplierIdentificationClosed : Bool
round813QToNestedMultiplierIdentificationClosed = false

round813IntroducesEstimate : Bool
round813IntroducesEstimate = false

round813W2Closed : Bool
round813W2Closed = false

round813ClayPromotion : Bool
round813ClayPromotion = false

round813CancellationEquivalentToQEquals9NestedFourHelicityWorkIsTrue :
  round813CancellationEquivalentToQEquals9NestedFourHelicityWork ≡ true
round813CancellationEquivalentToQEquals9NestedFourHelicityWorkIsTrue = refl

round813QToNestedMultiplierIdentificationClosedIsFalse :
  round813QToNestedMultiplierIdentificationClosed ≡ false
round813QToNestedMultiplierIdentificationClosedIsFalse = refl

round813IntroducesEstimateIsFalse :
  round813IntroducesEstimate ≡ false
round813IntroducesEstimateIsFalse = refl

round813W2ClosedIsFalse :
  round813W2Closed ≡ false
round813W2ClosedIsFalse = refl

round813ClayPromotionIsFalse :
  round813ClayPromotion ≡ false
round813ClayPromotionIsFalse = refl
