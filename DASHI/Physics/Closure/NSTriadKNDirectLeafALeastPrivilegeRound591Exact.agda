module DASHI.Physics.Closure.NSTriadKNDirectLeafALeastPrivilegeRound591Exact where

------------------------------------------------------------------------
-- ROUND591 / R572 TEMPORAL-PRODUCER LEAST PRIVILEGE
--
-- R572 still asked its producer to supply two facts that R571 already proves
-- from the literal live carrier: terminal global self-flux nonnegativity and
-- pointwise self-Gram nonnegativity.  Only the standard order property that the
-- integral of a nonnegative function is nonnegative is needed to lift the latter.
--
-- This round removes both duplicated sign receipts from that producer tactic.
-- R592 subsequently shows the whole R568/R572 temporal route is optional
-- relative to the canonical R503 direct signed-cross consumer.  This module
-- remains a minimized compatible producer, not a Clay prerequisite.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as FTC564
import DASHI.Physics.Closure.NSTriadKNLiveGlobalSelfFluxTangentWeldRound570Exact as T570
import DASHI.Physics.Closure.NSTriadKNLiveSelfGramAndFluxOrderRound571Exact as O571
import DASHI.Physics.Closure.NSTriadKNLiveCommutatorOnlyLeafABoundaryRound568Exact as C568
import DASHI.Physics.Closure.NSTriadKNDirectLeafACompilerRound572Exact as R572
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = Rational.rationalRealField

module Compile
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf : (Time → ℚ) → (Time → ℚ) → Set)
    (projectedCrossCalculus :
      R426.ProjectedCrossDerivativeCalculus Time VectorDerivativeOf)
    (vectorAlgebra : R425.VectorDerivativeAlgebra Time VectorDerivativeOf)
    (hermitianCalculus :
      R417.HermitianDerivativeCalculus
        Time VectorDerivativeOf ScalarDerivativeOf)
    (constantCalculus :
      R416.ScalarConstantDerivativeCalculus Time ScalarDerivativeOf)
    (scalarAlgebra : R412.ScalarDerivativeAlgebra Time ScalarDerivativeOf)
    (integration : R495.IntegrationTransportAuthority Time integrateTo)
    (D : R408.LiteralDynamics.LiteralRHSTrajectoryData
      Time initialTime integrateTo VectorDerivativeOf)
    (R : R405.LiteralCutoffSupport.LiteralNonzeroCutoffTrajectory
      Time initialTime integrateTo VectorDerivativeOf
      (R408.LiteralDynamics.literalPhysicalTrajectory
        Time initialTime integrateTo VectorDerivativeOf D)) where

  module Old = R572.Compile
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCrossCalculus vectorAlgebra hermitianCalculus
    constantCalculus scalarAlgebra integration D R

  module Comm = C568.LiveCommutatorOnly
    Time initialTime integrateTo VectorDerivativeOf integration

  record DirectLeafALeastPrivilegeProducer591 : Set₁ where
    field
      scalarFTC591 :
        FTC564.ScalarFundamentalTheorem564
          Time initialTime integrateTo ScalarDerivativeOf
      nonnegativeIntegration591 :
        O571.NonnegativeIntegrationAuthority571 Time integrateTo
      initialSelfFluxBound591 : ℚ
      initialSelfFluxUpper591 :
        (cutoff : Nat) →
        let module Tangent = T570.TangentWeld
              Time initialTime integrateTo
              VectorDerivativeOf ScalarDerivativeOf
              projectedCrossCalculus vectorAlgebra hermitianCalculus
              constantCalculus scalarAlgebra integration D R cutoff
        in Tangent.Global.globalSelfFlux initialTime ≤ initialSelfFluxBound591
      commutatorBudget591 : Comm.CommutatorOnlySpacetimeBudget568
        (R408.LiteralDynamics.literalPhysicalTrajectory
          Time initialTime integrateTo VectorDerivativeOf D) R
      cutoffIndependentLeafABound591 : Time → ℚ
      combinedBoundIsTwiceLeafABound591 :
        (terminal : Time) →
        R539.two * cutoffIndependentLeafABound591 terminal
        ≡ Comm.cutoffIndependentCommutatorBound568 commutatorBudget591 terminal
          + initialSelfFluxBound591

  open DirectLeafALeastPrivilegeProducer591 public

  toR572Producer591 :
    DirectLeafALeastPrivilegeProducer591 → Old.DirectLeafAProducer572
  toR572Producer591 P = record
    { Old.scalarFTC572 = scalarFTC591 P
    ; Old.integratedSelfGramNonnegative572 = λ cutoff terminal →
        let module Order = O571.LiveOrder
              Time initialTime integrateTo
              VectorDerivativeOf ScalarDerivativeOf
              projectedCrossCalculus vectorAlgebra hermitianCalculus
              constantCalculus scalarAlgebra integration D R cutoff
        in Order.integratedLiveSelfGramNonnegative571
          (nonnegativeIntegration591 P) terminal
    ; Old.terminalSelfFluxNonnegative572 = λ cutoff terminal →
        let module Order = O571.LiveOrder
              Time initialTime integrateTo
              VectorDerivativeOf ScalarDerivativeOf
              projectedCrossCalculus vectorAlgebra hermitianCalculus
              constantCalculus scalarAlgebra integration D R cutoff
        in Order.At.liveGlobalSelfFluxNonnegative571 terminal
    ; Old.initialSelfFluxBound572 = initialSelfFluxBound591 P
    ; Old.initialSelfFluxUpper572 = initialSelfFluxUpper591 P
    ; Old.commutatorBudget572 = commutatorBudget591 P
    ; Old.cutoffIndependentLeafABound572 = cutoffIndependentLeafABound591 P
    ; Old.combinedBoundIsTwiceLeafABound572 = combinedBoundIsTwiceLeafABound591 P
    }

round591PointwiseSelfGramSignAlreadyOwned : Bool
round591PointwiseSelfGramSignAlreadyOwned =
  O571.round571PointwiseLiveSelfGramNonnegativeClosed

round591TerminalSelfFluxSignAlreadyOwned : Bool
round591TerminalSelfFluxSignAlreadyOwned =
  O571.round571PointwiseLiveGlobalSelfFluxNonnegativeClosed

round591R572ProducerSignSocketsMandatory : Bool
round591R572ProducerSignSocketsMandatory = false

round591TemporalRouteCanonicalPrerequisite : Bool
round591TemporalRouteCanonicalPrerequisite = false

round591TemporalProducerStillCompatible : Bool
round591TemporalProducerStillCompatible = true

round591CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round591CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round591ClayPromotion : Bool
round591ClayPromotion = false

round591R572ProducerSignSocketsMandatoryIsFalse :
  round591R572ProducerSignSocketsMandatory ≡ false
round591R572ProducerSignSocketsMandatoryIsFalse = refl

round591TemporalRouteCanonicalPrerequisiteIsFalse :
  round591TemporalRouteCanonicalPrerequisite ≡ false
round591TemporalRouteCanonicalPrerequisiteIsFalse = refl

round591ClayPromotionIsFalse : round591ClayPromotion ≡ false
round591ClayPromotionIsFalse = refl
