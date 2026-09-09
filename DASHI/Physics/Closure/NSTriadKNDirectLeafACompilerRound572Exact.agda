module DASHI.Physics.Closure.NSTriadKNDirectLeafACompilerRound572Exact where

------------------------------------------------------------------------
-- ROUND572 / DIRECT LEAF-A COMPILER AFTER THE R566-R570 NORMAL FORM
--
-- The current direct route has only two kinds of unpaid authority:
--
--   * standard temporal/order authority for the already-constructed literal
--     self-flux derivative and nonnegative self-Gram integral;
--   * the genuinely new cutoff-uniform signed spacetime budget for the single
--     commutator-only full square from R568/R570.
--
-- This owner composes those receipts all the way into the PRE-EXISTING R503
-- DirectOffDiagonalBudget.  No replacement R406 observable, heat surrogate,
-- absolute-value majorant, or parallel leaf-A consumer is introduced.
--
-- The harmless factor 2 from R553 is discharged by an explicit rational
-- halving receipt.  We keep that normalization proof-bearing rather than hide
-- division in the consumer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

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
import DASHI.Physics.Closure.NSTriadKNDirectResolventIntegratedCompanionRound500Exact as R500
import DASHI.Physics.Closure.NSTriadKNDirectResolventSignedCrossToR415Round503Exact as R503
import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNFavorableDiagonalTemporalUpperRound553Exact as R553
import DASHI.Physics.Closure.NSTriadKNLiveIntegratedDiagonalReducedNormalFormRound557Exact as R557
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as FTC564
import DASHI.Physics.Closure.NSTriadKNLiveGlobalSelfFluxTangentWeldRound570Exact as T570
import DASHI.Physics.Closure.NSTriadKNFactoredFullCommutatorBudgetBidiRound570Exact as C570
import DASHI.Physics.Closure.NSTriadKNLiveCommutatorOnlyLeafABoundaryRound568Exact as C568
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = Rational.rationalRealField

twoPositive572 : 0ℚ < R539.two
twoPositive572 =
  ℚP.+-mono-<-< (ℚP.positive⁻¹ 1ℚ) (ℚP.positive⁻¹ 1ℚ)

module Compile
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf :
      (Time → ℚ) → (Time → ℚ) → Set)
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

  module Literal = R408.LiteralDynamics
    Time initialTime integrateTo VectorDerivativeOf
  module Integrated = R557.LiveIntegrated
    Time initialTime integrateTo VectorDerivativeOf integration
  module Direct = R500.IntegratedDirect
    Time initialTime integrateTo VectorDerivativeOf integration
  module DirectBudget = R503.DirectSignedCross
    Time initialTime integrateTo VectorDerivativeOf integration
  module Comm = C568.LiveCommutatorOnly
    Time initialTime integrateTo VectorDerivativeOf integration
  module Bidi = C570.Bidi
    Time initialTime integrateTo VectorDerivativeOf integration

  T = Literal.literalPhysicalTrajectory D

  ----------------------------------------------------------------------
  -- The only non-PDE inputs left around the diagonal are standard scalar
  -- calculus/order receipts.  The endpoint bound is required uniformly in the
  -- cutoff on the SAME global self-flux observable used by the FTC lane.
  ----------------------------------------------------------------------

  record DirectLeafAProducer572 : Set₁ where
    field
      scalarFTC572 :
        FTC564.ScalarFundamentalTheorem564
          Time initialTime integrateTo ScalarDerivativeOf

      integratedSelfGramNonnegative572 :
        (cutoff : Nat) (terminal : Time) →
        0ℚ ≤ integrateTo (Integrated.selfGram T R cutoff) terminal

      terminalSelfFluxNonnegative572 :
        (cutoff : Nat) (terminal : Time) →
        let module Tangent = T570.TangentWeld
              Time initialTime integrateTo
              VectorDerivativeOf ScalarDerivativeOf
              projectedCrossCalculus vectorAlgebra hermitianCalculus
              constantCalculus scalarAlgebra integration D R cutoff
        in
        0ℚ ≤ Tangent.Global.globalSelfFlux terminal

      initialSelfFluxBound572 : ℚ

      initialSelfFluxUpper572 :
        (cutoff : Nat) →
        let module Tangent = T570.TangentWeld
              Time initialTime integrateTo
              VectorDerivativeOf ScalarDerivativeOf
              projectedCrossCalculus vectorAlgebra hermitianCalculus
              constantCalculus scalarAlgebra integration D R cutoff
        in
        Tangent.Global.globalSelfFlux initialTime ≤ initialSelfFluxBound572

      commutatorBudget572 : Comm.CommutatorOnlySpacetimeBudget568 T R

      cutoffIndependentLeafABound572 : Time → ℚ

      combinedBoundIsTwiceLeafABound572 :
        (terminal : Time) →
        R539.two * cutoffIndependentLeafABound572 terminal
        ≡ Comm.cutoffIndependentCommutatorBound568 commutatorBudget572 terminal
          + initialSelfFluxBound572

  open DirectLeafAProducer572 public

  ----------------------------------------------------------------------
  -- Exact scalar upper bound for the literal R406 remainder integral.
  ----------------------------------------------------------------------

  literalR406IntegralUpper572 :
    (P : DirectLeafAProducer572) →
    (cutoff : Nat) (terminal : Time) →
    integrateTo (Integrated.literalRemainder T R cutoff) terminal
    ≤ cutoffIndependentLeafABound572 P terminal
  literalR406IntegralUpper572 P cutoff terminal =
    let
      module Tangent = T570.TangentWeld
        Time initialTime integrateTo
        VectorDerivativeOf ScalarDerivativeOf
        projectedCrossCalculus vectorAlgebra hermitianCalculus
        constantCalculus scalarAlgebra integration D R cutoff

      existingFactoredBudget =
        Bidi.commutatorBudgetBuildsExistingFactoredBudget
          (commutatorBudget572 P)

      reduced = Integrated.liveIntegratedReducedNormalForm
        T R cutoff terminal

      tangentFTC = Tangent.exactReducedTangentEndpointFTC570
        (scalarFTC572 P) terminal

      favorable :
        R539.two * integrateTo (Integrated.literalRemainder T R cutoff) terminal
        ≤ integrateTo (Integrated.factoredFull T R cutoff) terminal
          + Tangent.Global.globalSelfFlux initialTime
      favorable =
        R553.favorableDiagonalUpper
          (integrateTo (Integrated.literalRemainder T R cutoff) terminal)
          (integrateTo (Integrated.factoredFull T R cutoff) terminal)
          (integrateTo (Integrated.selfGram T R cutoff) terminal)
          (integrateTo (Integrated.selfFluxTangent T R cutoff) terminal)
          (Tangent.Global.globalSelfFlux initialTime)
          (Tangent.Global.globalSelfFlux terminal)
          reduced
          tangentFTC
          (integratedSelfGramNonnegative572 P cutoff terminal)
          (terminalSelfFluxNonnegative572 P cutoff terminal)

      factoredUpper =
        Bidi.Existing.literalFactoredFullUpper
          existingFactoredBudget cutoff terminal

      sumUpper :
        integrateTo (Integrated.factoredFull T R cutoff) terminal
          + Tangent.Global.globalSelfFlux initialTime
        ≤ Comm.cutoffIndependentCommutatorBound568
            (commutatorBudget572 P) terminal
          + initialSelfFluxBound572 P
      sumUpper =
        ℚP.+-mono-≤ factoredUpper (initialSelfFluxUpper572 P cutoff)

      combinedUpper :
        R539.two * integrateTo (Integrated.literalRemainder T R cutoff) terminal
        ≤ Comm.cutoffIndependentCommutatorBound568
            (commutatorBudget572 P) terminal
          + initialSelfFluxBound572 P
      combinedUpper = ℚP.≤-trans favorable sumUpper

      scaledToHalf :
        R539.two * integrateTo (Integrated.literalRemainder T R cutoff) terminal
        ≤ R539.two * cutoffIndependentLeafABound572 P terminal
      scaledToHalf =
        subst
          (λ rhs →
            R539.two * integrateTo (Integrated.literalRemainder T R cutoff) terminal
            ≤ rhs)
          (sym (combinedBoundIsTwiceLeafABound572 P terminal))
          combinedUpper
    in
    ℚP.*-cancelˡ-≤-pos R539.two scaledToHalf

  ----------------------------------------------------------------------
  -- Final compiler into the pre-existing R503 leaf-A consumer.
  ----------------------------------------------------------------------

  directLeafAProducerBuildsR503 :
    DirectLeafAProducer572 → DirectBudget.DirectOffDiagonalBudget T R
  directLeafAProducerBuildsR503 P = record
    { DirectBudget.cutoffIndependentBound = cutoffIndependentLeafABound572 P
    ; DirectBudget.directOffDiagonalBudget = λ cutoff terminal →
        subst
          (λ lhs → lhs ≤ cutoffIndependentLeafABound572 P terminal)
          (Direct.literalR406IntegralIsFourIntegratedDirectCompanion
            T R cutoff terminal)
          (literalR406IntegralUpper572 P cutoff terminal)
    }

------------------------------------------------------------------------
-- BIDI / frontier status.
------------------------------------------------------------------------

round572TemporalSameObjectChainConsumed : Bool
round572TemporalSameObjectChainConsumed = true

round572CommutatorBudgetPaysLiteralFactoredFullConsumer : Bool
round572CommutatorBudgetPaysLiteralFactoredFullConsumer = true

round572R503DirectBudgetCompilerClosedGivenReceipts : Bool
round572R503DirectBudgetCompilerClosedGivenReceipts = true

round572IntroducesParallelLeafAConsumer : Bool
round572IntroducesParallelLeafAConsumer = false

round572NovelCommutatorSpacetimeBudgetClosed : Bool
round572NovelCommutatorSpacetimeBudgetClosed = false

round572StandardScalarFTCInstalled : Bool
round572StandardScalarFTCInstalled = false

round572CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round572CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round572ClayPromotion : Bool
round572ClayPromotion = false

round572R503DirectBudgetCompilerClosedGivenReceiptsIsTrue :
  round572R503DirectBudgetCompilerClosedGivenReceipts ≡ true
round572R503DirectBudgetCompilerClosedGivenReceiptsIsTrue = refl

round572IntroducesParallelLeafAConsumerIsFalse :
  round572IntroducesParallelLeafAConsumer ≡ false
round572IntroducesParallelLeafAConsumerIsFalse = refl

round572ClayPromotionIsFalse : round572ClayPromotion ≡ false
round572ClayPromotionIsFalse = refl
