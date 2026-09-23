{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNDirectLeafAStandardReceiptsRound593Exact where

------------------------------------------------------------------------
-- ROUND593 / R568 -> R572 STANDARD-RECEIPT COMPRESSION
--
-- Two inputs still exposed by the R591 compatibility producer are not
-- independent mathematical obligations:
--
--   (1) R571's "integral of a nonnegative function is nonnegative" follows
--       from the already-used integration monotonicity authority plus R495's
--       exact integral-of-zero law.
--
--   (2) R572's final factor-two normalization does not need a caller-selected
--       bound/equality pair.  Over the exact rational carrier define the leaf
--       bound to be one half of (commutator bound + initial endpoint bound).
--
-- Consequently a temporal R568 producer needs only:
--
--   * scalar FTC on the concrete time carrier;
--   * the ordinary integration-order authority already used elsewhere;
--   * one cutoff-independent initial self-flux bound and its same-object upper;
--   * the genuinely analytic R568 commutator budget.
--
-- Pointwise self-Gram and terminal self-flux positivity are supplied by R571
-- through R591.  No Navier--Stokes estimate is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

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
import DASHI.Physics.Closure.NSTriadKNDirectLeafALeastPrivilegeRound591Exact as R591
import DASHI.Physics.Closure.NSTriadKNSignedRateVectorPaymentToR503Exact as Order
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = Rational.rationalRealField

half593 : ℚ
half593 = Int.+ 1 / 2

------------------------------------------------------------------------
-- R495 + monotonicity -> R571 nonnegative integration.
------------------------------------------------------------------------

orderBuildsNonnegativeIntegration593 :
  {Time : Set} →
  {integrateTo : (Time → ℚ) → Time → ℚ} →
  R495.IntegrationTransportAuthority Time integrateTo →
  Order.IntegrationOrderAuthority Time integrateTo →
  O571.NonnegativeIntegrationAuthority571 Time integrateTo
orderBuildsNonnegativeIntegration593 integration order = record
  { O571.NonnegativeIntegrationAuthority571.integrateNonnegative571 =
      λ f pointwise terminal →
        let
          zeroBelow :
            integrateTo (λ _ → 0ℚ) terminal ≤ integrateTo f terminal
          zeroBelow =
            Order.integrateMonotone order
              (λ _ → 0ℚ) f pointwise terminal
        in
        subst
          (λ lower → lower ≤ integrateTo f terminal)
          (R495.integrateZero integration terminal)
          zeroBelow
  }

------------------------------------------------------------------------
-- Remove the caller-selected final half-bound normalization.
------------------------------------------------------------------------

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

  module Least = R591.Compile
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCrossCalculus vectorAlgebra hermitianCalculus
    constantCalculus scalarAlgebra integration D R

  module Comm = C568.LiveCommutatorOnly
    Time initialTime integrateTo VectorDerivativeOf integration

  record DirectLeafAStandardProducer593 : Set₁ where
    field
      scalarFTC593 :
        FTC564.ScalarFundamentalTheorem564
          Time initialTime integrateTo ScalarDerivativeOf

      integrationOrder593 :
        Order.IntegrationOrderAuthority Time integrateTo

      initialSelfFluxBound593 : ℚ

      initialSelfFluxUpper593 :
        (cutoff : Nat) →
        let module Tangent = T570.TangentWeld
              Time initialTime integrateTo
              VectorDerivativeOf ScalarDerivativeOf
              projectedCrossCalculus vectorAlgebra hermitianCalculus
              constantCalculus scalarAlgebra integration D R cutoff
        in Tangent.Global.globalSelfFlux initialTime ≤ initialSelfFluxBound593

      commutatorBudget593 :
        Comm.CommutatorOnlySpacetimeBudget568
          (R408.LiteralDynamics.literalPhysicalTrajectory
            Time initialTime integrateTo VectorDerivativeOf D) R

  open DirectLeafAStandardProducer593 public

  cutoffIndependentLeafABound593 :
    DirectLeafAStandardProducer593 → Time → ℚ
  cutoffIndependentLeafABound593 P terminal =
    half593 *
      ( Comm.cutoffIndependentCommutatorBound568
          (commutatorBudget593 P) terminal
      + initialSelfFluxBound593 P )

  combinedBoundIsTwiceLeafABound593 :
    (P : DirectLeafAStandardProducer593) →
    (terminal : Time) →
    R539.two * cutoffIndependentLeafABound593 P terminal
    ≡ Comm.cutoffIndependentCommutatorBound568
        (commutatorBudget593 P) terminal
      + initialSelfFluxBound593 P
  combinedBoundIsTwiceLeafABound593 P terminal =
    solve
      ( Comm.cutoffIndependentCommutatorBound568
          (commutatorBudget593 P) terminal
      ∷ initialSelfFluxBound593 P
      ∷ [])

  toR591Producer593 :
    DirectLeafAStandardProducer593 →
    Least.DirectLeafALeastPrivilegeProducer591
  toR591Producer593 P = record
    { Least.scalarFTC591 = scalarFTC593 P
    ; Least.nonnegativeIntegration591 =
        orderBuildsNonnegativeIntegration593
          integration (integrationOrder593 P)
    ; Least.initialSelfFluxBound591 = initialSelfFluxBound593 P
    ; Least.initialSelfFluxUpper591 = initialSelfFluxUpper593 P
    ; Least.commutatorBudget591 = commutatorBudget593 P
    ; Least.cutoffIndependentLeafABound591 =
        cutoffIndependentLeafABound593 P
    ; Least.combinedBoundIsTwiceLeafABound591 =
        combinedBoundIsTwiceLeafABound593 P
    }

  toR572Producer593 :
    DirectLeafAStandardProducer593 →
    Least.Old.DirectLeafAProducer572
  toR572Producer593 P =
    Least.toR572Producer591 (toR591Producer593 P)

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round593IntegrationOrderReusesExistingA4Authority : Bool
round593IntegrationOrderReusesExistingA4Authority = true

round593SeparateNonnegativeIntegrationReceiptRequired : Bool
round593SeparateNonnegativeIntegrationReceiptRequired = false

round593CallerSelectedHalfBoundRequired : Bool
round593CallerSelectedHalfBoundRequired = false

round593PointwiseSelfGramSignReceiptRequired : Bool
round593PointwiseSelfGramSignReceiptRequired = false

round593TerminalSelfFluxSignReceiptRequired : Bool
round593TerminalSelfFluxSignReceiptRequired = false

round593InitialUniformEndpointBoundStillProofBearing : Bool
round593InitialUniformEndpointBoundStillProofBearing = true

round593ScalarFTCStillProofBearing : Bool
round593ScalarFTCStillProofBearing = true

round593NovelR568BudgetStillProofBearing : Bool
round593NovelR568BudgetStillProofBearing = true

round593IntroducesNewNSEstimate : Bool
round593IntroducesNewNSEstimate = false

round593CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round593CurrentGlobalFirstResidualStillLeafA =
  R504.currentFirstTerminalResidual

round593ClayPromotion : Bool
round593ClayPromotion = false

round593IntegrationOrderReusesExistingA4AuthorityIsTrue :
  round593IntegrationOrderReusesExistingA4Authority ≡ true
round593IntegrationOrderReusesExistingA4AuthorityIsTrue = refl

round593SeparateNonnegativeIntegrationReceiptRequiredIsFalse :
  round593SeparateNonnegativeIntegrationReceiptRequired ≡ false
round593SeparateNonnegativeIntegrationReceiptRequiredIsFalse = refl

round593CallerSelectedHalfBoundRequiredIsFalse :
  round593CallerSelectedHalfBoundRequired ≡ false
round593CallerSelectedHalfBoundRequiredIsFalse = refl

round593InitialUniformEndpointBoundStillProofBearingIsTrue :
  round593InitialUniformEndpointBoundStillProofBearing ≡ true
round593InitialUniformEndpointBoundStillProofBearingIsTrue = refl

round593ScalarFTCStillProofBearingIsTrue :
  round593ScalarFTCStillProofBearing ≡ true
round593ScalarFTCStillProofBearingIsTrue = refl

round593NovelR568BudgetStillProofBearingIsTrue :
  round593NovelR568BudgetStillProofBearing ≡ true
round593NovelR568BudgetStillProofBearingIsTrue = refl

round593IntroducesNewNSEstimateIsFalse :
  round593IntroducesNewNSEstimate ≡ false
round593IntroducesNewNSEstimateIsFalse = refl

round593ClayPromotionIsFalse :
  round593ClayPromotion ≡ false
round593ClayPromotionIsFalse = refl
