{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650GlobalProductRuleLoopBoundaryRound774Exact where

------------------------------------------------------------------------
-- ROUND774 / THE COMPLETE GLOBAL PRODUCT-RULE COLLAPSE RETURNS EXACTLY
--            TO THE OLD COMBINED-MINUS-PRODUCTION W2 SCALAR
--
-- R773:
--
--   9 BaseProductRuleFold - 2 PairedDyadicFold = 2 * R749Fold.
--
-- R749:
--
--   R749Fold = R745OrbitAlignedFold.
--
-- R745:
--
--   R745OrbitAlignedFold
--     = 3 * CombinedResidue - 3 * CriticalProduction.
--
-- Therefore exactly:
--
--   9 BaseProductRuleFold - 2 PairedDyadicFold
--     = 6 * (CombinedResidue - CriticalProduction).
--
-- Thus completing the p/q cyclic reindexing before using the R25 class
-- structure is a representation loop.  It removes pointwise cyclic clutter
-- but cannot by itself produce a new sign, gap, or coercive payment.
--
-- Any genuinely new W2 gain must preserve additional local structure before
-- this global collapse (e.g. R25 class, shell gap, helicity, or another
-- physically justified signed localization).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _-_; _*_)
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
import DASHI.Physics.Closure.NSTriadKNR650CriticalProductionIncidenceCarrierRound744Exact as R744
import DASHI.Physics.Closure.NSTriadKNR650GlobalPairedResidualProductRuleRound773Exact as R773

F : C3.RealField _
F = Rational.rationalRealField

six : ℚ
six = 6

module GlobalLoop
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

  module G = R773.GlobalProductRuleResidual
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Packet = G.Packet

  module At
      (cutoff : Nat)
      (time : Time)
      (S : Packet.LivePhysicalPacketStructure D C cutoff) where

    module P = G.At cutoff time S
    module Difference = P.Base
    module Orbit = Difference.Base

    globalProductRuleScalar : ℚ
    globalProductRuleScalar =
      R773.nine * P.pairedProductRuleBaseFold
        - Fold.two * P.pairedDyadicProductionFold

    globalProductRuleScalarIsSixCombinedMinusProduction :
      globalProductRuleScalar
      ≡
      six *
        ( G.Paired.Local.O.Combined.combinedResidueAt cutoff time
        - G.Paired.Local.O.W2.K.productionAt cutoff time )
    globalProductRuleScalarIsSixCombinedMinusProduction =
      trans
        P.productRuleNormalFormIsTwiceR749Fold
        (trans
          (cong
            (Fold.two *_)
            Difference.differenceAlignedFoldIsR745OrbitAlignedFold)
          (trans
            (cong
              (Fold.two *_)
              Orbit.foldIsThreeCombinedMinusThreeProduction)
            (solve
              ( Fold.two
              ∷ R744.three
              ∷ six
              ∷ G.Paired.Local.O.Combined.combinedResidueAt cutoff time
              ∷ G.Paired.Local.O.W2.K.productionAt cutoff time
              ∷ [])))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round774GlobalProductRuleCollapseReturnsToCombinedMinusProduction : Bool
round774GlobalProductRuleCollapseReturnsToCombinedMinusProduction = true

round774GlobalCyclicReindexingCreatesNewSign : Bool
round774GlobalCyclicReindexingCreatesNewSign = false

round774GlobalProductRuleRouteCreatesNewAnalyticLeaf : Bool
round774GlobalProductRuleRouteCreatesNewAnalyticLeaf = false

round774ClassLocalStructureMustBeUsedBeforeGlobalCollapse : Bool
round774ClassLocalStructureMustBeUsedBeforeGlobalCollapse = true

round774IntroducesEstimate : Bool
round774IntroducesEstimate = false

round774W2Closed : Bool
round774W2Closed = false

round774ClayPromotion : Bool
round774ClayPromotion = false

round774GlobalProductRuleCollapseReturnsToCombinedMinusProductionIsTrue :
  round774GlobalProductRuleCollapseReturnsToCombinedMinusProduction ≡ true
round774GlobalProductRuleCollapseReturnsToCombinedMinusProductionIsTrue = refl

round774GlobalCyclicReindexingCreatesNewSignIsFalse :
  round774GlobalCyclicReindexingCreatesNewSign ≡ false
round774GlobalCyclicReindexingCreatesNewSignIsFalse = refl

round774GlobalProductRuleRouteCreatesNewAnalyticLeafIsFalse :
  round774GlobalProductRuleRouteCreatesNewAnalyticLeaf ≡ false
round774GlobalProductRuleRouteCreatesNewAnalyticLeafIsFalse = refl

round774ClassLocalStructureMustBeUsedBeforeGlobalCollapseIsTrue :
  round774ClassLocalStructureMustBeUsedBeforeGlobalCollapse ≡ true
round774ClassLocalStructureMustBeUsedBeforeGlobalCollapseIsTrue = refl

round774IntroducesEstimateIsFalse :
  round774IntroducesEstimate ≡ false
round774IntroducesEstimateIsFalse = refl

round774W2ClosedIsFalse :
  round774W2Closed ≡ false
round774W2ClosedIsFalse = refl

round774ClayPromotionIsFalse :
  round774ClayPromotion ≡ false
round774ClayPromotionIsFalse = refl
