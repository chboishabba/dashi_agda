module DASHI.Papers.NavierStokes.TheoremInterfaceRound76Exact where

------------------------------------------------------------------------
-- PAPER-FACING ROUND76 DELTA
--
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Luis Caffarelli; Robert Kohn; Louis Nirenberg.
-- Title: "Partial regularity of suitable weak solutions of the Navier-Stokes
-- equations".
-- DOI: 10.1002/cpa.3160350604.
--
-- Authors: Hiroshi Fujita; Tosio Kato.
-- Title: "On the Navier-Stokes initial value problem. I".
-- DOI: 10.1007/BF00276188.
--
-- Author: J. D. Biggins.
-- Title: "Martingale convergence in the branching random walk".
-- DOI: 10.2307/3213258.
--
-- Author: Michael Hochman.
-- Title: "On self-similar sets with overlaps and inverse theorems for entropy".
-- DOI: 10.4007/annals.2014.180.2.7.
--
-- ROUND76 PAPER DELTA
--
-- 1. The fixed-output response frame is now explicitly normalized on the
--    literal Round75 two-channel row.  If ||u_k||^2 E_N<=1 then
--
--      (signed triadic remainder)^2 <= Q_k.
--
--    The remaining concentration statement is dynamic same-object transport,
--    physical normalization at the critical event, and Q_k=physical charge.
--
-- 2. Route B no longer asks for cross-generation charge orthogonality.  The
--    exact one-step identity M_(j+1)=M_j+Delta_j telescopes over arbitrary
--    finite histories, while the existing finite Carleson budget is applied
--    only to the FINAL antichain.  If the final mass exceeds the budget, that
--    one generation already contradicts funding.
--
-- 3. The HH-bad final-gate target is now exactly the remaining scalar headroom:
--
--      2 Lambda_bad < 1 - (eta_soft + 1/16)
--
--    implies the sharp total is <1.  CKN/Fujita--Kato supply provenance for
--    threshold/smallness logic only; their epsilons are not imported as DASHI
--    constants.
--
-- 4. The shortest remaining cutset is therefore 9 packages plus final assembly:
--
--    selected literal global Galerkin trajectory;
--    selected-trajectory fine structured balance;
--    dynamic canonical square-charge event;
--    physical supercritical final-antichain propagation;
--    critical-ratio barrier composition;
--    normalized six-three Gram estimate;
--    physical HH-bad capacity/headroom bound;
--    soft-data/boundary closure;
--    annular multiplier/kernel bound.
--
-- The old cumulative-budget arithmetic and final scalar-gate arithmetic are no
-- longer independent packages.  Clay promotion remains false.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Papers.NavierStokes.TheoremInterfaceRound74Exact
import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound76Exact as R76

round76PaperLiteralNormalizedSquareChargeCompiler : Bool
round76PaperLiteralNormalizedSquareChargeCompiler =
  R76.round76LiteralNormalizedSquareChargeCompiler

round76PaperRouteBFinalAntichainContradictionCompiler : Bool
round76PaperRouteBFinalAntichainContradictionCompiler =
  R76.round76RouteBFinalAntichainContradictionCompiler

round76PaperRouteBRequiresCrossGenerationChargeOrthogonality : Bool
round76PaperRouteBRequiresCrossGenerationChargeOrthogonality =
  R76.round76RouteBRequiresCrossGenerationChargeOrthogonality

round76PaperSharpHHBadHeadroomCompiler : Bool
round76PaperSharpHHBadHeadroomCompiler =
  R76.round76SharpHHBadHeadroomCompiler

round76PaperSelectedGalerkinTrajectoryExistsGloballyAndIsLiteral : Bool
round76PaperSelectedGalerkinTrajectoryExistsGloballyAndIsLiteral =
  R76.round76SelectedGalerkinTrajectoryExistsGloballyAndIsLiteral

round76PaperSelectedTrajectoryInstantiatesFineStructuredBalance : Bool
round76PaperSelectedTrajectoryInstantiatesFineStructuredBalance =
  R76.round76SelectedTrajectoryInstantiatesFineStructuredBalance

round76PaperPhysicalDynamicTwoChannelSquareCharge : Bool
round76PaperPhysicalDynamicTwoChannelSquareCharge =
  R76.round76PhysicalDynamicTwoChannelSquareCharge

round76PaperPhysicalSupercriticalFinalAntichainPropagation : Bool
round76PaperPhysicalSupercriticalFinalAntichainPropagation =
  R76.round76PhysicalSupercriticalFinalAntichainPropagation

round76PaperCriticalRatioBarrier : Bool
round76PaperCriticalRatioBarrier = R76.round76CriticalRatioBarrier

round76PaperPhysicalNormalizedSixThreeGramEstimate : Bool
round76PaperPhysicalNormalizedSixThreeGramEstimate =
  R76.round76PhysicalNormalizedSixThreeGramEstimate

round76PaperPhysicalHHBadCapacityChargeBound : Bool
round76PaperPhysicalHHBadCapacityChargeBound =
  R76.round76PhysicalHHBadCapacityChargeBound

round76PaperPhysicalSoftDataAndBoundaryClosure : Bool
round76PaperPhysicalSoftDataAndBoundaryClosure =
  R76.round76PhysicalSoftDataAndBoundaryClosure

round76PaperPhysicalAnnularMultiplierKernelBound : Bool
round76PaperPhysicalAnnularMultiplierKernelBound =
  R76.round76PhysicalAnnularMultiplierKernelBound

round76PaperClayPromotion : Bool
round76PaperClayPromotion = R76.round76ClayPromotion

round76PaperLiteralNormalizedSquareChargeCompilerIsTrue :
  round76PaperLiteralNormalizedSquareChargeCompiler ≡ true
round76PaperLiteralNormalizedSquareChargeCompilerIsTrue = refl

round76PaperRouteBFinalAntichainContradictionCompilerIsTrue :
  round76PaperRouteBFinalAntichainContradictionCompiler ≡ true
round76PaperRouteBFinalAntichainContradictionCompilerIsTrue = refl

round76PaperSharpHHBadHeadroomCompilerIsTrue :
  round76PaperSharpHHBadHeadroomCompiler ≡ true
round76PaperSharpHHBadHeadroomCompilerIsTrue = refl

round76PaperClayPromotionIsFalse : round76PaperClayPromotion ≡ false
round76PaperClayPromotionIsFalse = refl
