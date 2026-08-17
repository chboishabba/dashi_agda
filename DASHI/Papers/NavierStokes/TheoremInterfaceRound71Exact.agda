module DASHI.Papers.NavierStokes.TheoremInterfaceRound71Exact where

------------------------------------------------------------------------
-- PAPER-FACING ROUND71 DELTA
--
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- Author: Terence Tao.
-- Title: "Quantitative bounds for critically bounded solutions to the
-- Navier-Stokes equations".
-- DOI: 10.1090/PSPUM/104/01874.
-- Tao reports triple-exponential quantitative dependence on the critical L^3
-- bound.
--
-- Authors: Tobias Barker; Christophe Prange.
-- Title: "Quantitative Regularity for the Navier-Stokes Equations Via
-- Spatial Concentration".
-- DOI: 10.1007/s00220-021-04122-x.
--
-- Authors: Ruilin Hu; Phuoc-Tai Nguyen; Quoc-Hung Nguyen; Ping Zhang.
-- Title: "Quantitative bounds for bounded solutions to the Navier-Stokes
-- equations in endpoint critical Besov spaces".
-- arXiv DOI: 10.48550/arXiv.2411.06483.
-- Their abstract reports quadruple-exponential dependence on the Besov norm and
-- double-exponential dependence on the auxiliary L^p norm.
--
-- Authors: Jishan Fan; Song Jiang; Gen Nakamura; Yong Zhou.
-- Title: "Logarithmically Improved Regularity Criteria for the Navier-Stokes
-- and MHD Equations".
-- DOI: 10.1007/s00021-010-0039-5.
--
-- ROUND71 PAPER DELTA
--
-- Propagation side:
-- * Round70's one-event-per-depth dyadic no-go is not a no-go for dyadic LOSS
--   itself.  Round71 constructs a branching block whose descendant count
--   doubles while every floor halves; total guaranteed floor is exactly
--   conserved.
-- * Weighted branching has total floor exactly W at every depth, so W=E+1
--   exceeds any finite budget E.  Thus the physical discriminator is genuine
--   duplicate-free multiplicity TIMES per-descendant loss, not loss alone.
-- * No physical Navier-Stokes branching theorem is claimed yet.
--
-- Trajectory side:
-- * the old Assignment = CoordinateVariable -> Q carrier is formally rejected
--   as the finite cutoff Picard space: CoordinateVariable contains an injective
--   Nat-indexed family of Fourier slots, and Q is not the physical real field;
-- * a finite real canonical coordinate carrier is constructed with exactly six
--   Carrier F slots per retained canonical reality-orbit mode;
-- * literal physical TransverseModeCoefficient lists are encoded exactly into
--   those finite real slots, preserving the mode-slot order.
--
-- The remaining trajectory theorem is therefore narrower and more honest:
-- construct the canonical projected NS polynomial vector field on this finite
-- real carrier (or an equivalent transverse chart), prove local Lipschitz,
-- invoke finite-dimensional real Picard, and transport/invariantly retain the
-- transverse physical state.  Only then differentiate the localized identity.
--
-- Clay promotion remains false.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Papers.NavierStokes.TheoremInterfaceRound70Exact
import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound71Exact as R71

round71PaperBranchingCompensatesDyadicLoss : Bool
round71PaperBranchingCompensatesDyadicLoss =
  R71.round71BranchingCompensatesDyadicLossConstructed

round71PaperOldAssignmentNatInjectionConstructed : Bool
round71PaperOldAssignmentNatInjectionConstructed =
  R71.round71OldAssignmentNatInjectionConstructed

round71PaperFiniteRealCanonicalCarrierConstructed : Bool
round71PaperFiniteRealCanonicalCarrierConstructed =
  R71.round71FiniteRealCanonicalCarrierConstructed

round71PaperPhysicalToFiniteRealEncodingConstructed : Bool
round71PaperPhysicalToFiniteRealEncodingConstructed =
  R71.round71PhysicalToFiniteRealEncodingConstructed

round71PaperCanonicalPhysicalRHSActsOnFiniteRealCarrier : Bool
round71PaperCanonicalPhysicalRHSActsOnFiniteRealCarrier =
  R71.round71CanonicalPhysicalRHSActsOnFiniteRealCarrier

round71PaperSelectedGalerkinTrajectoryConstructed : Bool
round71PaperSelectedGalerkinTrajectoryConstructed =
  R71.round71SelectedGalerkinTrajectoryConstructed

round71PaperCriticalAmplificationForcesStructuredConcentration : Bool
round71PaperCriticalAmplificationForcesStructuredConcentration =
  R71.round71CriticalAmplificationForcesStructuredConcentration

round71PaperPhysicalDuplicateFreeDescendantsConstructed : Bool
round71PaperPhysicalDuplicateFreeDescendantsConstructed =
  R71.round71PhysicalPropagationProducesDuplicateFreeDescendants

round71PaperMultiplicityLossOutrunsBudget : Bool
round71PaperMultiplicityLossOutrunsBudget =
  R71.round71PhysicalMultiplicityLossBalanceOutrunsBudget

round71PaperCriticalRatioBarrier : Bool
round71PaperCriticalRatioBarrier = R71.round71CriticalRatioBarrierConstructed

round71PaperClayPromotion : Bool
round71PaperClayPromotion = R71.round71ClayPromotion

round71PaperBranchingCompensatesDyadicLossIsTrue :
  round71PaperBranchingCompensatesDyadicLoss ≡ true
round71PaperBranchingCompensatesDyadicLossIsTrue = refl

round71PaperOldAssignmentNatInjectionConstructedIsTrue :
  round71PaperOldAssignmentNatInjectionConstructed ≡ true
round71PaperOldAssignmentNatInjectionConstructedIsTrue = refl

round71PaperFiniteRealCanonicalCarrierConstructedIsTrue :
  round71PaperFiniteRealCanonicalCarrierConstructed ≡ true
round71PaperFiniteRealCanonicalCarrierConstructedIsTrue = refl

round71PaperPhysicalToFiniteRealEncodingConstructedIsTrue :
  round71PaperPhysicalToFiniteRealEncodingConstructed ≡ true
round71PaperPhysicalToFiniteRealEncodingConstructedIsTrue = refl

round71PaperCanonicalPhysicalRHSActsOnFiniteRealCarrierIsFalse :
  round71PaperCanonicalPhysicalRHSActsOnFiniteRealCarrier ≡ false
round71PaperCanonicalPhysicalRHSActsOnFiniteRealCarrierIsFalse = refl

round71PaperSelectedGalerkinTrajectoryConstructedIsFalse :
  round71PaperSelectedGalerkinTrajectoryConstructed ≡ false
round71PaperSelectedGalerkinTrajectoryConstructedIsFalse = refl

round71PaperCriticalAmplificationForcesStructuredConcentrationIsFalse :
  round71PaperCriticalAmplificationForcesStructuredConcentration ≡ false
round71PaperCriticalAmplificationForcesStructuredConcentrationIsFalse = refl

round71PaperMultiplicityLossOutrunsBudgetIsFalse :
  round71PaperMultiplicityLossOutrunsBudget ≡ false
round71PaperMultiplicityLossOutrunsBudgetIsFalse = refl

round71PaperCriticalRatioBarrierIsFalse :
  round71PaperCriticalRatioBarrier ≡ false
round71PaperCriticalRatioBarrierIsFalse = refl

round71PaperClayPromotionIsFalse : round71PaperClayPromotion ≡ false
round71PaperClayPromotionIsFalse = refl
