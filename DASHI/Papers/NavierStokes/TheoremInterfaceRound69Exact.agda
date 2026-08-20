module DASHI.Papers.NavierStokes.TheoremInterfaceRound69Exact where

------------------------------------------------------------------------
-- PAPER-FACING ROUND69 DELTA
--
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Luis Escauriaza; Gregory Seregin; Vladimir Sverak.
-- Title: "L3,infinity-solutions of the Navier-Stokes equations and backward
-- uniqueness".
-- DOI: 10.1070/RM2003v058n02ABEH000609.
--
-- Author: Terence Tao.
-- Title: "Quantitative bounds for critically bounded solutions to the
-- Navier-Stokes equations".
-- DOI: 10.1090/PSPUM/104/01874.
--
-- Authors: Tobias Barker; Christophe Prange.
-- Title: "Quantitative Regularity for the Navier-Stokes Equations Via
-- Spatial Concentration".
-- DOI: 10.1007/s00220-021-04122-x.
--
-- Authors: Luis Caffarelli; Robert Kohn; Louis Nirenberg.
-- Title: "Partial regularity of suitable weak solutions of the
-- Navier-Stokes equations".
-- DOI: 10.1002/cpa.3160350604.
--
-- Round69 changes proof priority.  The multiplier lane remains available, but
-- the decisive C1 test now comes first:
--
--   selected trajectory / literal localized PDE atom list
--     -> non-circular amplification remainder
--     -> positive structured triadic concentration
--     -> propagation/separation
--     -> finite funding contradiction / Xi barrier.
--
-- The amplification and finite-funding algebra are constructed.  The current
-- free-selector Round59 Duhamel interface is formally falsified as a physical
-- concentration authority.  The source authority used here is instead the
-- existing Round62 LocalizedPDEAtom list, which already carries physical source,
-- tail, kernel and classified boundary structure on one list.  Round69 defines
-- a nonnegative triadic concentration mass directly on those physical atoms.
--
-- Quantitative ESS/Tao/Barker-Prange machinery remains a conditional
-- propagation architecture: an ambient `forall n, Xi_n <= K` assumption is
-- literally the C1 target and is not imported as its proof.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Papers.NavierStokes.TheoremInterfaceRound67Exact
import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound69Exact as R69

round69PaperNonCircularAmplificationConstructed : Bool
round69PaperNonCircularAmplificationConstructed =
  R69.round69NonCircularCriticalAmplificationConstructed

round69PaperFiniteConcentrationFundingConstructed : Bool
round69PaperFiniteConcentrationFundingConstructed =
  R69.round69FiniteConcentrationFundingConstructed

round69PaperFreeDuhamelSelectorFalsified : Bool
round69PaperFreeDuhamelSelectorFalsified =
  R69.round69FreeDuhamelSelectorFalsified

round69PaperOneStructuredPDEAtomAuthorityConstructed : Bool
round69PaperOneStructuredPDEAtomAuthorityConstructed =
  R69.round69OneStructuredPDEAtomAuthorityConstructed

round69PaperStructuredTriadicConcentrationMassConstructed : Bool
round69PaperStructuredTriadicConcentrationMassConstructed =
  R69.round69StructuredTriadicConcentrationMassConstructed

round69PaperConditionalCriticalCircularityIdentified : Bool
round69PaperConditionalCriticalCircularityIdentified =
  R69.round69ConditionalCriticalCircularityIdentified

round69PaperOwnerLanguageCriticalBoundFalsified : Bool
round69PaperOwnerLanguageCriticalBoundFalsified =
  R69.round69OwnerLanguageCriticalBoundFalsified

round69PaperSelectedGalerkinTrajectoryConstructed : Bool
round69PaperSelectedGalerkinTrajectoryConstructed =
  R69.round69SelectedGalerkinTrajectoryConstructed

round69PaperLiteralTrajectoryEmitsStructuredAtoms : Bool
round69PaperLiteralTrajectoryEmitsStructuredAtoms =
  R69.round69LiteralTrajectoryEmitsStructuredAtoms

round69PaperCriticalAmplificationForcesStructuredConcentration : Bool
round69PaperCriticalAmplificationForcesStructuredConcentration =
  R69.round69CriticalAmplificationForcesStructuredConcentration

round69PaperNonCircularConcentrationPropagation : Bool
round69PaperNonCircularConcentrationPropagation =
  R69.round69NonCircularConcentrationPropagationConstructed

round69PaperPropagatedEventsFeedFiniteBudget : Bool
round69PaperPropagatedEventsFeedFiniteBudget =
  R69.round69PropagatedEventsFeedFiniteBudgetConstructed

round69PaperCriticalRatioBarrier : Bool
round69PaperCriticalRatioBarrier =
  R69.round69CriticalRatioBarrierConstructed

round69PaperClayPromotion : Bool
round69PaperClayPromotion = R69.round69ClayPromotion

round69PaperNonCircularAmplificationConstructedIsTrue :
  round69PaperNonCircularAmplificationConstructed ≡ true
round69PaperNonCircularAmplificationConstructedIsTrue = refl

round69PaperFiniteConcentrationFundingConstructedIsTrue :
  round69PaperFiniteConcentrationFundingConstructed ≡ true
round69PaperFiniteConcentrationFundingConstructedIsTrue = refl

round69PaperFreeDuhamelSelectorFalsifiedIsTrue :
  round69PaperFreeDuhamelSelectorFalsified ≡ true
round69PaperFreeDuhamelSelectorFalsifiedIsTrue = refl

round69PaperOneStructuredPDEAtomAuthorityConstructedIsTrue :
  round69PaperOneStructuredPDEAtomAuthorityConstructed ≡ true
round69PaperOneStructuredPDEAtomAuthorityConstructedIsTrue = refl

round69PaperStructuredTriadicConcentrationMassConstructedIsTrue :
  round69PaperStructuredTriadicConcentrationMassConstructed ≡ true
round69PaperStructuredTriadicConcentrationMassConstructedIsTrue = refl

round69PaperConditionalCriticalCircularityIdentifiedIsTrue :
  round69PaperConditionalCriticalCircularityIdentified ≡ true
round69PaperConditionalCriticalCircularityIdentifiedIsTrue = refl

round69PaperOwnerLanguageCriticalBoundFalsifiedIsTrue :
  round69PaperOwnerLanguageCriticalBoundFalsified ≡ true
round69PaperOwnerLanguageCriticalBoundFalsifiedIsTrue = refl

round69PaperSelectedGalerkinTrajectoryConstructedIsFalse :
  round69PaperSelectedGalerkinTrajectoryConstructed ≡ false
round69PaperSelectedGalerkinTrajectoryConstructedIsFalse = refl

round69PaperLiteralTrajectoryEmitsStructuredAtomsIsFalse :
  round69PaperLiteralTrajectoryEmitsStructuredAtoms ≡ false
round69PaperLiteralTrajectoryEmitsStructuredAtomsIsFalse = refl

round69PaperCriticalAmplificationForcesStructuredConcentrationIsFalse :
  round69PaperCriticalAmplificationForcesStructuredConcentration ≡ false
round69PaperCriticalAmplificationForcesStructuredConcentrationIsFalse = refl

round69PaperCriticalRatioBarrierIsFalse :
  round69PaperCriticalRatioBarrier ≡ false
round69PaperCriticalRatioBarrierIsFalse = refl

round69PaperClayPromotionIsFalse : round69PaperClayPromotion ≡ false
round69PaperClayPromotionIsFalse = refl
