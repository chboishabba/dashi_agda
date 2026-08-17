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
-- Round69 changes the proof priority.  The multiplier lane remains available,
-- but the decisive C1 test now comes first:
--
--   literal trajectory shell identity
--     -> non-circular amplification remainder
--     -> localized positive concentration
--     -> propagation/separation
--     -> finite funding contradiction/barrier.
--
-- The first and last algebraic implications are constructed.  The current
-- Duhamel selector interface is formally falsified as a physical concentration
-- authority and replaced upstream by a literal signed seven-source atom list.
-- A nonnegative frequency mass is constructed on actual physical triad
-- incidences.  What remains open is the new PDE inequality identifying excess
-- critical remainder with localized frequency/physical-space concentration and
-- propagating it without assuming the C1 bound itself.
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

round69PaperLiteralSignedShellSourceConstructed : Bool
round69PaperLiteralSignedShellSourceConstructed =
  R69.round69LiteralSignedShellSourceConstructed

round69PaperConditionalCriticalCircularityIdentified : Bool
round69PaperConditionalCriticalCircularityIdentified =
  R69.round69ConditionalCriticalCircularityIdentified

round69PaperLiteralFrequencyConcentrationMassConstructed : Bool
round69PaperLiteralFrequencyConcentrationMassConstructed =
  R69.round69LiteralFrequencyConcentrationMassConstructed

round69PaperRemainderForcesLocalizedConcentration : Bool
round69PaperRemainderForcesLocalizedConcentration =
  R69.round69RemainderForcesLocalizedFrequencyConcentration

round69PaperNonCircularConcentrationPropagation : Bool
round69PaperNonCircularConcentrationPropagation =
  R69.round69NonCircularConcentrationPropagationConstructed

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

round69PaperLiteralSignedShellSourceConstructedIsTrue :
  round69PaperLiteralSignedShellSourceConstructed ≡ true
round69PaperLiteralSignedShellSourceConstructedIsTrue = refl

round69PaperConditionalCriticalCircularityIdentifiedIsTrue :
  round69PaperConditionalCriticalCircularityIdentified ≡ true
round69PaperConditionalCriticalCircularityIdentifiedIsTrue = refl

round69PaperLiteralFrequencyConcentrationMassConstructedIsTrue :
  round69PaperLiteralFrequencyConcentrationMassConstructed ≡ true
round69PaperLiteralFrequencyConcentrationMassConstructedIsTrue = refl

round69PaperRemainderForcesLocalizedConcentrationIsFalse :
  round69PaperRemainderForcesLocalizedConcentration ≡ false
round69PaperRemainderForcesLocalizedConcentrationIsFalse = refl

round69PaperCriticalRatioBarrierIsFalse :
  round69PaperCriticalRatioBarrier ≡ false
round69PaperCriticalRatioBarrierIsFalse = refl

round69PaperClayPromotionIsFalse : round69PaperClayPromotion ≡ false
round69PaperClayPromotionIsFalse = refl
