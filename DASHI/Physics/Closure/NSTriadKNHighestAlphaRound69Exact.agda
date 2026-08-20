module DASHI.Physics.Closure.NSTriadKNHighestAlphaRound69Exact where

------------------------------------------------------------------------
-- ROUND 69 HIGHEST-ALPHA CUTSET
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
-- ROUND69 RESULT
--
-- The critical-ratio route is now tested before further B/E polishing.
--
-- CONSTRUCTED:
--
-- 1. On the canonical Xi_n carrier, excess amplification beyond a SAME-OBJECT
--    inherited allowance forces an equally large one-step remainder, with no
--    ambient hypothesis Xi_n <= K.
--
-- 2. A finite list of separated concentration events, each carrying at least
--    mu charge, consumes at least the recursively accumulated N*mu funding
--    cost.  If total charge is bounded by a finite energy budget, so is this
--    minimum funding cost.
--
-- 3. The existing Round59 PhysicalLocalizedDuhamelSource is formally too weak
--    for physical concentration: the same physical shell data and identical
--    trajectory authority admit generatedSelector constantly 0 or constantly
--    1.  Thus generatedAt is not yet a physical observable.
--
-- 4. Round62 already provides the correct source authority:
--    LocalizedPDEAtom, one list carrying physical interior cells, tail,
--    duplicate/cancelling/independent kernel atoms and classified boundaries.
--    It derives the kernel residual and boundary ledger from that same list.
--
-- 5. Round69 defines a nonnegative triadic concentration mass DIRECTLY on that
--    one structured PDE list.  Only literal triadic physicalAtom values enter;
--    Com, tail, kernel and boundary atoms are not silently reclassified as
--    concentration.  Each triadic cell retains its PhysicalTriadIncidence.
--
-- 6. The ambient critical hypothesis used by quantitative ESS/Tao/Barker-
--    Prange style propagation is literally the Round63 C1 target
--
--         forall n, Xi_n <= K.
--
--    Therefore that literature is a propagation architecture/lemma mine, not
--    an unconditional producer of C1.
--
-- 7. Round63 already proves the owner carrier alone admits
--    integralCritical=K+1 for every candidate K.  Hence the new concentration
--    inequality MUST use selected-solution/localized-PDE coupling; it cannot be
--    derived from the owner language or renamed critical-bound assumptions.
--
-- NEW SHORTEST FRONTIER:
--
-- A. construct the selected finite Galerkin trajectory and make its literal
--    localized identity EMIT the existing Round62 LocalizedPDEAtom list;
-- B. prove CriticalAmplificationForcesConcentration on that same object:
--    excess Xi remainder forces a positive lower bound on
--    triadicConcentrationMass in a controlled subfibre, without Xi<=K;
-- C. convert/propagate that concentration through a physical-space periodic
--    analogue of the ESS/Tao/Barker-Prange mechanism, again without consuming
--    the C1 target as an ambient premise;
-- D. prove the propagated events are sufficiently separated/duplicate-free to
--    feed the finite funding theorem and obtain an invariant Xi barrier;
-- E. only then return to the remaining Gram/HH-bad/data/kernel/gate closures.
--
-- Clay promotion is intentionally false.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound67Exact
import DASHI.Physics.Closure.NSTriadKNFourierStrainFirstVariationFrobeniusRound68Exact
import DASHI.Physics.Closure.NSTriadKNCriticalAmplificationForcesRemainderRound69Exact as Amplification
import DASHI.Physics.Closure.NSTriadKNFiniteDisjointConcentrationBudgetRound69Exact as Funding
import DASHI.Physics.Closure.NSTriadKNPhysicalDuhamelSelectorUnderdeterminationRound69Exact as SelectorNoGo
import DASHI.Physics.Closure.NSTriadKNLocalizedPDEStructuredAtomsRound62Exact as Structured
import DASHI.Physics.Closure.NSTriadKNLocalizedPDETriadicConcentrationMassRound69Exact as StructuredMass
import DASHI.Physics.Closure.NSTriadKNCriticalAmbientBoundIdentityRound69Exact as Ambient
import DASHI.Physics.Closure.NSTriadKNCriticalOwnerLanguageUniformBoundNoGoRound63Exact as OwnerNoGo

round69NonCircularCriticalAmplificationConstructed : Bool
round69NonCircularCriticalAmplificationConstructed =
  Amplification.round69CriticalAmplificationAlternativeConstructed

round69FiniteConcentrationFundingConstructed : Bool
round69FiniteConcentrationFundingConstructed =
  Funding.round69FiniteConcentrationFundingConstructed

round69FreeDuhamelSelectorFalsified : Bool
round69FreeDuhamelSelectorFalsified =
  SelectorNoGo.sameTrajectoryFreeGeneratedSelectorFalsifier

round69OneStructuredPDEAtomAuthorityConstructed : Bool
round69OneStructuredPDEAtomAuthorityConstructed =
  Structured.structuredAtomsDeriveKernelResidualAndBoundaryLedger

round69StructuredTriadicConcentrationMassConstructed : Bool
round69StructuredTriadicConcentrationMassConstructed =
  StructuredMass.round69StructuredTriadicConcentrationMassConstructed

round69ConditionalCriticalCircularityIdentified : Bool
round69ConditionalCriticalCircularityIdentified =
  Ambient.round69AmbientCriticalHypothesisIsExactlyC1

round69OwnerLanguageCriticalBoundFalsified : Bool
round69OwnerLanguageCriticalBoundFalsified =
  OwnerNoGo.round63C1CannotComeFromOwnerLanguageAlone

-- Genuine remaining physical producers.
round69SelectedGalerkinTrajectoryConstructed : Bool
round69SelectedGalerkinTrajectoryConstructed = false

round69LiteralTrajectoryEmitsStructuredAtoms : Bool
round69LiteralTrajectoryEmitsStructuredAtoms = false

round69CriticalAmplificationForcesStructuredConcentration : Bool
round69CriticalAmplificationForcesStructuredConcentration = false

round69FrequencyToPhysicalSpaceConcentrationConstructed : Bool
round69FrequencyToPhysicalSpaceConcentrationConstructed = false

round69NonCircularConcentrationPropagationConstructed : Bool
round69NonCircularConcentrationPropagationConstructed = false

round69PropagatedEventsFeedFiniteBudgetConstructed : Bool
round69PropagatedEventsFeedFiniteBudgetConstructed = false

round69CriticalRatioBarrierConstructed : Bool
round69CriticalRatioBarrierConstructed = false

round69ClayPromotion : Bool
round69ClayPromotion = false

round69NonCircularCriticalAmplificationConstructedIsTrue :
  round69NonCircularCriticalAmplificationConstructed ≡ true
round69NonCircularCriticalAmplificationConstructedIsTrue = refl

round69FiniteConcentrationFundingConstructedIsTrue :
  round69FiniteConcentrationFundingConstructed ≡ true
round69FiniteConcentrationFundingConstructedIsTrue = refl

round69FreeDuhamelSelectorFalsifiedIsTrue :
  round69FreeDuhamelSelectorFalsified ≡ true
round69FreeDuhamelSelectorFalsifiedIsTrue = refl

round69OneStructuredPDEAtomAuthorityConstructedIsTrue :
  round69OneStructuredPDEAtomAuthorityConstructed ≡ true
round69OneStructuredPDEAtomAuthorityConstructedIsTrue = refl

round69StructuredTriadicConcentrationMassConstructedIsTrue :
  round69StructuredTriadicConcentrationMassConstructed ≡ true
round69StructuredTriadicConcentrationMassConstructedIsTrue = refl

round69ConditionalCriticalCircularityIdentifiedIsTrue :
  round69ConditionalCriticalCircularityIdentified ≡ true
round69ConditionalCriticalCircularityIdentifiedIsTrue = refl

round69OwnerLanguageCriticalBoundFalsifiedIsTrue :
  round69OwnerLanguageCriticalBoundFalsified ≡ true
round69OwnerLanguageCriticalBoundFalsifiedIsTrue = refl

round69SelectedGalerkinTrajectoryConstructedIsFalse :
  round69SelectedGalerkinTrajectoryConstructed ≡ false
round69SelectedGalerkinTrajectoryConstructedIsFalse = refl

round69LiteralTrajectoryEmitsStructuredAtomsIsFalse :
  round69LiteralTrajectoryEmitsStructuredAtoms ≡ false
round69LiteralTrajectoryEmitsStructuredAtomsIsFalse = refl

round69CriticalAmplificationForcesStructuredConcentrationIsFalse :
  round69CriticalAmplificationForcesStructuredConcentration ≡ false
round69CriticalAmplificationForcesStructuredConcentrationIsFalse = refl

round69CriticalRatioBarrierConstructedIsFalse :
  round69CriticalRatioBarrierConstructed ≡ false
round69CriticalRatioBarrierConstructedIsFalse = refl

round69ClayPromotionIsFalse : round69ClayPromotion ≡ false
round69ClayPromotionIsFalse = refl
