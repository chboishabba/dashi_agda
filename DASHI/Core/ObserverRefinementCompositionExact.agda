module DASHI.Core.ObserverRefinementCompositionExact where

------------------------------------------------------------------------
-- STRICTNESS PROPAGATES UPWARD THROUGH REFINEMENT
--
-- Once a concrete collision has been split at one stage of a refinement
-- ladder, every later genuine refinement retains that split.  This lets a
-- source-native falsifier witness survive without being rebuilt at each later
-- observer stage.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ObserverFactorizedRefinementExact as Factorized
import DASHI.Core.ObserverRefinementLatticeExact as Observer

composeRefines :
  ∀ {State Coarse Middle Fine : Set}
    {coarse : Observer.Observer State Coarse}
    {middle : Observer.Observer State Middle}
    {fine : Observer.Observer State Fine} →
  Observer.Refines coarse middle →
  Observer.Refines middle fine →
  Observer.Refines coarse fine
composeRefines coarseMiddle middleFine x y sameFine =
  coarseMiddle x y (middleFine x y sameFine)

strictRefinementPersistsUpward :
  ∀ {State Coarse Middle Fine : Set}
    {coarse : Observer.Observer State Coarse}
    {middle : Observer.Observer State Middle}
    {fine : Observer.Observer State Fine} →
  Observer.StrictRefinement coarse middle →
  Observer.Refines middle fine →
  Observer.StrictRefinement coarse fine
strictRefinementPersistsUpward strict middleFine =
  Observer.strictRefinement
    (composeRefines (Observer.refinementLaw strict) middleFine)
    (Observer.refinementLeft strict)
    (Observer.refinementRight strict)
    (Observer.refinementCoarseCollision strict)
    (λ sameFine →
      Observer.refinementFineSeparates strict
        (middleFine
          (Observer.refinementLeft strict)
          (Observer.refinementRight strict)
          sameFine))

strictRefinementPersistsThroughFactorizedStage :
  ∀ {State Coarse Middle Fine : Set}
    {coarse : Observer.Observer State Coarse}
    {middle : Observer.Observer State Middle}
    {fine : Observer.Observer State Fine} →
  Observer.StrictRefinement coarse middle →
  Factorized.FactorizedRefinement middle fine →
  Observer.StrictRefinement coarse fine
strictRefinementPersistsThroughFactorizedStage strict factorized =
  strictRefinementPersistsUpward
    strict
    (Factorized.factorizedRefinementImpliesRefines factorized)

composeFamilyRefines :
  ∀ {State Value : Set}
    {coarse middle fine : Observer.ObserverFamily State Value} →
  Observer.FamilyRefines coarse middle →
  Observer.FamilyRefines middle fine →
  Observer.FamilyRefines coarse fine
composeFamilyRefines coarseMiddle middleFine x y sameFine =
  coarseMiddle x y (middleFine x y sameFine)

strictFamilyRefinementPersistsUpward :
  ∀ {State Value : Set}
    {coarse middle fine : Observer.ObserverFamily State Value} →
  Observer.StrictFamilyRefinement coarse middle →
  Observer.FamilyRefines middle fine →
  Observer.StrictFamilyRefinement coarse fine
strictFamilyRefinementPersistsUpward strict middleFine =
  Observer.strictFamilyRefinement
    (composeFamilyRefines (Observer.familyRefinementLaw strict) middleFine)
    (Observer.familyLeft strict)
    (Observer.familyRight strict)
    (Observer.familyCoarseCollision strict)
    (λ sameFine →
      Observer.familyFineSeparates strict
        (middleFine
          (Observer.familyLeft strict)
          (Observer.familyRight strict)
          sameFine))

record ObserverRefinementCompositionBoundary : Set where
  constructor observerRefinementCompositionBoundary
  field
    refinementIsTransitive : Bool
    refinementIsTransitiveIsTrue : refinementIsTransitive ≡ true
    onceSplitAlwaysSplitUnderRefinement : Bool
    onceSplitAlwaysSplitUnderRefinementIsTrue :
      onceSplitAlwaysSplitUnderRefinement ≡ true
    laterRefinementProvesEarlierCoarseWasGloballyBad : Bool
    laterRefinementProvesEarlierCoarseWasGloballyBadIsFalse :
      laterRefinementProvesEarlierCoarseWasGloballyBad ≡ false

canonicalObserverRefinementCompositionBoundary :
  ObserverRefinementCompositionBoundary
canonicalObserverRefinementCompositionBoundary =
  observerRefinementCompositionBoundary true refl true refl false refl
