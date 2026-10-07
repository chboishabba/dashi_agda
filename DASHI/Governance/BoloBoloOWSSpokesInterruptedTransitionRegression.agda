module DASHI.Governance.BoloBoloOWSSpokesInterruptedTransitionRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.BoloBoloOWSSpokesInterruptedTransitionExact as Transition

firstSpokesDayPinned :
  Transition.firstSpokesCouncilDayNovember2011 Transition.canonicalTransitionWindow ≡ 7
firstSpokesDayPinned = refl

postDevelopmentRowsPinned :
  Transition.postTransitionDevelopmentRecordCount Transition.canonicalTransitionWindow ≡ 3
postDevelopmentRowsPinned = refl

postHoldoutPreserved :
  Transition.protectedHoldoutConsumed Transition.canonicalOWSSpokesTransitionBoundary ≡ false
postHoldoutPreserved = refl

postDelegateLexicalAggregatePinned :
  Transition.delegateParagraphs Transition.postSpokesDevelopmentLexicalAggregate ≡ 4
postDelegateLexicalAggregatePinned = refl

onlyOnePostDurationRow : Transition.postSpokesDurationRowCount ≡ 1
onlyOnePostDurationRow = refl

noCausalPromotion :
  Transition.lexicalBeforeAfterDifferenceIsCausalEffect Transition.canonicalOWSSpokesTransitionBoundary ≡ false
noCausalPromotion = refl
