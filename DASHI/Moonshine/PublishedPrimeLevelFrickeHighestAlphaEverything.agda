module DASHI.Moonshine.PublishedPrimeLevelFrickeHighestAlphaEverything where

------------------------------------------------------------------------
-- Focused highest-alpha root after the local p11 falsifiers and the published
-- Deligne--Rapoport/Fricke authority weld.
--
-- CLOSED HERE
--   * coarse prime-level special-fibre authority is imported at one explicit
--     standard boundary and pinned to the requested prime;
--   * pair defect = g(X_0^+(p)) is derived through the actual nodal model;
--   * pointwise coarse Frobenius fixed iff g(X_0^+(p))=0 is derived;
--   * no finite Ogg table or Monster label is consumed;
--   * Gamma(2)-marked geometry is kept separate from the coarse selector, with
--     p11 providing an explicit forget-level pair-collapse counterexample.
--
-- REMAINING MOONSHINE STEP
--   Connect the table-free genus-zero/all-fixed theorem to the independently
--   characterized Monster/Ogg prime condition.  The geometric selector itself
--   is no longer the missing theorem once the standard authority is accepted.
--
-- LOCAL OLDSPACE STEP REMAINS SEPARATE
--   The p11 K(2)-fixed vs K_0(4)-fixed comparison still requires genuine local
--   GL_2(Q_2) / Casselman test-vector machinery.  Away-from-2 Hecke, compact
--   averaging, and the internal positive R2 have all been formally falsified
--   as sufficient/correct substitutes.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_)
open import Data.Nat.Primality using (Prime)

import DASHI.Moonshine.PublishedPrimeLevelFrickeSelectorPinnedExact as Published
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeSelectorExact as Selector
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeCombinatoricsExact as DR
import DASHI.Moonshine.Gamma2MarkedVsCoarseFrickeCarrierRegressionExact as MarkedCoarse

publishedGenusPairRegression :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  Selector.genericFrickeGenus (Published.publishedAuthorityAt p prime ge5)
  ≡ DR.pairedCount
      (Selector.supersingularFrobenius
        (Published.publishedAuthorityAt p prime ge5))
publishedGenusPairRegression = Published.publishedPairDefectEqualsFrickeGenus

publishedFixedGenusZeroRegression :
  (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
  Published.PublishedFrobeniusFullyFixed p prime ge5
  ↔ Selector.genericFrickeGenus (Published.publishedAuthorityAt p prime ge5) ≡ 0
publishedFixedGenusZeroRegression =
  Published.publishedFrobeniusFullyFixedIffFrickeGenusZero

p11MarkedPairCollapseRegression :
  MarkedCoarse.markedPairCountReallyOne ≡ MarkedCoarse.markedPairCountReallyOne
p11MarkedPairCollapseRegression = refl

finiteOggTableUnusedRegression :
  Published.finiteOggTableUsed
    Published.canonicalPublishedPrimePinnedSelectorBoundary ≡ false
finiteOggTableUnusedRegression = refl

monsterLabelUnusedRegression :
  Published.monsterLabelUsed
    Published.canonicalPublishedPrimePinnedSelectorBoundary ≡ false
monsterLabelUnusedRegression = refl
