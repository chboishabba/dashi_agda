module DASHI.Physics.YangMills.BalabanLiteralOriginalGridDenominatorMaskExact where

-- Source-identical 4^4 generated grid: each regular cell has a positive
-- rational rank lower bound. No external trig bound or source formula is
-- smuggled into this finite combinatorial proof.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Agda.Builtin.Unit using (tt)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_; _<_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanLiteralRankAwareDenominatorRationalBoundsExact as Rank

sourceOuter : Grid.IntervalCell → Bool
sourceOuter Grid.negativeOuter = true
sourceOuter Grid.negativeInner = false
sourceOuter Grid.positiveInner = false
sourceOuter Grid.positiveOuter = true

sourceRankLower : Grid.GridCell4 → ℚ
sourceRankLower cell = Rank.rankMaskLower
  (sourceOuter (Grid.c0 cell)) (sourceOuter (Grid.c1 cell))
  (sourceOuter (Grid.c2 cell)) (sourceOuter (Grid.c3 cell))

-- The original 256 generated cells, no surrogate support representation.
-- For the 16 all-inner configurations, the hypothesis regular ≡ false
-- is definitionally impossible. For each of the 240 regular boxes the
-- inequality is a decision-procedure-certified exact rational comparison.
sourceRegularRankAtLeastTwo :
  (cell : Grid.GridCell4) →
  Grid.allInner cell ≡ false →
  Rank.two ≤ sourceRankLower cell
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.negativeOuter Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.negativeOuter Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.negativeOuter Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.negativeOuter Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.negativeInner Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.negativeInner Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.negativeInner Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.negativeInner Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.positiveInner Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.positiveInner Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.positiveInner Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.positiveInner Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.positiveOuter Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.positiveOuter Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.positiveOuter Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.negativeOuter Grid.positiveOuter Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.negativeOuter Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.negativeOuter Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.negativeOuter Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.negativeOuter Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.negativeInner Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.negativeInner Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.negativeInner Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.negativeInner Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.positiveInner Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.positiveInner Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.positiveInner Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.positiveInner Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.positiveOuter Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.positiveOuter Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.positiveOuter Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.negativeInner Grid.positiveOuter Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.negativeOuter Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.negativeOuter Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.negativeOuter Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.negativeOuter Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.negativeInner Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.negativeInner Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.negativeInner Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.negativeInner Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.positiveInner Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.positiveInner Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.positiveInner Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.positiveInner Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.positiveOuter Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.positiveOuter Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.positiveOuter Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.positiveInner Grid.positiveOuter Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.negativeOuter Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.negativeOuter Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.negativeOuter Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.negativeOuter Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.negativeInner Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.negativeInner Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.negativeInner Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.negativeInner Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.positiveInner Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.positiveInner Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.positiveInner Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.positiveInner Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.positiveOuter Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.positiveOuter Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.positiveOuter Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeOuter Grid.positiveOuter Grid.positiveOuter Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.negativeOuter Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.negativeOuter Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.negativeOuter Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.negativeOuter Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.negativeInner Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.negativeInner Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.negativeInner Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.negativeInner Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.positiveInner Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.positiveInner Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.positiveInner Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.positiveInner Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.positiveOuter Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.positiveOuter Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.positiveOuter Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.negativeOuter Grid.positiveOuter Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeOuter Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeOuter Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeOuter Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeOuter Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeInner Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeInner Grid.negativeInner) ()
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeInner Grid.positiveInner) ()
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.negativeInner Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveInner Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveInner Grid.negativeInner) ()
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveInner Grid.positiveInner) ()
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveInner Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveOuter Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveOuter Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveOuter Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.negativeInner Grid.positiveOuter Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeOuter Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeOuter Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeOuter Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeOuter Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeInner Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeInner Grid.negativeInner) ()
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeInner Grid.positiveInner) ()
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.negativeInner Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveInner Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveInner Grid.negativeInner) ()
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveInner Grid.positiveInner) ()
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveInner Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveOuter Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveOuter Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveOuter Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.positiveInner Grid.positiveOuter Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.negativeOuter Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.negativeOuter Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.negativeOuter Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.negativeOuter Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.negativeInner Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.negativeInner Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.negativeInner Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.negativeInner Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.positiveInner Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.positiveInner Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.positiveInner Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.positiveInner Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.positiveOuter Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.positiveOuter Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.positiveOuter Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.negativeInner Grid.positiveOuter Grid.positiveOuter Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.negativeOuter Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.negativeOuter Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.negativeOuter Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.negativeOuter Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.negativeInner Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.negativeInner Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.negativeInner Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.negativeInner Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.positiveInner Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.positiveInner Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.positiveInner Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.positiveInner Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.positiveOuter Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.positiveOuter Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.positiveOuter Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.negativeOuter Grid.positiveOuter Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeOuter Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeOuter Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeOuter Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeOuter Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeInner Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeInner Grid.negativeInner) ()
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeInner Grid.positiveInner) ()
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.negativeInner Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveInner Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveInner Grid.negativeInner) ()
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveInner Grid.positiveInner) ()
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveInner Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveOuter Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveOuter Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveOuter Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.negativeInner Grid.positiveOuter Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeOuter Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeOuter Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeOuter Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeOuter Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeInner Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeInner Grid.negativeInner) ()
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeInner Grid.positiveInner) ()
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.negativeInner Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveInner Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveInner Grid.negativeInner) ()
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveInner Grid.positiveInner) ()
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveInner Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveOuter Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveOuter Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveOuter Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveOuter Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.negativeOuter Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.negativeOuter Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.negativeOuter Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.negativeOuter Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.negativeInner Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.negativeInner Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.negativeInner Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.negativeInner Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.positiveInner Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.positiveInner Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.positiveInner Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.positiveInner Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.positiveOuter Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.positiveOuter Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.positiveOuter Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveInner Grid.positiveOuter Grid.positiveOuter Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.negativeOuter Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.negativeOuter Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.negativeOuter Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.negativeOuter Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.negativeInner Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.negativeInner Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.negativeInner Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.negativeInner Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.positiveInner Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.positiveInner Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.positiveInner Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.positiveInner Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.positiveOuter Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.positiveOuter Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.positiveOuter Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.negativeOuter Grid.positiveOuter Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.negativeOuter Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.negativeOuter Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.negativeOuter Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.negativeOuter Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.negativeInner Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.negativeInner Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.negativeInner Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.negativeInner Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.positiveInner Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.positiveInner Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.positiveInner Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.positiveInner Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.positiveOuter Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.positiveOuter Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.positiveOuter Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.negativeInner Grid.positiveOuter Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.negativeOuter Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.negativeOuter Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.negativeOuter Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.negativeOuter Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.negativeInner Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.negativeInner Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.negativeInner Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.negativeInner Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.positiveInner Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.positiveInner Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.positiveInner Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.positiveInner Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.positiveOuter Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.positiveOuter Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.positiveOuter Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.positiveInner Grid.positiveOuter Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.negativeOuter Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.negativeOuter Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.negativeOuter Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.negativeOuter Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.negativeInner Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.negativeInner Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.negativeInner Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.negativeInner Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.positiveInner Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.positiveInner Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.positiveInner Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.positiveInner Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.positiveOuter Grid.negativeOuter) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.positiveOuter Grid.negativeInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.positiveOuter Grid.positiveInner) _ = ℚP.≤ᵇ⇒≤ tt
sourceRegularRankAtLeastTwo (Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter Grid.positiveOuter Grid.positiveOuter) _ = ℚP.≤ᵇ⇒≤ tt

-- This is the exact bridge from the 240 geometrically regular boxes
-- to the source-normalized four-axis rational lower enclosures.
-- Its hypotheses are the four ORIGINAL per-axis interval certificates.
-- They are not provided by the combinatorial partition alone.
record SourceAxisEnclosures (cell : Grid.GridCell4) : Set where
  field
    q0 q1 q2 q3 : ℚ
    q0Lower : Rank.axisLower (sourceOuter (Grid.c0 cell)) ≤ q0
    q1Lower : Rank.axisLower (sourceOuter (Grid.c1 cell)) ≤ q1
    q2Lower : Rank.axisLower (sourceOuter (Grid.c2 cell)) ≤ q2
    q3Lower : Rank.axisLower (sourceOuter (Grid.c3 cell)) ≤ q3

open SourceAxisEnclosures public

sourceAllFourAxisBound :
  (cell : Grid.GridCell4) →
  (receipt : SourceAxisEnclosures cell) →
  sourceRankLower cell ≤ Rank.sumFour
    (q0 receipt) (q1 receipt) (q2 receipt) (q3 receipt)
sourceAllFourAxisBound cell receipt =
  Rank.allMasksFourAxisLowerBound
    (sourceOuter (Grid.c0 cell)) (sourceOuter (Grid.c1 cell))
    (sourceOuter (Grid.c2 cell)) (sourceOuter (Grid.c3 cell))
    (q0Lower receipt) (q1Lower receipt)
    (q2Lower receipt) (q3Lower receipt)

sourceAllRegularAxisBound :
  (cell : Grid.GridCell4) →
  Grid.allInner cell ≡ false →
  (receipt : SourceAxisEnclosures cell) →
  Rank.two ≤ Rank.sumFour
    (q0 receipt) (q1 receipt) (q2 receipt) (q3 receipt)
sourceAllRegularAxisBound cell regular receipt =
  ℚP.≤-trans
    (sourceRegularRankAtLeastTwo cell regular)
    (sourceAllFourAxisBound cell receipt)

-- To inhabit the actual physical propagator certificate, establish:
-- q_i ≡ the lower endpoint of the original source's ith sine-square
-- contribution and its normalized-momentum trigonometric enclosure.
-- Then use sourceAllRegularAxisBound and the 0 < 2 rational theorem.

-- Turn the source-generated rank floor into STRICT positive rational
-- positivity without postulating any real analytic sine theorem.
sourceTwoStrictlyPositive : 0ℚ < Rank.two
sourceTwoStrictlyPositive = ℚP.positive⁻¹ Rank.two

sourceRegularRankStrictlyPositive :
  (cell : Grid.GridCell4) →
  Grid.allInner cell ≡ false →
  0ℚ < sourceRankLower cell
sourceRegularRankStrictlyPositive cell regular =
  ℚP.<-≤-trans sourceTwoStrictlyPositive
    (sourceRegularRankAtLeastTwo cell regular)

sourceSummedAxisStrictlyPositive :
  (cell : Grid.GridCell4) →
  Grid.allInner cell ≡ false →
  (receipt : SourceAxisEnclosures cell) →
  0ℚ < Rank.sumFour
    (q0 receipt) (q1 receipt) (q2 receipt) (q3 receipt)
sourceSummedAxisStrictlyPositive cell regular receipt =
  ℚP.<-≤-trans sourceTwoStrictlyPositive
    (sourceAllRegularAxisBound cell regular receipt)

-- Same ORIGINAL Typed division target, once the original source AST
-- has been shown to yield exactly the sum of those four axis bounds.
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4TypedRationalExpressionIntervalExact as Typed

record SourceDenominatorAdmission (cell : Grid.GridCell4) : Set where
  field
    sourceAxes : SourceAxisEnclosures cell
    sourceDenominator : Eval.RationalInterval
    denominatorLowerSameSource :
      Eval.lower sourceDenominator ≡
      Rank.sumFour
        (q0 sourceAxes) (q1 sourceAxes)
        (q2 sourceAxes) (q3 sourceAxes)
open SourceDenominatorAdmission public

admittedPhysicalDenominatorPositive :
  (cell : Grid.GridCell4) →
  Grid.allInner cell ≡ false →
  (receipt : SourceDenominatorAdmission cell) →
  0ℚ < Eval.lower (sourceDenominator receipt)
admittedPhysicalDenominatorPositive cell regular receipt =
  subst (λ x → 0ℚ < x)
    (sym (denominatorLowerSameSource receipt))
    (sourceSummedAxisStrictlyPositive cell regular (sourceAxes receipt))

admittedTypedPositiveDivision :
  (cell : Grid.GridCell4) →
  Grid.allInner cell ≡ false →
  (receipt : SourceDenominatorAdmission cell) →
  Eval.RationalInterval →
  Eval.RationalInterval
admittedTypedPositiveDivision cell regular receipt numerator =
  Typed.divideInterval numerator (sourceDenominator receipt)
    (admittedPhysicalDenominatorPositive cell regular receipt)

-- The SourceDenominatorAdmission object is NOT constructed here:
-- it requires actual source trig intervals and AST equality. This
-- function only shows the physical positivity certificate is exactly
-- sufficient to call the existing proof-requiring typed backend.
