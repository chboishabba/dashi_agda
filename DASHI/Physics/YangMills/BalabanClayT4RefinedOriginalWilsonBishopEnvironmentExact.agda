module DASHI.Physics.YangMills.BalabanClayT4RefinedOriginalWilsonBishopEnvironmentExact where

-- A real source-domain interface: the same selected Bishop sine-half
-- atoms enter the original four-dimensional Wilson denominator, but
-- their square intervals are dependency-aware, not naïve [a,b]*[a,b].
--
-- All four sine bounds are genuine propositions over the ACTUAL physical
-- Bishop values. They must be derived from the Machin Fourier atom
-- source. No fake sine data are constructed here. The result gives
-- sound original Wilson hatMomentumSquared(loopMomentum) intervals and
-- their strict rational endpoint positivity on every regular cell.
--
-- SHIFTED and EXTERNAL momentum atoms are left at their original
-- Canonical interval values; the theorem does NOT license dividing
-- by a shifted propagator without its own positive-denominator check.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (0ℚ; _<_)
import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4CanonicalBishopAtomEnvironmentExact as Canonical
import DASHI.Physics.YangMills.BalabanClayT4BishopFourCornerIntervalExact as Product
import DASHI.Physics.YangMills.BalabanClayT4BishopExpressionIntervalSemanticsExact as Sem
import DASHI.Physics.YangMills.BalabanClayT4RefinedSineSquareRegularBoxesExact as Square

record ActualSourceFourSineMembership
    (trig : Canonical.PhysicalTrigBoxData)
    (role : Eval.MomentumRole)
    (cell : Grid.GridCell4) : Set where
  field
    axis0RealSine :
      Product.BishopLiesIn
        (Canonical.sineHalfValue trig role Eval.axis0)
        (Square.sourceSineBox (Grid.c0 cell))
    axis1RealSine :
      Product.BishopLiesIn
        (Canonical.sineHalfValue trig role Eval.axis1)
        (Square.sourceSineBox (Grid.c1 cell))
    axis2RealSine :
      Product.BishopLiesIn
        (Canonical.sineHalfValue trig role Eval.axis2)
        (Square.sourceSineBox (Grid.c2 cell))
    axis3RealSine :
      Product.BishopLiesIn
        (Canonical.sineHalfValue trig role Eval.axis3)
        (Square.sourceSineBox (Grid.c3 cell))
open ActualSourceFourSineMembership public

fourPhysicalComponentSound :
  ∀ {trig role cell} →
  (source : ActualSourceFourSineMembership trig role cell) →
  Product.BishopLiesIn
    (Canonical.scaledSineSquareValue trig role Eval.axis0)
    (Square.sourceComponent (Grid.c0 cell))
fourPhysicalComponentSound source =
  Square.sourceComponentBishopSound _ (axis0RealSine source)

onePhysicalComponentSound :
  ∀ {trig role cell} →
  (source : ActualSourceFourSineMembership trig role cell) →
  Product.BishopLiesIn
    (Canonical.scaledSineSquareValue trig role Eval.axis1)
    (Square.sourceComponent (Grid.c1 cell))
onePhysicalComponentSound source =
  Square.sourceComponentBishopSound _ (axis1RealSine source)

twoPhysicalComponentSound :
  ∀ {trig role cell} →
  (source : ActualSourceFourSineMembership trig role cell) →
  Product.BishopLiesIn
    (Canonical.scaledSineSquareValue trig role Eval.axis2)
    (Square.sourceComponent (Grid.c2 cell))
twoPhysicalComponentSound source =
  Square.sourceComponentBishopSound _ (axis2RealSine source)

threePhysicalComponentSound :
  ∀ {trig role cell} →
  (source : ActualSourceFourSineMembership trig role cell) →
  Product.BishopLiesIn
    (Canonical.scaledSineSquareValue trig role Eval.axis3)
    (Square.sourceComponent (Grid.c3 cell))
threePhysicalComponentSound source =
  Square.sourceComponentBishopSound _ (axis3RealSine source)

originalWilsonHatSound :
  ∀ {trig role cell} →
  ActualSourceFourSineMembership trig role cell →
  Product.BishopLiesIn
    (Canonical.hatMomentumValue trig role)
    (Square.sourceWilsonDenominatorBox cell)
originalWilsonHatSound {trig} {role} source =
  let
    s0 = Canonical.scaledSineSquareValue trig role Eval.axis0
    s1 = Canonical.scaledSineSquareValue trig role Eval.axis1
    s2 = Canonical.scaledSineSquareValue trig role Eval.axis2
    s3 = Canonical.scaledSineSquareValue trig role Eval.axis3

    grouped = Sem.addIntervalBishopSound
      (Sem.addIntervalBishopSound
        (fourPhysicalComponentSound source)
        (onePhysicalComponentSound source))
      (Sem.addIntervalBishopSound
        (twoPhysicalComponentSound source)
        (threePhysicalComponentSound source))

    regroup : Canonical.hatMomentumValue trig role Bishop.≃
      ((s0 Bishop.+ s1) Bishop.+ (s2 Bishop.+ s3))
    regroup = BishopP.+-assoc (s0 Bishop.+ s1) s2 s3
  in
  Product.bishopLiesIn
    (BishopP.≤-respʳ-≃
      (BishopP.≃-symm regroup)
      (Product.lowerSound grouped))
    (BishopP.≤-respˡ-≃
      regroup
      (Product.upperSound grouped))

-- Override precisely ONE true original atom: the summed UNshifted
-- Wilson loop propagator symbol. Everything else remains the original
-- (potentially coarser) canonical certified physical atom interval.
refinedLoopAtomInterval :
  ∀ trig cell → Eval.TrigAtom → Eval.RationalInterval
refinedLoopAtomInterval trig cell
  (Eval.hatMomentumSquared Eval.loopMomentum) =
  Square.sourceWilsonDenominatorBox cell
refinedLoopAtomInterval trig cell atom =
  Canonical.canonicalAtomInterval trig atom

refinedLoopAtomSound :
  ∀ {trig cell} →
  ActualSourceFourSineMembership trig Eval.loopMomentum cell →
  ∀ atom →
  Product.BishopLiesIn
    (Canonical.canonicalAtomValue trig atom)
    (refinedLoopAtomInterval trig cell atom)
refinedLoopAtomSound source
  (Eval.hatMomentumSquared Eval.loopMomentum) =
  originalWilsonHatSound source
refinedLoopAtomSound {trig} source
  (Eval.hatMomentumSquared Eval.externalMomentum) =
  Canonical.canonicalAtomSound trig
    (Eval.hatMomentumSquared Eval.externalMomentum)
refinedLoopAtomSound {trig} source
  (Eval.hatMomentumSquared Eval.shiftedMomentum) =
  Canonical.canonicalAtomSound trig
    (Eval.hatMomentumSquared Eval.shiftedMomentum)
refinedLoopAtomSound {trig} source atom =
  Canonical.canonicalAtomSound trig atom

-- This is the same Bishop value function as the existing canonical
-- environment; only the correctly dependent interval for the original
-- unshifted Wilson denominator is sharpened.
refinedLoopBishopEnvironment :
  ∀ {trig cell} →
  ActualSourceFourSineMembership trig Eval.loopMomentum cell →
  Sem.BishopAtomEnvironment
refinedLoopBishopEnvironment {trig} {cell} source = record
  { Sem.BishopAtomEnvironment.atomValue = Canonical.canonicalAtomValue trig
  ; Sem.BishopAtomEnvironment.atomInterval = refinedLoopAtomInterval trig cell
  ; Sem.BishopAtomEnvironment.atomSound = refinedLoopAtomSound source
  }

refinedLoopDenominatorPositive :
  ∀ {trig cell} →
  ActualSourceFourSineMembership trig Eval.loopMomentum cell →
  Grid.allInner cell ≡ false →
  0ℚ < Eval.lower
    (refinedLoopAtomInterval trig cell
      (Eval.hatMomentumSquared Eval.loopMomentum))
refinedLoopDenominatorPositive {cell = cell} source regular =
  Square.sourceStrictPositiveAtRegularBox cell regular

-- Does NOT construct the source's actual Wilson bubble/tadpole/
-- ghost/Haar numerator AST or shifted-momentum sine enclosures.
