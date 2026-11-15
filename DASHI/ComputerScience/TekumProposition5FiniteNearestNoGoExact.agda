module DASHI.ComputerScience.TekumProposition5FiniteNearestNoGoExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Rational.Base as ℚ using (ℚ; _-_; _≤_; _<_; ∣_∣; _/_)
import Data.Rational.Properties as ℚP
open ℚP using (_<?_)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Relation.Nullary.Negation.Core using (¬_)

import DASHI.Algebra.Trit as Trit
import DASHI.ComputerScience.TekumAnchorCodecExact as Anchor
import DASHI.ComputerScience.TekumExactTriadicSemanticsExact as Exact
import DASHI.ComputerScience.TekumFiniteSemanticsExact as Sem
import DASHI.ComputerScience.TekumFixedWidthBalancedArithmeticExact as Fixed
import DASHI.ComputerScience.TekumSourceAnchorCenterExact as Center
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source
import DASHI.ComputerScience.TekumSpecialValuesExact as Special
import DASHI.ComputerScience.TekumTruncationRoundingExact as Truncate

------------------------------------------------------------------------
-- PROPOSITION 5: FINITE-DOMAIN NEAREST-ROUNDING NO-GO
--
-- The earlier boundary owner shows that unrestricted raw 10 -> 8 truncation
-- can land on NaR/infinity.  Finite closure does NOT repair the proposition.
-- This owner gives a stronger ordinary -> ordinary counterexample using only
-- the repository's exact source decoder.
--
-- Source word (LST first) has centered integer code +13669 and exact value
--
--     1094 / 2187.
--
-- Raw Definition-7 anchor truncation/inversion lands at the ordinary 8-trit
-- word with value
--
--     122 / 243 = 1098 / 2187,
--
-- while the adjacent ordinary 8-trit competitor has value
--
--     364 / 729 = 1092 / 2187.
--
-- Therefore the raw target is distance 4/2187 from the source whereas the
-- competitor is distance 2/2187.  The raw target is strictly NOT nearest even
-- though source, target and competitor are all ordinary finite values.
--
-- This is stronger than the endpoint NaR/infinity obstruction: it rules out
-- the proposed repair "restrict Proposition 5 to raw truncations that remain
-- finite" without making any appeal to special-value semantics.
------------------------------------------------------------------------

finiteNearestCounterexample10 : Vec Trit.Trit 10
finiteNearestCounterexample10 =
  Trit.pos ∷ Trit.neg ∷ Trit.pos ∷ Trit.neg ∷ Trit.pos ∷
  Trit.neg ∷ Trit.pos ∷ Trit.zer ∷ Trit.neg ∷ Trit.pos ∷ []

finiteNearestRawTarget8 : Vec Trit.Trit 8
finiteNearestRawTarget8 =
  Trit.pos ∷ Trit.neg ∷ Trit.pos ∷ Trit.neg ∷
  Trit.pos ∷ Trit.zer ∷ Trit.neg ∷ Trit.pos ∷ []

finiteNearestCompetitor8 : Vec Trit.Trit 8
finiteNearestCompetitor8 =
  Trit.zer ∷ Trit.neg ∷ Trit.pos ∷ Trit.neg ∷
  Trit.pos ∷ Trit.zer ∷ Trit.neg ∷ Trit.pos ∷ []

sourceIsOrdinary :
  Special.classifySpecial finiteNearestCounterexample10 ≡ nothing
sourceIsOrdinary = refl

targetIsOrdinary :
  Special.classifySpecial finiteNearestRawTarget8 ≡ nothing
targetIsOrdinary = refl

competitorIsOrdinary :
  Special.classifySpecial finiteNearestCompetitor8 ≡ nothing
competitorIsOrdinary = refl

counterexampleAnchor10 : Vec Trit.Trit 10
counterexampleAnchor10 = Fixed.concreteAnchor finiteNearestCounterexample10

counterexampleTruncatedAnchor8 : Vec Trit.Trit 8
counterexampleTruncatedAnchor8 = Truncate.truncateTwo counterexampleAnchor10

counterexampleRawRounded8 : Vec Trit.Trit 8
counterexampleRawRounded8 =
  Fixed.addWord counterexampleTruncatedAnchor8 (Center.sourceAnchorCenterWord 8)

rawTruncationActuallySelectsTarget :
  counterexampleRawRounded8 ≡ finiteNearestRawTarget8
rawTruncationActuallySelectsTarget = refl

sourceOrdinary : Sem.OrdinaryTekum
sourceOrdinary =
  Sem.ordinaryTekum
    Anchor.positiveSign
    (Sem.nonnegative 0)
    (Sem.negative 1093)
    7

targetOrdinary : Sem.OrdinaryTekum
targetOrdinary =
  Sem.ordinaryTekum
    Anchor.positiveSign
    (Sem.nonnegative 0)
    (Sem.negative 121)
    5

competitorOrdinary : Sem.OrdinaryTekum
competitorOrdinary =
  Sem.ordinaryTekum
    Anchor.positiveSign
    (Sem.negative 1)
    (Sem.nonnegative 121)
    5

sourceDecoderSameObject :
  Source.parseTekumWord finiteNearestCounterexample10
  ≡ just (Sem.ordinary sourceOrdinary)
sourceDecoderSameObject = refl

targetDecoderSameObject :
  Source.parseTekumWord finiteNearestRawTarget8
  ≡ just (Sem.ordinary targetOrdinary)
targetDecoderSameObject = refl

competitorDecoderSameObject :
  Source.parseTekumWord finiteNearestCompetitor8
  ≡ just (Sem.ordinary competitorOrdinary)
competitorDecoderSameObject = refl

sourceValue : ℚ
sourceValue = Exact.ordinaryRational sourceOrdinary

targetValue : ℚ
targetValue = Exact.ordinaryRational targetOrdinary

competitorValue : ℚ
competitorValue = Exact.ordinaryRational competitorOrdinary

sourceValueExact : sourceValue ≡ (+ 1094 / 2187)
sourceValueExact = refl

targetValueExact : targetValue ≡ (+ 122 / 243)
targetValueExact = refl

competitorValueExact : competitorValue ≡ (+ 364 / 729)
competitorValueExact = refl

tekumDistance : ℚ → ℚ → ℚ
tekumDistance x y = ∣ x - y ∣

sourceToRawTargetDistanceExact :
  tekumDistance sourceValue targetValue ≡ (+ 4 / 2187)
sourceToRawTargetDistanceExact = refl

sourceToCompetitorDistanceExact :
  tekumDistance sourceValue competitorValue ≡ (+ 2 / 2187)
sourceToCompetitorDistanceExact = refl

competitorStrictlyCloser :
  tekumDistance sourceValue competitorValue
  < tekumDistance sourceValue targetValue
competitorStrictlyCloser =
  toWitness
    {a? =
      tekumDistance sourceValue competitorValue
      <? tekumDistance sourceValue targetValue}
    _

NearestAgainst : ℚ → ℚ → ℚ → Set
NearestAgainst source chosen competitor =
  tekumDistance source chosen ≤ tekumDistance source competitor

rawTargetNotNearestAgainstFiniteCompetitor :
  ¬ NearestAgainst sourceValue targetValue competitorValue
rawTargetNotNearestAgainstFiniteCompetitor claimedNearest =
  ℚP.<-irrefl (tekumDistance sourceValue competitorValue)
    (ℚP.<-≤-trans competitorStrictlyCloser claimedNearest)

record RawTruncationNearestOnFiniteClosure : Set where
  constructor rawTruncationNearestOnFiniteClosure
  field
    counterexampleInstanceNearest :
      NearestAgainst sourceValue targetValue competitorValue
open RawTruncationNearestOnFiniteClosure public

finiteClosureDoesNotRepairProposition5 :
  ¬ RawTruncationNearestOnFiniteClosure
finiteClosureDoesNotRepairProposition5 claimed =
  rawTargetNotNearestAgainstFiniteCompetitor
    (counterexampleInstanceNearest claimed)
