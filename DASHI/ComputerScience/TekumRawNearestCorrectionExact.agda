module DASHI.ComputerScience.TekumRawNearestCorrectionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (_+_)
open import Data.Integer.Base as ℤ using (ℤ; +_; -[1+_]; _-_)
open import Data.Maybe.Base using (just)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Nullary.Negation.Core using (¬_)

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.ComputerScience.TekumFiniteSemanticsExact as Sem
import DASHI.ComputerScience.TekumFixedWidthBalancedArithmeticExact as Fixed
import DASHI.ComputerScience.TekumSourceAnchorCenterExact as Center
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source
import DASHI.ComputerScience.TekumTruncationRoundingExact as Truncate

------------------------------------------------------------------------
-- Existing raw n→n-2 path, now named independently of nearest semantics.
------------------------------------------------------------------------

rawTruncationCandidate :
  ∀ {extra} →
  Vec Trit.Trit (suc (suc (8 + extra))) →
  Vec Trit.Trit (8 + extra)
rawTruncationCandidate {extra} source =
  Fixed.addWord
    (Truncate.truncateTwo (Fixed.concreteAnchor source))
    (Center.sourceAnchorCenterWord (8 + extra))

record RawTargetOrdinary
    {extra}
    (word : Vec Trit.Trit (8 + extra)) : Set where
  constructor rawTargetOrdinary
  field
    ordinary : Sem.OrdinaryTekum
    decoderSameObject :
      Source.parseTekumWord word ≡ just (Sem.ordinary ordinary)
open RawTargetOrdinary public

rawNearestDisplacement :
  ∀ {n} → Vec Trit.Trit n → Vec Trit.Trit n → ℤ
rawNearestDisplacement raw nearest =
  BT.toInteger (BT.eval nearest) ℤ.- BT.toInteger (BT.eval raw)

------------------------------------------------------------------------
-- Exhaustive 10→8 maximum-radius witness.
------------------------------------------------------------------------

maxRadiusSource10 : Vec Trit.Trit 10
maxRadiusSource10 =
  Trit.neg ∷ Trit.neg ∷ Trit.zer ∷ Trit.neg ∷ Trit.neg ∷
  Trit.neg ∷ Trit.neg ∷ Trit.neg ∷ Trit.neg ∷ Trit.neg ∷ []

maxRadiusRaw8 : Vec Trit.Trit 8
maxRadiusRaw8 =
  Trit.zer ∷ Trit.pos ∷ Trit.pos ∷ Trit.pos ∷
  Trit.pos ∷ Trit.pos ∷ Trit.pos ∷ Trit.pos ∷ []

maxRadiusNearest8 : Vec Trit.Trit 8
maxRadiusNearest8 =
  Trit.zer ∷ Trit.neg ∷ Trit.neg ∷ Trit.neg ∷
  Trit.neg ∷ Trit.neg ∷ Trit.neg ∷ Trit.neg ∷ []

maxRadiusRawSameObject :
  rawTruncationCandidate maxRadiusSource10 ≡ maxRadiusRaw8
maxRadiusRawSameObject = refl

maxRadiusDisplacementExact :
  rawNearestDisplacement maxRadiusRaw8 maxRadiusNearest8 ≡ -[1+ 6557 ]
maxRadiusDisplacementExact = refl

data RadiusOne : ℤ → Set where
  radiusMinusOne : RadiusOne -[1+ 0 ]
  radiusZero : RadiusOne (+ 0)
  radiusPlusOne : RadiusOne (+ 1)

maxRadiusNotRadiusOne :
  ¬ RadiusOne (rawNearestDisplacement maxRadiusRaw8 maxRadiusNearest8)
maxRadiusNotRadiusOne ()

record UniformRadiusOneRawCorrection : Set where
  constructor uniformRadiusOneRawCorrection
  field
    maxWitnessWithinRadiusOne :
      RadiusOne (rawNearestDisplacement maxRadiusRaw8 maxRadiusNearest8)
open UniformRadiusOneRawCorrection public

uniformRadiusOneRawCorrectionRefuted :
  ¬ UniformRadiusOneRawCorrection
uniformRadiusOneRawCorrectionRefuted claim =
  maxRadiusNotRadiusOne (maxWitnessWithinRadiusOne claim)

------------------------------------------------------------------------
-- The discovery census is stronger: the observed maximum equals the entire
-- ordinary 8-trit carrier size (6558), and 12→10 analogously reaches 59046.
-- Hence the small raw-neighbourhood optimisation lane is fail-closed rather
-- than promoted from finite experiments.
------------------------------------------------------------------------
