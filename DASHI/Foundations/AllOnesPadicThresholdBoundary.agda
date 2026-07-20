module DASHI.Foundations.AllOnesPadicThresholdBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope
  using (Trit; neg; zer; pos)
import DASHI.Foundations.TriadicFiniteQuotient as Quotient

------------------------------------------------------------------------
-- Finite all-ones balanced/ordinary ternary prefixes.
--
-- `allOnesPrefix n` is the ordinary natural value of the n-digit string
-- 111...111 in base 3.  It is distinct from the carrier cardinality 3^n.

allOnesPrefix : Nat → Nat
allOnesPrefix zero = zero
allOnesPrefix (suc n) = 1 + 3 * allOnesPrefix n

allOnesPrefix0 : allOnesPrefix 0 ≡ 0
allOnesPrefix0 = refl

allOnesPrefix1 : allOnesPrefix 1 ≡ 1
allOnesPrefix1 = refl

allOnesPrefix2 : allOnesPrefix 2 ≡ 4
allOnesPrefix2 = refl

allOnesPrefix3 : allOnesPrefix 3 ≡ 13
allOnesPrefix3 = refl

allOnesPrefix4 : allOnesPrefix 4 ≡ 40
allOnesPrefix4 = refl

allOnesPrefix10 : allOnesPrefix 10 ≡ 29524
allOnesPrefix10 = refl

triadicCarrierDepth3 : Quotient.pow3 3 ≡ 27
triadicCarrierDepth3 = refl

prefixAndCarrierAreDifferentAtDepth3 : String
prefixAndCarrierAreDifferentAtDepth3 =
  "111_3 has ordinary value 13, while the depth-three quotient has 27 residue states"

------------------------------------------------------------------------
-- Scaled balanced-ternary decision polarity.

data HalfPolarity : Set where
  negativeHalf zeroHalf positiveHalf : HalfPolarity

tritToHalfPolarity : Trit → HalfPolarity
tritToHalfPolarity neg = negativeHalf
tritToHalfPolarity zer = zeroHalf
tritToHalfPolarity pos = positiveHalf

negativeTritMapsNegativeHalf : tritToHalfPolarity neg ≡ negativeHalf
negativeTritMapsNegativeHalf = refl

zeroTritMapsZeroHalf : tritToHalfPolarity zer ≡ zeroHalf
zeroTritMapsZeroHalf = refl

positiveTritMapsPositiveHalf : tritToHalfPolarity pos ≡ positiveHalf
positiveTritMapsPositiveHalf = refl

record PadicAllOnesLimitObligation : Set₁ where
  field
    Q3 : Set
    embedNatural : Nat → Q3
    negativeHalfQ3 : Q3
    padicDistance : Q3 → Q3 → Q3
    convergesToNegativeHalf : Set
    realDiverges : Set
    metricsKeptDistinct : Set

record AllOnesPadicBoundary : Set where
  constructor allOnesPadicBoundary
  field
    finitePrefixArithmeticChecked : Bool
    depthTenValueChecked : Bool
    minusHalfPadicLimitPromotedHere : Bool
    minusHalfPadicLimitPromotedHereIsFalse :
      minusHalfPadicLimitPromotedHere ≡ false
    minusHalfIsRealDecisionThresholdClaimed : Bool
    minusHalfIsRealDecisionThresholdClaimedIsFalse :
      minusHalfIsRealDecisionThresholdClaimed ≡ false
    additiveAndMultiplicativeInverseCollapsed : Bool
    additiveAndMultiplicativeInverseCollapsedIsFalse :
      additiveAndMultiplicativeInverseCollapsed ≡ false
    interpretation : String

canonicalAllOnesPadicBoundary : AllOnesPadicBoundary
canonicalAllOnesPadicBoundary =
  allOnesPadicBoundary
    true
    true
    false refl
    false refl
    false refl
    "finite all-ones prefixes are exact; the Q3 convergence to -1/2 and any bridge to a real decision policy remain separately typed"
