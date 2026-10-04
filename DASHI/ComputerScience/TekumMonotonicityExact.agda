module DASHI.ComputerScience.TekumMonotonicityExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (suc; _+_)
open import Data.Integer.Base using (+_)
open import Data.Maybe.Base using (just)
open import Data.Product.Base using (_,_)
open import Data.Rational.Base as ℚ using (_<_)
open import Data.Vec.Base using (Vec)

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.ComputerScience.TekumBalancedSuccessorExact as Succ
import DASHI.ComputerScience.TekumFixedWidthBalancedArithmeticExact as Fixed
import DASHI.ComputerScience.TekumParsedAdjacentCarryExtractExact as Extract
import DASHI.ComputerScience.TekumParsedBandMembershipExact as Parsed
import DASHI.ComputerScience.TekumPositiveSourceSuccessorAnchorExact as PositiveSource
import DASHI.ComputerScience.TekumSourceOrderExact as Order
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source
import DASHI.ComputerScience.TekumWidthAdmissibilityExact as Width

open import DASHI.ComputerScience.TekumFormalPropertiesExact public
  using (TekumOrderedCodeWitness)

open import DASHI.ComputerScience.TekumMonotoneMagnitudeExact public
  using
    ( exponentStrictForcesMagnitudeStrict
    ; sameExponentSignificandStrictForcesMagnitudeStrict
    )

open import DASHI.ComputerScience.TekumPositiveSourceSuccessorAnchorExact public
  using
    ( positiveSourceStepRaisesAnchorRank
    ; positiveSourceSuccessorAnchorsAreAdjacent
    )

open import DASHI.ComputerScience.TekumSourceOrderExact public
  using
    ( PositiveAdjacentOrder
    ; positiveAdjacentSourceCodeStrict
    ; hunholdProposition4PositiveAdjacent
    )

------------------------------------------------------------------------
-- HUNHOLD PROP. 4: THE ADJACENT POSITIVE SOURCE LEAF
--
-- The parser/carry extraction is now constructive.  Successful adjacent
-- ordinary parser images produce PositiveAdjacentOrder, which the exact
-- rational compiler turns into strict magnitude order.
------------------------------------------------------------------------

hunholdProposition4PositiveParsedAdjacent :
  ∀ {extra r s payload₁ payload₂ parsed₁ parsed₂}
  (left right : Vec Trit.Trit (8 + extra)) →
  Source.parseOrdinaryAnchor left ≡ just (r , payload₁ , parsed₁) →
  Source.parseOrdinaryAnchor right ≡ just (s , payload₂ , parsed₂) →
  Succ.successorWord (Fixed.concreteAnchor left)
    ≡ Fixed.concreteAnchor right →
  Parsed.parsedMagnitude parsed₁ ℚ.< Parsed.parsedMagnitude parsed₂
hunholdProposition4PositiveParsedAdjacent
    left right leftParse rightParse anchorStep =
  Order.positiveAdjacentSourceCodeStrict _ _
    (Extract.extractPositiveAdjacentOrder
      left right leftParse rightParse anchorStep)

hunholdProposition4PositiveSourceAdjacent :
  ∀ {extra r s payload₁ payload₂ parsed₁ parsed₂ m}
  (even : Width.EvenWidth (8 + extra))
  (left right : Vec Trit.Trit (8 + extra)) →
  BT.toInteger (BT.eval left) ≡ + (suc m) →
  BT.toInteger (BT.eval right) ≡ + (suc (suc m)) →
  Succ.HasSuccessor (Fixed.concreteAnchor left) →
  Source.parseOrdinaryAnchor left ≡ just (r , payload₁ , parsed₁) →
  Source.parseOrdinaryAnchor right ≡ just (s , payload₂ , parsed₂) →
  Parsed.parsedMagnitude parsed₁ ℚ.< Parsed.parsedMagnitude parsed₂
hunholdProposition4PositiveSourceAdjacent
    even left right leftValue rightValue anchorCarry leftParse rightParse =
  hunholdProposition4PositiveParsedAdjacent
    left right leftParse rightParse
    (PositiveSource.positiveSourceSuccessorAnchorsAreAdjacent
      even left right leftValue rightValue anchorCarry)

------------------------------------------------------------------------
-- Full Proposition 4 still composes the paper's convention branches:
-- NaR is least, infinity greatest, zero is the sign boundary, and the negative
-- half is reflected through Proposition 3.  The formerly open positive
-- parser/carry leaf is paid above.
------------------------------------------------------------------------
