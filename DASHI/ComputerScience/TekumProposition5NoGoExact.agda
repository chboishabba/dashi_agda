module DASHI.ComputerScience.TekumProposition5NoGoExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Maybe.Base using (just)
open import Data.Product.Base using (_×_; _,_)
open import Data.Vec.Base using (Vec)
open import Relation.Nullary.Negation using (¬_)

import DASHI.Algebra.Trit as Trit
import DASHI.ComputerScience.TekumFiniteSemanticsExact as Sem
import DASHI.ComputerScience.TekumProposition5CounterexampleExact as Counterexample
import DASHI.ComputerScience.TekumSpecialValuesExact as Special

------------------------------------------------------------------------
-- HUNHOLD PROPOSITION 5: UNRESTRICTED FINITE-TARGET NO-GO
--
-- The paper-facing nearest-finite statement needs raw two-trit truncation of
-- every ordinary 10-trit input to land in the finite 8-trit target set.
-- The already-paid edge calculations show that this premise fails at both
-- reserved endpoints: the negative edge reaches NaR and the positive edge
-- reaches infinity.  Any unrestricted finite-target theorem would therefore
-- imply the impossible boundary obligations packaged below.
------------------------------------------------------------------------

infix 4 _≢_
_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

IsFiniteLowerPrecision : Vec Trit.Trit 8 → Set
IsFiniteLowerPrecision word =
  (Special.classifySpecial word ≢ just Sem.naR) ×
  (Special.classifySpecial word ≢ just Sem.infinity)

negativeEdgeFinite : Set
negativeEdgeFinite =
  IsFiniteLowerPrecision Counterexample.negativeEdgeRounded8

positiveEdgeFinite : Set
positiveEdgeFinite =
  IsFiniteLowerPrecision Counterexample.positiveEdgeRounded8

record RawTruncationFiniteClosed : Set where
  constructor rawTruncationFiniteClosed
  field
    negativeBoundaryFinite : negativeEdgeFinite
    positiveBoundaryFinite : positiveEdgeFinite
open RawTruncationFiniteClosed public

negativeEdgeRefutesFiniteClosure : ¬ negativeEdgeFinite
negativeEdgeRefutesFiniteClosure (notNaR , notInfinity) =
  notNaR Counterexample.negativeEdgeRoundHitsNaR

positiveEdgeRefutesFiniteClosure : ¬ positiveEdgeFinite
positiveEdgeRefutesFiniteClosure (notNaR , notInfinity) =
  notInfinity Counterexample.positiveEdgeRoundHitsInfinity

unrestrictedRawTruncationFiniteClosureImpossible :
  ¬ RawTruncationFiniteClosed
unrestrictedRawTruncationFiniteClosureImpossible closed =
  negativeEdgeRefutesFiniteClosure (negativeBoundaryFinite closed)
