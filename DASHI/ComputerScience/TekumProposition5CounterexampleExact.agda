module DASHI.ComputerScience.TekumProposition5CounterexampleExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Maybe using (just; nothing)
open import Data.Vec using (Vec; []; _∷_)

import DASHI.Algebra.Trit as Trit
import DASHI.ComputerScience.TekumFiniteSemanticsExact as Sem
import DASHI.ComputerScience.TekumFixedWidthBalancedArithmeticExact as Fixed
import DASHI.ComputerScience.TekumSourceAnchorCenterExact as Center
import DASHI.ComputerScience.TekumSpecialValuesExact as Special
import DASHI.ComputerScience.TekumTruncationRoundingExact as Truncate

------------------------------------------------------------------------
-- A SOURCE-LEVEL OBSTRUCTION TO HUNHOLD PROPOSITION 5 AS STATED
--
-- For the finite 10-trit source word
--
--     T T T T T T T T T 0          (MSB first)
--
-- the Definition-7 anchor is
--
--     1 T 1 T 1 T 1 T 0 1.
--
-- Dropping the two low anchor trits therefore leaves the 8-trit midpoint
-- anchor 1T1T1T1T.  Inverting that anchor with the original negative sign
-- reaches TTTTTTTT, which is the reserved NaR source string.  Thus the raw
-- truncation construction does not always land in the finite lower-precision
-- candidate set needed by the paper's rational absolute-distance argmin.
--
-- This owner records the concrete source calculation rather than postulating a
-- globally false nearest-finite theorem.  A repaired Proposition 5 must either
-- restrict the domain or specify saturation/special handling at this boundary.
------------------------------------------------------------------------

negativeEdge10 : Vec Trit.Trit 10
negativeEdge10 =
  Trit.zer ∷ Trit.neg ∷ Trit.neg ∷ Trit.neg ∷ Trit.neg ∷
  Trit.neg ∷ Trit.neg ∷ Trit.neg ∷ Trit.neg ∷ Trit.neg ∷ []

negativeEdge10IsOrdinarySourceWord :
  Special.classifySpecial negativeEdge10 ≡ nothing
negativeEdge10IsOrdinarySourceWord = refl

negativeEdgeAnchor10 : Vec Trit.Trit 10
negativeEdgeAnchor10 = Fixed.concreteAnchor negativeEdge10

negativeEdgeTruncatedAnchor8 : Vec Trit.Trit 8
negativeEdgeTruncatedAnchor8 = Truncate.truncateTwo negativeEdgeAnchor10

negativeAnchorInverse8 : Vec Trit.Trit 8 → Vec Trit.Trit 8
negativeAnchorInverse8 anchor =
  Fixed.negateWord
    (Fixed.addWord anchor (Center.sourceAnchorCenterWord 8))

negativeEdgeRounded8 : Vec Trit.Trit 8
negativeEdgeRounded8 = negativeAnchorInverse8 negativeEdgeTruncatedAnchor8

negativeEdgeAnchorTruncatesToMidpoint :
  negativeEdgeTruncatedAnchor8 ≡ Center.sourceAnchorCenterWord 8
negativeEdgeAnchorTruncatesToMidpoint = refl

negativeEdgeRoundHitsNaR :
  Special.classifySpecial negativeEdgeRounded8 ≡ just Sem.naR
negativeEdgeRoundHitsNaR = refl

------------------------------------------------------------------------
-- Symmetric positive boundary: raw truncation reaches the infinity encoding.
------------------------------------------------------------------------

positiveEdge10 : Vec Trit.Trit 10
positiveEdge10 =
  Trit.zer ∷ Trit.pos ∷ Trit.pos ∷ Trit.pos ∷ Trit.pos ∷
  Trit.pos ∷ Trit.pos ∷ Trit.pos ∷ Trit.pos ∷ Trit.pos ∷ []

positiveEdge10IsOrdinarySourceWord :
  Special.classifySpecial positiveEdge10 ≡ nothing
positiveEdge10IsOrdinarySourceWord = refl

positiveEdgeAnchor10 : Vec Trit.Trit 10
positiveEdgeAnchor10 = Fixed.concreteAnchor positiveEdge10

positiveEdgeTruncatedAnchor8 : Vec Trit.Trit 8
positiveEdgeTruncatedAnchor8 = Truncate.truncateTwo positiveEdgeAnchor10

positiveAnchorInverse8 : Vec Trit.Trit 8 → Vec Trit.Trit 8
positiveAnchorInverse8 anchor =
  Fixed.addWord anchor (Center.sourceAnchorCenterWord 8)

positiveEdgeRounded8 : Vec Trit.Trit 8
positiveEdgeRounded8 = positiveAnchorInverse8 positiveEdgeTruncatedAnchor8

positiveEdgeAnchorTruncatesToMidpoint :
  positiveEdgeTruncatedAnchor8 ≡ Center.sourceAnchorCenterWord 8
positiveEdgeAnchorTruncatesToMidpoint = refl

positiveEdgeRoundHitsInfinity :
  Special.classifySpecial positiveEdgeRounded8 ≡ just Sem.infinity
positiveEdgeRoundHitsInfinity = refl
