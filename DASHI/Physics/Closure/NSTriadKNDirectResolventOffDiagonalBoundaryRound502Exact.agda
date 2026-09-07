module DASHI.Physics.Closure.NSTriadKNDirectResolventOffDiagonalBoundaryRound502Exact where

------------------------------------------------------------------------
-- ROUND502 / DIRECT RESOLVENT OFF-DIAGONAL VS FULL R439 COMPANION FIREWALL
--
-- R448 already proves that the live R397/R406 resolvent object is the
-- OFF-DIAGONAL Cauchy form: one unordered alpha<beta contribution per physical
-- output fibre.  R496-R500 give an exact nonlinear companion for that same
-- off-diagonal carrier.
--
-- R439/R440, however, factor a separable FULL SQUARE double sum over a complete
-- output fibre, including diagonal alpha=beta terms.  Therefore an exact
-- R406 off-diagonal companion must not be identified with the literal R439
-- full companion merely because both use the word "companion".
--
-- Consequence:
--   * R500 is an exact R415 signed-cross producer;
--   * R501's R423 construction is only Clay-facing after an additional theorem
--     identifies the selected off-diagonal signed cross with the intended
--     homogeneity-correct quadratic-companion observable;
--   * alternatively R423 can be tightened so that this same-object receipt is
--     explicit in its type.
--
-- No equality between full and off-diagonal forms is asserted here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSTriadKNPhysicalCauchyOffDiagonalR397WeldRound448Exact as R448
import DASHI.Physics.Closure.NSTriadKNPhysicalHeatDoubleSumFactorizationRound440Exact as R440
import DASHI.Physics.Closure.NSTriadKNDirectResolventIntegratedCompanionRound500Exact as R500
import DASHI.Physics.Closure.NSTriadKNDirectResolventCompanionToR423Round501Exact as R501

------------------------------------------------------------------------
-- No-collapse marker.
------------------------------------------------------------------------

data OffDiagonalIsFullR439WithoutReceipt : Set where

offDiagonalCannotBecomeFullR439ByName :
  OffDiagonalIsFullR439WithoutReceipt → ⊥
offDiagonalCannotBecomeFullR439ByName ()

------------------------------------------------------------------------
-- Exact status pins.
------------------------------------------------------------------------

round502R448LiveCarrierIsLiteralOffDiagonal : Bool
round502R448LiveCarrierIsLiteralOffDiagonal = true

round502R440CompanionUsesFullSquareDoubleSum : Bool
round502R440CompanionUsesFullSquareDoubleSum = true

round502R500ExactR406SignedCrossProducer : Bool
round502R500ExactR406SignedCrossProducer = true

round502OffDiagonalEqualsFullR439WithoutExtraReceipt : Bool
round502OffDiagonalEqualsFullR439WithoutExtraReceipt = false

round502R501AloneClosesStrictLiteralR439CompanionWeld : Bool
round502R501AloneClosesStrictLiteralR439CompanionWeld = false

round502AdditionalHomogeneityCorrectSameObjectReceiptRequired : Bool
round502AdditionalHomogeneityCorrectSameObjectReceiptRequired = true

round502SignedSpacetimeEstimateClosed : Bool
round502SignedSpacetimeEstimateClosed = false

round502ClayPromotion : Bool
round502ClayPromotion = false

round502R448LiveCarrierIsLiteralOffDiagonalIsTrue :
  round502R448LiveCarrierIsLiteralOffDiagonal ≡ true
round502R448LiveCarrierIsLiteralOffDiagonalIsTrue = refl

round502OffDiagonalEqualsFullR439WithoutExtraReceiptIsFalse :
  round502OffDiagonalEqualsFullR439WithoutExtraReceipt ≡ false
round502OffDiagonalEqualsFullR439WithoutExtraReceiptIsFalse = refl

round502R501AloneClosesStrictLiteralR439CompanionWeldIsFalse :
  round502R501AloneClosesStrictLiteralR439CompanionWeld ≡ false
round502R501AloneClosesStrictLiteralR439CompanionWeldIsFalse = refl

round502ClayPromotionIsFalse : round502ClayPromotion ≡ false
round502ClayPromotionIsFalse = refl
