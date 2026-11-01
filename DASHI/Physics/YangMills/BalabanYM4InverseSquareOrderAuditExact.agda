module DASHI.Physics.YangMills.BalabanYM4InverseSquareOrderAuditExact where

------------------------------------------------------------------------
-- AUDIT COMPANION FOR THE RATIONAL INVERSE-SQUARE BRIDGE
--
-- This small module exposes the two genuinely representation-level hypotheses
-- consumed by BalabanYM4RationalInverseSquareOrderExact:
--
--   u_k g_k^2 = 1,       u_* gamma^2 = 1,
--
-- plus positivity.  It prevents a later caller from replacing them with an
-- abstract monotonicity axiom.  Once these equalities are obtained from the
-- literal source definition u_k = g_k^-2, all order transport is theorem-level.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; Positive; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4RationalInverseSquareOrderExact as Order

record LiteralInverseSquareRepresentation : Set where
  field
    g gamma u uStar : ℚ
    gPositive : Positive g
    gammaPositive : Positive gamma
    uRepresentsInverseSquare : u * Order.square g ≡ 1ℚ
    uStarRepresentsInverseSquare : uStar * Order.square gamma ≡ 1ℚ

open LiteralInverseSquareRepresentation public

asOrderData : LiteralInverseSquareRepresentation → Order.RationalInverseSquareOrderData
asOrderData representation = record
  { Order.RationalInverseSquareOrderData.coupling = g representation
  ; Order.RationalInverseSquareOrderData.thresholdCoupling = gamma representation
  ; Order.RationalInverseSquareOrderData.inverseCoupling = u representation
  ; Order.RationalInverseSquareOrderData.inverseThreshold = uStar representation
  ; Order.RationalInverseSquareOrderData.couplingPositive = gPositive representation
  ; Order.RationalInverseSquareOrderData.thresholdCouplingPositive = gammaPositive representation
  ; Order.RationalInverseSquareOrderData.inverseCouplingTimesSquare = uRepresentsInverseSquare representation
  ; Order.RationalInverseSquareOrderData.inverseThresholdTimesSquare = uStarRepresentsInverseSquare representation
  }

literalInverseSquareThresholdImpliesCouplingCap :
  ∀ representation →
  uStar representation ≤ u representation →
  g representation ≤ gamma representation
literalInverseSquareThresholdImpliesCouplingCap representation =
  Order.inverseSquareThresholdImpliesSmallCoupling (asOrderData representation)

ym4LiteralInverseSquareRepresentationAuditLevel : ProofLevel
ym4LiteralInverseSquareRepresentationAuditLevel = machineChecked
