module DASHI.Physics.Closure.NSCompactGammaBufferedDangerExpenditure where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Primitive using (Set; Set₁)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption

------------------------------------------------------------------------
-- Buffered finite-net danger expenditure.
--
-- A member state with Gamma >= lambda need not have a center with the same
-- threshold.  A local Gamma modulus instead transfers member danger to a
-- buffered center predicate, typically Gamma(center) >= lambda - delta.
--
-- If the buffered center spends at least `centerLower`, and the escape can lose
-- at most `oscillationAllowance` between center and member, then any split
--
--   centerLower = memberLower + oscillationAllowance
--
-- yields the positive member lower bound `memberLower <= memberEscape`.
--
-- Constructing the predicates and inequalities uniformly in shell and cutoff is
-- the analytic obligation.  This module proves only their exact composition.
------------------------------------------------------------------------

record BufferedDangerExpenditureInputs
    (A : AbsorptionArithmetic) : Set₁ where
  field
    MemberDanger : Set
    CenterBufferedDanger : Set

    centerLower : Scalar A
    memberLower : Scalar A
    oscillationAllowance : Scalar A
    centerEscape : Scalar A
    memberEscape : Scalar A

    dangerTransfersToBufferedCenter :
      MemberDanger → CenterBufferedDanger

    bufferedCenterDangerForcesEscape :
      CenterBufferedDanger →
      _≤_ A centerLower centerEscape

    centerEscapeNearMember :
      _≤_ A centerEscape
        (_+_ A memberEscape oscillationAllowance)

    centerLowerSplitsMemberAndAllowance :
      centerLower ≡ _+_ A memberLower oscillationAllowance

open BufferedDangerExpenditureInputs public

bufferedDangerForcesMemberExpenditure :
  (A : AbsorptionArithmetic) →
  (I : BufferedDangerExpenditureInputs A) →
  MemberDanger I →
  _≤_ A (memberLower I) (memberEscape I)
bufferedDangerForcesMemberExpenditure A I memberDanger =
  additionCancelRight A memberPlusAllowance≤escapePlusAllowance
  where
  centerDanger : CenterBufferedDanger I
  centerDanger = dangerTransfersToBufferedCenter I memberDanger

  centerLower≤centerEscape :
    _≤_ A (centerLower I) (centerEscape I)
  centerLower≤centerEscape =
    bufferedCenterDangerForcesEscape I centerDanger

  centerLower≤memberPlusAllowance :
    _≤_ A
      (centerLower I)
      (_+_ A (memberEscape I) (oscillationAllowance I))
  centerLower≤memberPlusAllowance =
    ≤-trans A centerLower≤centerEscape (centerEscapeNearMember I)

  memberPlusAllowance≤escapePlusAllowance :
    _≤_ A
      (_+_ A (memberLower I) (oscillationAllowance I))
      (_+_ A (memberEscape I) (oscillationAllowance I))
  memberPlusAllowance≤escapePlusAllowance =
    subst
      (λ lower →
        _≤_ A lower
          (_+_ A (memberEscape I) (oscillationAllowance I)))
      (centerLowerSplitsMemberAndAllowance I)
      centerLower≤memberPlusAllowance
