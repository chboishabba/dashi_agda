module DASHI.Moonshine.Monster3BG2FourDescriptorResidualPromotionBidiExact where

------------------------------------------------------------------------
-- G2(4) DEGREE / RESIDUAL / SAME-OBJECT PROMOTION BIDI
--
-- Cross-pollination shape, implemented independently on this branch so that
-- the Monster PR does not import theorem authority from another open PR:
--
--   coarse descriptor     = representation degree
--   retained residual     = source/action role and cover provenance
--   promotion             = same-object representation identification
--
-- Equal degree is a coarse collision.  Same-object promotion still requires
-- the explicit bijection + action intertwining already owned by the G2 bridge.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Moonshine.Monster3BG2FourSixtyFiveSeventyEightBridgeBidiExact as G2

------------------------------------------------------------------------
-- Two live role-labelled 78 candidates.
------------------------------------------------------------------------

data SeventyEightCandidate : Set where
  suz143G2Branch78 : SeventyEightCandidate
  wilsonMultiplicity78 : SeventyEightCandidate

data SeventyEightResidual : Set where
  suzBranchActionProvenance : SeventyEightResidual
  wilsonNormalizerActionProvenance : SeventyEightResidual

degree78Observer : SeventyEightCandidate → Nat
degree78Observer suz143G2Branch78 = 78
degree78Observer wilsonMultiplicity78 = 78

residual78Observer : SeventyEightCandidate → SeventyEightResidual
residual78Observer suz143G2Branch78 = suzBranchActionProvenance
residual78Observer wilsonMultiplicity78 = wilsonNormalizerActionProvenance

sameDegree78Collision :
  degree78Observer suz143G2Branch78 ≡
  degree78Observer wilsonMultiplicity78
sameDegree78Collision = refl

residual78Separates :
  residual78Observer suz143G2Branch78 ≡
  residual78Observer wilsonMultiplicity78 →
  ⊥
residual78Separates ()

------------------------------------------------------------------------
-- The pair (degree,residual) is a strict refinement of degree alone.
------------------------------------------------------------------------

degreeResidual78StrictRefinement :
  Observer.StrictRefinement
    degree78Observer
    (Observer.pairObserver degree78Observer residual78Observer)
degreeResidual78StrictRefinement =
  Observer.strictPairRefinement
    degree78Observer
    residual78Observer
    suz143G2Branch78
    wilsonMultiplicity78
    sameDegree78Collision
    residual78Separates

------------------------------------------------------------------------
-- Degree cannot reconstruct the provenance/action residual.
------------------------------------------------------------------------

DegreeRecoversResidual : Set
DegreeRecoversResidual =
  Σ (Nat → SeventyEightResidual)
    (λ recover →
      ∀ candidate → recover (degree78Observer candidate) ≡ residual78Observer candidate)

degree78CannotRecoverResidual : DegreeRecoversResidual → ⊥
degree78CannotRecoverResidual recovery =
  residual78Separates
    (trans
      (sym (commutes suz143G2Branch78))
      (trans
        (cong recover sameDegree78Collision)
        (commutes wilsonMultiplicity78)))
  where
    recover = proj₁ recovery
    commutes = proj₂ recovery

------------------------------------------------------------------------
-- Same-object promotion remains exactly the stronger existing receipt.
--
-- This adapter is intentionally one-way: once the actual weld is inhabited,
-- it supplies a promoted identification.  The coarse degree collision cannot
-- manufacture the weld.
------------------------------------------------------------------------

record SameObjectPromotion
    (branch : G2.Suz143ToG2FourBranching) : Set₁ where
  constructor same-object-promotion
  field
    weld : G2.WilsonSeventyEightG2FourSameObject branch

open SameObjectPromotion public

promoteFromActualWeld :
  ∀ {branch : G2.Suz143ToG2FourBranching} →
  G2.WilsonSeventyEightG2FourSameObject branch →
  SameObjectPromotion branch
promoteFromActualWeld actual = same-object-promotion actual

------------------------------------------------------------------------
-- Reverse BIDI acquisition target.
------------------------------------------------------------------------

record SameObjectReverseObligation : Set where
  constructor same-object-reverse-obligation
  field
    requireConcreteSuz143ToG2Branch78 : Bool
    requireConcreteSuz143ToG2Branch78IsTrue :
      requireConcreteSuz143ToG2Branch78 ≡ true

    requireWilson78RestrictedSameCarrier : Bool
    requireWilson78RestrictedSameCarrierIsTrue :
      requireWilson78RestrictedSameCarrier ≡ true

    requireTwoSidedCarrierEquivalence : Bool
    requireTwoSidedCarrierEquivalenceIsTrue :
      requireTwoSidedCarrierEquivalence ≡ true

    requireActionIntertwining : Bool
    requireActionIntertwiningIsTrue :
      requireActionIntertwining ≡ true

    degreeEqualityAloneDischargesPromotion : Bool
    degreeEqualityAloneDischargesPromotionIsFalse :
      degreeEqualityAloneDischargesPromotion ≡ false

canonicalSameObjectReverseObligation : SameObjectReverseObligation
canonicalSameObjectReverseObligation =
  same-object-reverse-obligation
    true refl
    true refl
    true refl
    true refl
    false refl

------------------------------------------------------------------------
-- Boundary: this file proves a coarse-descriptor non-factorability theorem on
-- role-labelled candidates.  It does not claim the two representations are
-- unequal as abstract G2(4) representations; that question is exactly what the
-- actual restricted class-function/action weld must decide.
------------------------------------------------------------------------

record MonsterDescriptorResidualBoundary : Set where
  constructor monster-descriptor-residual-boundary
  field
    degree78DeterminesSourceActionRole : Bool
    degree78DeterminesSourceActionRoleIsFalse :
      degree78DeterminesSourceActionRole ≡ false

    roleResidualStrictlyRefinesDegree : Bool
    roleResidualStrictlyRefinesDegreeIsTrue :
      roleResidualStrictlyRefinesDegree ≡ true

    roleDifferenceProvesRepresentationsNonisomorphic : Bool
    roleDifferenceProvesRepresentationsNonisomorphicIsFalse :
      roleDifferenceProvesRepresentationsNonisomorphic ≡ false

    sameObjectStillNeedsIntertwiner : Bool
    sameObjectStillNeedsIntertwinerIsTrue :
      sameObjectStillNeedsIntertwiner ≡ true

canonicalMonsterDescriptorResidualBoundary : MonsterDescriptorResidualBoundary
canonicalMonsterDescriptorResidualBoundary =
  monster-descriptor-residual-boundary false refl true refl false refl true refl
