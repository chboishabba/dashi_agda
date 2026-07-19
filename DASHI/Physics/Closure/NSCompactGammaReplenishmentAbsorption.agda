module DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Primitive using (Set)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

------------------------------------------------------------------------
-- Integrated compact-Gamma replenishment absorption.
--
-- Write E for the integrated sum of negative mechanism derivatives and R for
-- the integrated sum of positive mechanism derivatives.  The bounded
-- potential balance is
--
--   initial + R = final + E.
--
-- If R <= thetaE + C and E = marginE + thetaE, then nonnegativity of the
-- final potential implies
--
--   marginE <= initial + C.
--
-- This is the exact algebraic leaf needed after the finite audit: the analytic
-- work must construct a cutoff-uniform split E=marginE+thetaE and prove the
-- replenishment estimate.
------------------------------------------------------------------------

record AbsorptionArithmetic : Set₁ where
  field
    Scalar : Set
    zero : Scalar
    _+_ : Scalar → Scalar → Scalar
    _≤_ : Scalar → Scalar → Set

    ≤-trans :
      {a b c : Scalar} → _≤_ a b → _≤_ b c → _≤_ a c

    addZeroLeft :
      (a : Scalar) → _+_ zero a ≡ a

    addAssociative :
      (a b c : Scalar) → _+_ (_+_ a b) c ≡ _+_ a (_+_ b c)

    addCommutative :
      (a b : Scalar) → _+_ a b ≡ _+_ b a

    additionMonotoneLeft :
      {a b c : Scalar} →
      _≤_ a b →
      _≤_ (_+_ c a) (_+_ c b)

    additionMonotoneRight :
      {a b c : Scalar} →
      _≤_ a b →
      _≤_ (_+_ a c) (_+_ b c)

    additionCancelRight :
      {a b c : Scalar} →
      _≤_ (_+_ a c) (_+_ b c) →
      _≤_ a b

open AbsorptionArithmetic public

record CompactGammaAbsorptionInputs
    (A : AbsorptionArithmetic) : Set₁ where
  field
    initialPotential : Scalar A
    finalPotential : Scalar A
    escapeSupply : Scalar A
    replenishment : Scalar A
    thetaEscape : Scalar A
    marginEscape : Scalar A
    remainderConstant : Scalar A

    finalPotentialNonnegative :
      _≤_ A (zero A) finalPotential

    potentialBalance :
      _+_ A initialPotential replenishment ≡
      _+_ A finalPotential escapeSupply

    replenishmentAbsorbed :
      _≤_ A replenishment
        (_+_ A thetaEscape remainderConstant)

    escapeSplitsMarginAndAbsorbedPart :
      escapeSupply ≡ _+_ A marginEscape thetaEscape

open CompactGammaAbsorptionInputs public

absorbedReplenishmentBoundsEscapeMargin :
  (A : AbsorptionArithmetic) →
  (I : CompactGammaAbsorptionInputs A) →
  _≤_ A
    (marginEscape I)
    (_+_ A (initialPotential I) (remainderConstant I))
absorbedReplenishmentBoundsEscapeMargin A I =
  additionCancelRight A marginPlusTheta≤upperPlusTheta
  where
  zeroPlusEscape≤finalPlusEscape :
    _≤_ A
      (_+_ A (zero A) (escapeSupply I))
      (_+_ A (finalPotential I) (escapeSupply I))
  zeroPlusEscape≤finalPlusEscape =
    additionMonotoneRight A (finalPotentialNonnegative I)

  escape≤initialPlusReplenishment :
    _≤_ A
      (escapeSupply I)
      (_+_ A (initialPotential I) (replenishment I))
  escape≤initialPlusReplenishment =
    subst
      (λ lhs →
        _≤_ A lhs (_+_ A (initialPotential I) (replenishment I)))
      (addZeroLeft A (escapeSupply I))
      (subst
        (λ rhs →
          _≤_ A
            (_+_ A (zero A) (escapeSupply I))
            rhs)
        (sym (potentialBalance I))
        zeroPlusEscape≤finalPlusEscape)

  initialPlusReplenishment≤initialPlusAbsorbed :
    _≤_ A
      (_+_ A (initialPotential I) (replenishment I))
      (_+_ A
        (initialPotential I)
        (_+_ A (thetaEscape I) (remainderConstant I)))
  initialPlusReplenishment≤initialPlusAbsorbed =
    additionMonotoneLeft A (replenishmentAbsorbed I)

  escape≤initialPlusThetaPlusRemainder :
    _≤_ A
      (escapeSupply I)
      (_+_ A
        (initialPotential I)
        (_+_ A (thetaEscape I) (remainderConstant I)))
  escape≤initialPlusThetaPlusRemainder =
    ≤-trans A
      escape≤initialPlusReplenishment
      initialPlusReplenishment≤initialPlusAbsorbed

  marginPlusTheta≤initialPlusThetaPlusRemainder :
    _≤_ A
      (_+_ A (marginEscape I) (thetaEscape I))
      (_+_ A
        (initialPotential I)
        (_+_ A (thetaEscape I) (remainderConstant I)))
  marginPlusTheta≤initialPlusThetaPlusRemainder =
    subst
      (λ lhs →
        _≤_ A lhs
          (_+_ A
            (initialPotential I)
            (_+_ A (thetaEscape I) (remainderConstant I))))
      (escapeSplitsMarginAndAbsorbedPart I)
      escape≤initialPlusThetaPlusRemainder

  upperReassociation :
    _+_ A
      (initialPotential I)
      (_+_ A (thetaEscape I) (remainderConstant I))
    ≡
    _+_ A
      (_+_ A (initialPotential I) (remainderConstant I))
      (thetaEscape I)
  upperReassociation =
    trans
      (subst
        (λ middle →
          _+_ A (initialPotential I) middle ≡
          _+_ A
            (initialPotential I)
            (_+_ A (remainderConstant I) (thetaEscape I)))
        (addCommutative A (thetaEscape I) (remainderConstant I))
        (Agda.Builtin.Equality.refl))
      (sym (addAssociative A
        (initialPotential I)
        (remainderConstant I)
        (thetaEscape I)))

  marginPlusTheta≤upperPlusTheta :
    _≤_ A
      (_+_ A (marginEscape I) (thetaEscape I))
      (_+_ A
        (_+_ A (initialPotential I) (remainderConstant I))
        (thetaEscape I))
  marginPlusTheta≤upperPlusTheta =
    subst
      (λ rhs →
        _≤_ A
          (_+_ A (marginEscape I) (thetaEscape I))
          rhs)
      upperReassociation
      marginPlusTheta≤initialPlusThetaPlusRemainder

------------------------------------------------------------------------
-- Residence adapter.  The analytic danger theorem may directly produce a
-- margin-weighted residence expenditure controlled by marginEscape.
------------------------------------------------------------------------

record CompactGammaAbsorbedResidenceInputs
    (A : AbsorptionArithmetic) : Set₁ where
  field
    absorptionInputs : CompactGammaAbsorptionInputs A
    dangerousResidenceExpenditure : Scalar A

    dangerousResidenceConsumesEscapeMargin :
      _≤_ A dangerousResidenceExpenditure
        (marginEscape absorptionInputs)

open CompactGammaAbsorbedResidenceInputs public

absorbedCompactGammaReplenishmentBoundsResidence :
  (A : AbsorptionArithmetic) →
  (I : CompactGammaAbsorbedResidenceInputs A) →
  _≤_ A
    (dangerousResidenceExpenditure I)
    (_+_ A
      (initialPotential (absorptionInputs I))
      (remainderConstant (absorptionInputs I)))
absorbedCompactGammaReplenishmentBoundsResidence A I =
  ≤-trans A
    (dangerousResidenceConsumesEscapeMargin I)
    (absorbedReplenishmentBoundsEscapeMargin A (absorptionInputs I))
