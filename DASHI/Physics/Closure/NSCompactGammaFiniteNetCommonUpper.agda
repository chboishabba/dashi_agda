module DASHI.Physics.Closure.NSCompactGammaFiniteNetCommonUpper where

open import Agda.Primitive using (Set; Set₁)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption

------------------------------------------------------------------------
-- Finite-net reduction for a cutoff/shell/profile common upper bound.
--
-- The compact transfer potential satisfies 0 <= B_K <= 1 in its intended
-- real-number instantiation.  The previous absorption theorem gives
--
--   residenceExpenditure <= B_K(t0) + C_K.
--
-- Therefore the remaining common-upper problem can be reduced to a uniform
-- bound for the integrated replenishment remainder C_K.  A finite net is useful
-- only after an analytic local-oscillation estimate is supplied; sampled
-- distances or fitted slopes are not proof terms.
------------------------------------------------------------------------

record CompactGammaFiniteNetCommonUpperInputs
    (A : AbsorptionArithmetic) : Set₁ where
  field
    Cutoff : Set
    Shell : Set
    State : Set
    Center : Set

    member :
      Cutoff → Shell → State →
      CompactGammaAbsorbedResidenceInputs A

    one : Scalar A
    netRemainderUpper : Scalar A
    oscillationAllowance : Scalar A

    chooseCenter : Cutoff → Shell → State → Center
    centerRemainder : Center → Scalar A

    initialPotentialBoundedByOne :
      (cutoff : Cutoff) →
      (shell : Shell) →
      (state : State) →
      _≤_ A
        (initialPotential
          (absorptionInputs (member cutoff shell state)))
        one

    memberRemainderNearCenter :
      (cutoff : Cutoff) →
      (shell : Shell) →
      (state : State) →
      _≤_ A
        (remainderConstant
          (absorptionInputs (member cutoff shell state)))
        (_+_ A
          (centerRemainder (chooseCenter cutoff shell state))
          oscillationAllowance)

    centerRemainderBound :
      (center : Center) →
      _≤_ A (centerRemainder center) netRemainderUpper

open CompactGammaFiniteNetCommonUpperInputs public

finiteNetCommonUpperBoundsResidence :
  (A : AbsorptionArithmetic) →
  (I : CompactGammaFiniteNetCommonUpperInputs A) →
  (cutoff : Cutoff I) →
  (shell : Shell I) →
  (state : State I) →
  _≤_ A
    (dangerousResidenceExpenditure (member I cutoff shell state))
    (_+_ A
      (one I)
      (_+_ A (netRemainderUpper I) (oscillationAllowance I)))
finiteNetCommonUpperBoundsResidence A I cutoff shell state =
  ≤-trans A residence≤memberUpper memberUpper≤commonUpper
  where
  M : CompactGammaAbsorbedResidenceInputs A
  M = member I cutoff shell state

  residence≤memberUpper :
    _≤_ A
      (dangerousResidenceExpenditure M)
      (_+_ A
        (initialPotential (absorptionInputs M))
        (remainderConstant (absorptionInputs M)))
  residence≤memberUpper =
    absorbedCompactGammaReplenishmentBoundsResidence A M

  center≤net :
    _≤_ A
      (centerRemainder I (chooseCenter I cutoff shell state))
      (netRemainderUpper I)
  center≤net =
    centerRemainderBound I (chooseCenter I cutoff shell state)

  centerPlusAllowance≤netPlusAllowance :
    _≤_ A
      (_+_ A
        (centerRemainder I (chooseCenter I cutoff shell state))
        (oscillationAllowance I))
      (_+_ A
        (netRemainderUpper I)
        (oscillationAllowance I))
  centerPlusAllowance≤netPlusAllowance =
    additionMonotoneRight A center≤net

  remainder≤netPlusAllowance :
    _≤_ A
      (remainderConstant (absorptionInputs M))
      (_+_ A
        (netRemainderUpper I)
        (oscillationAllowance I))
  remainder≤netPlusAllowance =
    ≤-trans A
      (memberRemainderNearCenter I cutoff shell state)
      centerPlusAllowance≤netPlusAllowance

  initialPlusRemainder≤onePlusRemainder :
    _≤_ A
      (_+_ A
        (initialPotential (absorptionInputs M))
        (remainderConstant (absorptionInputs M)))
      (_+_ A
        (one I)
        (remainderConstant (absorptionInputs M)))
  initialPlusRemainder≤onePlusRemainder =
    additionMonotoneRight A
      (initialPotentialBoundedByOne I cutoff shell state)

  onePlusRemainder≤commonUpper :
    _≤_ A
      (_+_ A
        (one I)
        (remainderConstant (absorptionInputs M)))
      (_+_ A
        (one I)
        (_+_ A (netRemainderUpper I) (oscillationAllowance I)))
  onePlusRemainder≤commonUpper =
    additionMonotoneLeft A remainder≤netPlusAllowance

  memberUpper≤commonUpper :
    _≤_ A
      (_+_ A
        (initialPotential (absorptionInputs M))
        (remainderConstant (absorptionInputs M)))
      (_+_ A
        (one I)
        (_+_ A (netRemainderUpper I) (oscillationAllowance I)))
  memberUpper≤commonUpper =
    ≤-trans A
      initialPlusRemainder≤onePlusRemainder
      onePlusRemainder≤commonUpper
