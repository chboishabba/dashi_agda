module DASHI.Physics.Closure.NSPeriodicHysteresisSeparation where

open import Agda.Primitive using (Set)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Quantitative hysteresis separation.
--
-- Suppose shell a beats shell b by a gap at one switch and b later beats a
-- by the same gap.  If each score changes by at most one common modulus over
-- that interval, then two gaps are bounded by two moduli.  Consequently any
-- interval whose modulus is smaller than the hysteresis gap cannot contain an
-- immediate reverse switch.
------------------------------------------------------------------------

interchangeFourTerms :
  (A : AbsorptionArithmetic) →
  (a b c d : Scalar A) →
  _+_ A (_+_ A a b) (_+_ A c d) ≡
  _+_ A (_+_ A a c) (_+_ A b d)
interchangeFourTerms A a b c d =
  trans
    (addAssociative A a b (_+_ A c d))
    (trans
      (cong
        (λ middle → _+_ A a middle)
        (trans
          (sym (addAssociative A b c d))
          (trans
            (cong (λ left → _+_ A left d)
              (addCommutative A b c))
            (addAssociative A c b d))))
      (sym (addAssociative A a c (_+_ A b d))))

record PeriodicHysteresisSeparationInputs
    (A : AbsorptionArithmetic) : Set₁ where
  field
    oldScoreAtFirst newScoreAtFirst : Scalar A
    oldScoreAtSecond newScoreAtSecond : Scalar A
    hysteresisGap scoreModulus : Scalar A

    firstSwitchGain :
      _≤_ A
        (_+_ A oldScoreAtFirst hysteresisGap)
        newScoreAtFirst

    reverseSwitchGain :
      _≤_ A
        (_+_ A newScoreAtSecond hysteresisGap)
        oldScoreAtSecond

    oldScoreVariation :
      _≤_ A oldScoreAtSecond
        (_+_ A oldScoreAtFirst scoreModulus)

    newScoreVariation :
      _≤_ A newScoreAtFirst
        (_+_ A newScoreAtSecond scoreModulus)

open PeriodicHysteresisSeparationInputs public

twoWayHysteresisRequiresDoubleModulus :
  ∀ {A : AbsorptionArithmetic} →
  (H : PeriodicHysteresisSeparationInputs A) →
  _≤_ A
    (_+_ A (hysteresisGap H) (hysteresisGap H))
    (_+_ A (scoreModulus H) (scoreModulus H))
twoWayHysteresisRequiresDoubleModulus {A = A} H =
  additionCancelRight A commonMovedToRight
  where
  firstAcrossInterval :
    _≤_ A
      (_+_ A (oldScoreAtFirst H) (hysteresisGap H))
      (_+_ A (newScoreAtSecond H) (scoreModulus H))
  firstAcrossInterval =
    ≤-trans A (firstSwitchGain H) (newScoreVariation H)

  reverseAcrossInterval :
    _≤_ A
      (_+_ A (newScoreAtSecond H) (hysteresisGap H))
      (_+_ A (oldScoreAtFirst H) (scoreModulus H))
  reverseAcrossInterval =
    ≤-trans A (reverseSwitchGain H) (oldScoreVariation H)

  pairStepOne :
    _≤_ A
      (_+_ A
        (_+_ A (oldScoreAtFirst H) (hysteresisGap H))
        (_+_ A (newScoreAtSecond H) (hysteresisGap H)))
      (_+_ A
        (_+_ A (newScoreAtSecond H) (scoreModulus H))
        (_+_ A (newScoreAtSecond H) (hysteresisGap H)))
  pairStepOne = additionMonotoneRight A firstAcrossInterval

  pairStepTwo :
    _≤_ A
      (_+_ A
        (_+_ A (newScoreAtSecond H) (scoreModulus H))
        (_+_ A (newScoreAtSecond H) (hysteresisGap H)))
      (_+_ A
        (_+_ A (newScoreAtSecond H) (scoreModulus H))
        (_+_ A (oldScoreAtFirst H) (scoreModulus H)))
  pairStepTwo = additionMonotoneLeft A reverseAcrossInterval

  rawPairBound :
    _≤_ A
      (_+_ A
        (_+_ A (oldScoreAtFirst H) (hysteresisGap H))
        (_+_ A (newScoreAtSecond H) (hysteresisGap H)))
      (_+_ A
        (_+_ A (newScoreAtSecond H) (scoreModulus H))
        (_+_ A (oldScoreAtFirst H) (scoreModulus H)))
  rawPairBound = ≤-trans A pairStepOne pairStepTwo

  leftInterchanged :
    _≤_ A
      (_+_ A
        (_+_ A (oldScoreAtFirst H) (newScoreAtSecond H))
        (_+_ A (hysteresisGap H) (hysteresisGap H)))
      (_+_ A
        (_+_ A (newScoreAtSecond H) (scoreModulus H))
        (_+_ A (oldScoreAtFirst H) (scoreModulus H)))
  leftInterchanged =
    subst
      (λ lhs →
        _≤_ A lhs
          (_+_ A
            (_+_ A (newScoreAtSecond H) (scoreModulus H))
            (_+_ A (oldScoreAtFirst H) (scoreModulus H))))
      (interchangeFourTerms A
        (oldScoreAtFirst H) (hysteresisGap H)
        (newScoreAtSecond H) (hysteresisGap H))
      rawPairBound

  bothInterchanged :
    _≤_ A
      (_+_ A
        (_+_ A (oldScoreAtFirst H) (newScoreAtSecond H))
        (_+_ A (hysteresisGap H) (hysteresisGap H)))
      (_+_ A
        (_+_ A (newScoreAtSecond H) (oldScoreAtFirst H))
        (_+_ A (scoreModulus H) (scoreModulus H)))
  bothInterchanged =
    subst
      (λ rhs →
        _≤_ A
          (_+_ A
            (_+_ A (oldScoreAtFirst H) (newScoreAtSecond H))
            (_+_ A (hysteresisGap H) (hysteresisGap H)))
          rhs)
      (interchangeFourTerms A
        (newScoreAtSecond H) (scoreModulus H)
        (oldScoreAtFirst H) (scoreModulus H))
      leftInterchanged

  commonPrefixAligned :
    _≤_ A
      (_+_ A
        (_+_ A (oldScoreAtFirst H) (newScoreAtSecond H))
        (_+_ A (hysteresisGap H) (hysteresisGap H)))
      (_+_ A
        (_+_ A (oldScoreAtFirst H) (newScoreAtSecond H))
        (_+_ A (scoreModulus H) (scoreModulus H)))
  commonPrefixAligned =
    subst
      (λ rhs →
        _≤_ A
          (_+_ A
            (_+_ A (oldScoreAtFirst H) (newScoreAtSecond H))
            (_+_ A (hysteresisGap H) (hysteresisGap H)))
          (_+_ A rhs
            (_+_ A (scoreModulus H) (scoreModulus H))))
      (addCommutative A (newScoreAtSecond H) (oldScoreAtFirst H))
      bothInterchanged

  leftCommonMoved :
    _≤_ A
      (_+_ A
        (_+_ A (hysteresisGap H) (hysteresisGap H))
        (_+_ A (oldScoreAtFirst H) (newScoreAtSecond H)))
      (_+_ A
        (_+_ A (oldScoreAtFirst H) (newScoreAtSecond H))
        (_+_ A (scoreModulus H) (scoreModulus H)))
  leftCommonMoved =
    subst
      (λ lhs →
        _≤_ A lhs
          (_+_ A
            (_+_ A (oldScoreAtFirst H) (newScoreAtSecond H))
            (_+_ A (scoreModulus H) (scoreModulus H))))
      (addCommutative A
        (_+_ A (oldScoreAtFirst H) (newScoreAtSecond H))
        (_+_ A (hysteresisGap H) (hysteresisGap H)))
      commonPrefixAligned

  commonMovedToRight :
    _≤_ A
      (_+_ A
        (_+_ A (hysteresisGap H) (hysteresisGap H))
        (_+_ A (oldScoreAtFirst H) (newScoreAtSecond H)))
      (_+_ A
        (_+_ A (scoreModulus H) (scoreModulus H))
        (_+_ A (oldScoreAtFirst H) (newScoreAtSecond H)))
  commonMovedToRight =
    subst
      (λ rhs →
        _≤_ A
          (_+_ A
            (_+_ A (hysteresisGap H) (hysteresisGap H))
            (_+_ A (oldScoreAtFirst H) (newScoreAtSecond H)))
          rhs)
      (addCommutative A
        (_+_ A (oldScoreAtFirst H) (newScoreAtSecond H))
        (_+_ A (scoreModulus H) (scoreModulus H)))
      leftCommonMoved

hysteresisGapExcludesImmediateBackSwitch :
  ∀ {A : AbsorptionArithmetic} →
  (H : PeriodicHysteresisSeparationInputs A) →
  (_≤_ A
    (_+_ A (hysteresisGap H) (hysteresisGap H))
    (_+_ A (scoreModulus H) (scoreModulus H)) → ⊥) →
  ⊥
hysteresisGapExcludesImmediateBackSwitch H gapLargerThanModulus =
  gapLargerThanModulus (twoWayHysteresisRequiresDoubleModulus H)

------------------------------------------------------------------------
-- Status: the separation theorem is checked.  The PDE work must still bound
-- the actual chart-score modulus uniformly and choose a positive hysteresis
-- gap that violates the double-modulus inequality on a short interval.
------------------------------------------------------------------------

hysteresisSeparationAssemblyLevel : ProofLevel
hysteresisSeparationAssemblyLevel = machineChecked
