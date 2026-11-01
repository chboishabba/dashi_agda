module DASHI.Physics.YangMills.BalabanSU2ConditionalCovarianceFormula where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

record ConditionalCovarianceData
  {f c : Level}
  (Fine : Set f)
  (Coarse : Set c) : Set (lsuc (f ⊔ c)) where
  field
    propagator : Fine → Fine
    average : Fine → Coarse
    averageStar : Coarse → Fine
    middleInverse : Coarse → Coarse
    fineSubtract : Fine → Fine → Fine
    coarseSubtract : Coarse → Coarse → Coarse
    coarseZero : Coarse
    averageSubtract : ∀ left right →
      average (fineSubtract left right)
        ≡ coarseSubtract (average left) (average right)
    coarseSubtractSelf : ∀ value → coarseSubtract value value ≡ coarseZero
    constrainedLift : Coarse → Fine
    constrainedLiftDefinition : ∀ coarse →
      constrainedLift coarse
        ≡ propagator (averageStar (middleInverse coarse))
    constrainedLiftRightInverse : ∀ coarse →
      average (constrainedLift coarse) ≡ coarse
open ConditionalCovarianceData public

conditionalCovariance :
  ∀ {f c} {Fine : Set f} {Coarse : Set c} →
  ConditionalCovarianceData Fine Coarse → Fine → Fine
conditionalCovariance bundle source =
  fineSubtract bundle
    (propagator bundle source)
    (constrainedLift bundle
      (average bundle (propagator bundle source)))

conditionalCovarianceConstraint :
  ∀ {f c} {Fine : Set f} {Coarse : Set c}
  (bundle : ConditionalCovarianceData Fine Coarse) →
  ∀ source →
  average bundle (conditionalCovariance bundle source)
    ≡ coarseZero bundle
conditionalCovarianceConstraint bundle source =
  trans
    (averageSubtract bundle
      (propagator bundle source)
      (constrainedLift bundle
        (average bundle (propagator bundle source))))
    (trans
      (cong
        (coarseSubtract bundle
          (average bundle (propagator bundle source)))
        (constrainedLiftRightInverse bundle
          (average bundle (propagator bundle source))))
      (coarseSubtractSelf bundle
        (average bundle (propagator bundle source))))

-- The same construction also kills a source already in the lifted coarse
-- sector once the propagator/lift compatibility is supplied.  This is the
-- finite algebraic content of C Q* = 0.
conditionalCovarianceKillsLiftedSource :
  ∀ {f c} {Fine : Set f} {Coarse : Set c}
  (bundle : ConditionalCovarianceData Fine Coarse) →
  (fineZero : Fine) →
  (∀ value → fineSubtract bundle value value ≡ fineZero) →
  (∀ coarse →
    propagator bundle (averageStar bundle coarse)
      ≡ constrainedLift bundle
          (average bundle
            (propagator bundle (averageStar bundle coarse)))) →
  ∀ coarse →
  conditionalCovariance bundle (averageStar bundle coarse) ≡ fineZero
conditionalCovarianceKillsLiftedSource
  bundle fineZero subtractSelf propagatorLifted coarse =
  trans
    (cong
      (λ left →
        fineSubtract bundle left
          (constrainedLift bundle
            (average bundle
              (propagator bundle (averageStar bundle coarse)))))
      (propagatorLifted coarse))
    (subtractSelf
      (constrainedLift bundle
        (average bundle
          (propagator bundle (averageStar bundle coarse)))))
