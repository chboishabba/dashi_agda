module DASHI.Physics.YangMills.BalabanSU2RadialAdjointComposition where

------------------------------------------------------------------------
-- Composition algebra for radial functions of ad_y.
--
-- This is the scalar-facing form of the reduced composition law.  It permits
-- source identities such as g(ad_y) g^{-1}(ad_y) = I to be stated and proved
-- coefficientwise once the three radial coefficient functions are supplied.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  ( _+R_
  ; _*R_
  ; -R_
  ; zeroR
  ; oneR
  )
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  ( SU2LieAlgebra )
open import DASHI.Physics.YangMills.BalabanSU2AdjointCubicReduction using
  ( fourR
  ; adCubicCoefficient
  )
open import DASHI.Physics.YangMills.BalabanSU2ReducedAdjointCalculus using
  ( ReducedAdjointOperator
  ; reducedAd
  ; reducedAdjointExt
  ; applyReducedAdjoint
  ; composeReducedAdjoint
  ; applyReducedComposition
  ; identityReducedAdjoint
  )
open import DASHI.Physics.YangMills.BalabanSU2ReducedAdjointDeterminantProduct using
  ( reducedAdjointDeterminantValue
  ; reducedAdjointDeterminantMultiplicative
  )
open import DASHI.Physics.YangMills.BalabanSU2RadialAdjointOperator using
  ( RadialReducedOperator
  ; radialReduced
  ; identityRadial
  ; linearRadial
  ; quadraticRadial
  ; radialInvariant
  ; evaluateRadialReduced
  ; applyRadialReduced
  )

radialCubicCoefficient : ℝ → ℝ
radialCubicCoefficient radiusSquared =
  -R (fourR *R radiusSquared)

adCubicCoefficientIsRadial :
  ∀ Y →
  adCubicCoefficient Y
    ≡ radialCubicCoefficient (radialInvariant Y)
adCubicCoefficientIsRadial Y = refl

identityRadialReduced : RadialReducedOperator
identityRadialReduced =
  radialReduced
    (λ _ → oneR)
    (λ _ → zeroR)
    (λ _ → zeroR)

composeRadialReduced :
  RadialReducedOperator →
  RadialReducedOperator →
  RadialReducedOperator
composeRadialReduced left right =
  radialReduced
    (λ radius →
      identityRadial left radius *R identityRadial right radius)
    (λ radius →
      ((identityRadial left radius *R linearRadial right radius)
        +R (linearRadial left radius *R identityRadial right radius))
      +R
      (radialCubicCoefficient radius *R
        ((linearRadial left radius *R quadraticRadial right radius)
          +R
         (quadraticRadial left radius *R linearRadial right radius))))
    (λ radius →
      (((identityRadial left radius *R quadraticRadial right radius)
        +R (linearRadial left radius *R linearRadial right radius))
        +R (quadraticRadial left radius *R identityRadial right radius))
      +R
      (radialCubicCoefficient radius *R
        (quadraticRadial left radius *R quadraticRadial right radius)))

evaluateIdentityRadialReduced :
  ∀ Y →
  evaluateRadialReduced identityRadialReduced Y
    ≡ identityReducedAdjoint
evaluateIdentityRadialReduced Y = refl

evaluateComposeRadialReduced :
  ∀ left right Y →
  evaluateRadialReduced (composeRadialReduced left right) Y
  ≡
  composeReducedAdjoint Y
    (evaluateRadialReduced left Y)
    (evaluateRadialReduced right Y)
evaluateComposeRadialReduced left right Y
  rewrite adCubicCoefficientIsRadial Y = refl

applyComposeRadialReduced :
  ∀ left right Y X →
  applyRadialReduced left Y
    (applyRadialReduced right Y X)
  ≡
  applyRadialReduced (composeRadialReduced left right) Y X
applyComposeRadialReduced left right Y X =
  trans
    (applyReducedComposition Y
      (evaluateRadialReduced left Y)
      (evaluateRadialReduced right Y)
      X)
    (cong
      (λ operator → applyReducedAdjoint Y operator X)
      (sym (evaluateComposeRadialReduced left right Y)))
  where
    sym :
      ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
    sym refl = refl

radialDeterminantMultiplicative :
  ∀ left right Y →
  reducedAdjointDeterminantValue Y
    (evaluateRadialReduced (composeRadialReduced left right) Y)
  ≡
  reducedAdjointDeterminantValue Y
    (evaluateRadialReduced left Y)
  *R
  reducedAdjointDeterminantValue Y
    (evaluateRadialReduced right Y)
radialDeterminantMultiplicative left right Y =
  trans
    (cong
      (reducedAdjointDeterminantValue Y)
      (evaluateComposeRadialReduced left right Y))
    (reducedAdjointDeterminantMultiplicative Y
      (evaluateRadialReduced left Y)
      (evaluateRadialReduced right Y))
