module DASHI.Physics.YangMills.BalabanSU2RadialAdjointInverse where

------------------------------------------------------------------------
-- Pointwise inverse criterion for radial reduced adjoint operators.
--
-- No reciprocal operation is postulated.  Instead, three explicit scalar
-- equations at r = <y,y> are shown to be exactly sufficient for the two
-- reduced operators to compose to the identity.  The future g/g^{-1} lane must
-- prove these equations from the actual scalar functions.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  ( _+R_
  ; _*R_
  ; zeroR
  ; oneR
  )
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  ( SU2LieAlgebra )
open import DASHI.Physics.YangMills.BalabanSU2ReducedAdjointCalculus using
  ( reducedAdjointExt
  ; applyReducedAdjoint
  ; identityReducedAdjoint
  ; applyIdentityReducedAdjoint
  )
open import DASHI.Physics.YangMills.BalabanSU2RadialAdjointOperator using
  ( RadialReducedOperator
  ; identityRadial
  ; linearRadial
  ; quadraticRadial
  ; radialInvariant
  ; evaluateRadialReduced
  )
open import DASHI.Physics.YangMills.BalabanSU2RadialAdjointComposition using
  ( radialCubicCoefficient
  ; composeRadialReduced
  ; evaluateComposeRadialReduced
  )

RadialInverseAt :
  RadialReducedOperator →
  RadialReducedOperator →
  ℝ →
  Set
RadialInverseAt left right radius =
  (identityRadial left radius *R identityRadial right radius ≡ oneR)
  ×
  ((((identityRadial left radius *R linearRadial right radius)
      +R (linearRadial left radius *R identityRadial right radius))
    +R
    (radialCubicCoefficient radius *R
      ((linearRadial left radius *R quadraticRadial right radius)
        +R
       (quadraticRadial left radius *R linearRadial right radius))))
    ≡ zeroR)
  ×
  (((((identityRadial left radius *R quadraticRadial right radius)
      +R (linearRadial left radius *R linearRadial right radius))
      +R (quadraticRadial left radius *R identityRadial right radius))
    +R
    (radialCubicCoefficient radius *R
      (quadraticRadial left radius *R quadraticRadial right radius)))
    ≡ zeroR)

radialInverseEvaluatesToIdentity :
  ∀ left right Y →
  RadialInverseAt left right (radialInvariant Y) →
  evaluateRadialReduced (composeRadialReduced left right) Y
    ≡ identityReducedAdjoint
radialInverseEvaluatesToIdentity left right Y equations =
  reducedAdjointExt
    (proj₁ equations)
    (proj₁ (proj₂ equations))
    (proj₂ (proj₂ equations))

applyRadialInverse :
  ∀ left right Y X →
  RadialInverseAt left right (radialInvariant Y) →
  applyReducedAdjoint Y (evaluateRadialReduced left Y)
    (applyReducedAdjoint Y (evaluateRadialReduced right Y) X)
  ≡ X
applyRadialInverse left right Y X equations =
  trans
    (DASHI.Physics.YangMills.BalabanSU2ReducedAdjointCalculus.applyReducedComposition
      Y
      (evaluateRadialReduced left Y)
      (evaluateRadialReduced right Y)
      X)
    (trans
      (cong
        (λ operator → applyReducedAdjoint Y operator X)
        (trans
          (DASHI.Relation.Binary.PropositionalEquality.sym
            (evaluateComposeRadialReduced left right Y))
          (radialInverseEvaluatesToIdentity left right Y equations)))
      (applyIdentityReducedAdjoint Y X))
