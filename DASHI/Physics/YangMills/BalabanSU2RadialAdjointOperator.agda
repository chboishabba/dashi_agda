module DASHI.Physics.YangMills.BalabanSU2RadialAdjointOperator where

------------------------------------------------------------------------
-- Radial reduced functions of ad_y.
--
-- Every conjugation-equivariant scalar function of the concrete su(2)
-- adjoint map has the reduced form
--
--   a(<y,y>) I + b(<y,y>) ad_y + c(<y,y>) ad_y^2.
--
-- The scalar coefficient functions remain ordinary explicit parameters.  This
-- module proves the resulting operator, its action, and its determinant are
-- gauge covariant/invariant.  It is therefore a non-analytic construction
-- layer into which the source functions g, g^{-1}, and exp can later be
-- inserted without hiding their scalar definitions or estimates.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  ( SU2LieAlgebra
  ; su2Adjoint
  )
open import DASHI.Physics.YangMills.BalabanSU2AdjointInnerProduct using
  ( su2Dot
  ; su2DotAdjointInvariant
  )
open import DASHI.Physics.YangMills.BalabanSU2ReducedAdjointCalculus using
  ( ReducedAdjointOperator
  ; reducedAd
  ; reducedAdjointExt
  ; applyReducedAdjoint
  )
open import DASHI.Physics.YangMills.BalabanSU2AdjointMatrixDeterminant using
  ( determinantMatrix3
  ; reducedAdjointMatrix
  )
open import DASHI.Physics.YangMills.BalabanSU2ReducedAdjointGaugeCovariance using
  ( applyReducedAdjointGaugeCovariant
  ; reducedAdjointMatrixDeterminantGaugeInvariant
  )

record RadialReducedOperator : Set₁ where
  constructor radialReduced
  field
    identityRadial : ℝ → ℝ
    linearRadial : ℝ → ℝ
    quadraticRadial : ℝ → ℝ

open RadialReducedOperator public

radialInvariant : SU2LieAlgebra → ℝ
radialInvariant Y = su2Dot Y Y

evaluateRadialReduced :
  RadialReducedOperator →
  SU2LieAlgebra →
  ReducedAdjointOperator
evaluateRadialReduced radial Y =
  reducedAd
    (identityRadial radial (radialInvariant Y))
    (linearRadial radial (radialInvariant Y))
    (quadraticRadial radial (radialInvariant Y))

radialInvariantGaugeInvariant :
  ∀ u Y →
  radialInvariant (su2Adjoint u Y) ≡ radialInvariant Y
radialInvariantGaugeInvariant u Y =
  su2DotAdjointInvariant u Y Y

evaluateRadialReducedGaugeInvariant :
  ∀ radial u Y →
  evaluateRadialReduced radial (su2Adjoint u Y)
    ≡ evaluateRadialReduced radial Y
evaluateRadialReducedGaugeInvariant radial u Y
  rewrite radialInvariantGaugeInvariant u Y = refl

applyRadialReduced :
  RadialReducedOperator →
  SU2LieAlgebra →
  SU2LieAlgebra →
  SU2LieAlgebra
applyRadialReduced radial Y X =
  applyReducedAdjoint Y (evaluateRadialReduced radial Y) X

applyRadialReducedGaugeCovariant :
  ∀ radial u Y X →
  su2Adjoint u (applyRadialReduced radial Y X)
  ≡
  applyRadialReduced radial
    (su2Adjoint u Y)
    (su2Adjoint u X)
applyRadialReducedGaugeCovariant radial u Y X =
  trans
    (applyReducedAdjointGaugeCovariant
      u Y (evaluateRadialReduced radial Y) X)
    (cong
      (λ operator →
        applyReducedAdjoint
          (su2Adjoint u Y)
          operator
          (su2Adjoint u X))
      (sym (evaluateRadialReducedGaugeInvariant radial u Y)))

radialReducedDeterminant :
  RadialReducedOperator →
  SU2LieAlgebra →
  ℝ
radialReducedDeterminant radial Y =
  determinantMatrix3
    (reducedAdjointMatrix Y (evaluateRadialReduced radial Y))

radialReducedDeterminantGaugeInvariant :
  ∀ radial u Y →
  radialReducedDeterminant radial (su2Adjoint u Y)
    ≡ radialReducedDeterminant radial Y
radialReducedDeterminantGaugeInvariant radial u Y =
  trans
    (cong
      (determinantMatrix3 ∘ reducedAdjointMatrix (su2Adjoint u Y))
      (evaluateRadialReducedGaugeInvariant radial u Y))
    (reducedAdjointMatrixDeterminantGaugeInvariant
      u Y (evaluateRadialReduced radial Y))
  where
    _∘_ :
      ∀ {A B C : Set} →
      (B → C) → (A → B) → A → C
    (f ∘ g) x = f (g x)
