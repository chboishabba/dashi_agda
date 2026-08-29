{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanRowAShootingTubeFromBetaBoundsRound102Exact where

------------------------------------------------------------------------
-- ROUND102 A: TWO-SIDED CUMULATIVE BETA BOUNDS MAKE THE SHOOTING TUBE INVARIANT
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; _+ℝ_; _≤ℝ_; ≤ℝ-refl; +-mono-≤)
open import DASHI.Physics.YangMills.CompactLieProofLevel

record ShootingTubeBounds (Point : Set) : Set₁ where
  field
    coordinate : Point → ℝ
    renormalisationMap : Point → Point
    renormalisedInverseSquare : ℝ
    cumulativeBeta : Point → ℝ

    lowerPrefix upperPrefix : ℝ
    lowerBelowUpper : lowerPrefix ≤ℝ upperPrefix

    cumulativeLower : ∀ u → lowerPrefix ≤ℝ cumulativeBeta u
    cumulativeUpper : ∀ u → cumulativeBeta u ≤ℝ upperPrefix

    mapFormula : ∀ u →
      coordinate (renormalisationMap u)
      ≡ renormalisedInverseSquare +ℝ cumulativeBeta u

open ShootingTubeBounds public

lowerEndpoint : ∀ {Point} → ShootingTubeBounds Point → ℝ
lowerEndpoint dataSet = renormalisedInverseSquare dataSet +ℝ lowerPrefix dataSet

upperEndpoint : ∀ {Point} → ShootingTubeBounds Point → ℝ
upperEndpoint dataSet = renormalisedInverseSquare dataSet +ℝ upperPrefix dataSet

endpointsOrdered :
  ∀ {Point} (dataSet : ShootingTubeBounds Point) →
  lowerEndpoint dataSet ≤ℝ upperEndpoint dataSet
endpointsOrdered dataSet =
  +-mono-≤ ≤ℝ-refl (lowerBelowUpper dataSet)

mapAboveLowerEndpoint :
  ∀ {Point} (dataSet : ShootingTubeBounds Point) u →
  lowerEndpoint dataSet ≤ℝ coordinate dataSet (renormalisationMap dataSet u)
mapAboveLowerEndpoint dataSet u =
  subst
    (λ right → lowerEndpoint dataSet ≤ℝ right)
    (sym (mapFormula dataSet u))
    (+-mono-≤ ≤ℝ-refl (cumulativeLower dataSet u))

mapBelowUpperEndpoint :
  ∀ {Point} (dataSet : ShootingTubeBounds Point) u →
  coordinate dataSet (renormalisationMap dataSet u) ≤ℝ upperEndpoint dataSet
mapBelowUpperEndpoint dataSet u =
  subst
    (λ left → left ≤ℝ upperEndpoint dataSet)
    (sym (mapFormula dataSet u))
    (+-mono-≤ ≤ℝ-refl (cumulativeUpper dataSet u))

mapInsideTube :
  ∀ {Point} (dataSet : ShootingTubeBounds Point) u →
  lowerEndpoint dataSet ≤ℝ coordinate dataSet (renormalisationMap dataSet u)
  × coordinate dataSet (renormalisationMap dataSet u) ≤ℝ upperEndpoint dataSet
mapInsideTube dataSet u =
  mapAboveLowerEndpoint dataSet u , mapBelowUpperEndpoint dataSet u

shootingTubeFromBetaBoundsLevel : ProofLevel
shootingTubeFromBetaBoundsLevel = machineChecked

literalCMP109BetaBoundsGiveShootingSelfMapLevel : ProofLevel
literalCMP109BetaBoundsGiveShootingSelfMapLevel = machineChecked
