{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP119ResidualToRegularEProjectionRound224Exact where

------------------------------------------------------------------------
-- ROUND224 / STRONGER CMP119 RESIDUAL -> PREFERRED REGULAR-E FIBRE
--
-- The full Round219 residual family remains a valid stronger producer.  This
-- adapter projects it to the least-privilege Round221 source fibre so the two
-- routes do not fork or require a second regular-E identity theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact as R219
import DASHI.Physics.YangMills.BalabanCMP119RegularESourceProjectionRound221Exact as ESource

record ResidualRegularEAuthority
    {trajectory split inputs}
    (family : R219.BetaDrivenCMP119ResidualFamily
      {trajectory = trajectory} {split = split} inputs)
    (scale : Nat)
    (density : Beta.Density inputs)
    (regular : R219.RegularTerm family) : Set where
  constructor residualRegularEAuthority
  field
    densityIsSelected : density ≡ Beta.densityAt inputs scale
    regularIsResidualE : regular ≡ R219.regularEAt family scale

open ResidualRegularEAuthority public

regularEProjectionFromResidual :
  ∀ {trajectory split inputs}
    (family : R219.BetaDrivenCMP119ResidualFamily
      {trajectory = trajectory} {split = split} inputs) →
  ESource.CMP119RegularESourceProjection inputs
regularEProjectionFromResidual {inputs = inputs} family = record
  { ESource.CMP119RegularESourceProjection.RegularTerm = R219.RegularTerm family
  ; ESource.CMP119RegularESourceProjection.regularEOfDensity =
      λ scale density → R219.regularEAt family scale
  ; ESource.CMP119RegularESourceProjection.IsCMP119Section2RegularE =
      ResidualRegularEAuthority family
  ; ESource.CMP119RegularESourceProjection.selectedRegularEIsSourceCoordinate =
      λ scale → residualRegularEAuthority refl refl
  }

selectedRegularEIsResidualRegularE :
  ∀ {trajectory split inputs}
    (family : R219.BetaDrivenCMP119ResidualFamily
      {trajectory = trajectory} {split = split} inputs) →
  ∀ scale →
  ESource.selectedRegularE (regularEProjectionFromResidual family) scale
  ≡ R219.regularEAt family scale
selectedRegularEIsResidualRegularE family scale = refl

residualToRegularEProjectionCompilerLevel : ProofLevel
residualToRegularEProjectionCompilerLevel = machineChecked
