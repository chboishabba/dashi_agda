{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP119RegularESourceProjectionRound221Exact where

------------------------------------------------------------------------
-- ROUND221 / CONSUMER-INDEXED CMP119 REGULAR-E SOURCE FIBRE
--
-- CMP119 Sect.2 gives each complete density rho_k a regular, fully-renormalized
-- small-field sector E_k; (2.25)--(2.29) then localize that E sector.  CMP109
-- Eq.(5.1) differentiates this regular E object, not the full complete action.
--
-- Therefore BC1 does not need T_k, R_k, B_k or the full action algebra merely
-- to identify its source potential.  The preferred source fibre records only
-- the pre-existing source projection
--
--   (k, rho_k) |-> E_k
--
-- and a source-authority predicate saying that this is the CMP119 Sect.2
-- regular-E coordinate.  The projection is fixed before any BC1 target exists,
-- avoiding the circular "choose E to equal BC1" construction audited earlier.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta

record CMP119RegularESourceProjection
    {trajectory split}
    (inputs : Beta.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}) : Set₁ where
  field
    RegularTerm : Set

    regularEOfDensity : Nat → Beta.Density inputs → RegularTerm

    IsCMP119Section2RegularE :
      Nat → Beta.Density inputs → RegularTerm → Set

    selectedRegularEIsSourceCoordinate : ∀ scale →
      IsCMP119Section2RegularE scale
        (Beta.densityAt inputs scale)
        (regularEOfDensity scale (Beta.densityAt inputs scale))

open CMP119RegularESourceProjection public

selectedRegularE :
  ∀ {trajectory split inputs} →
  CMP119RegularESourceProjection
    {trajectory = trajectory} {split = split} inputs →
  Nat → RegularTerm _
selectedRegularE {inputs = inputs} projection scale =
  regularEOfDensity projection scale (Beta.densityAt inputs scale)

selectedRegularEHasSourceAuthority :
  ∀ {trajectory split inputs}
    (projection : CMP119RegularESourceProjection
      {trajectory = trajectory} {split = split} inputs) →
  ∀ scale →
  IsCMP119Section2RegularE projection scale
    (Beta.densityAt inputs scale)
    (selectedRegularE projection scale)
selectedRegularEHasSourceAuthority projection scale =
  selectedRegularEIsSourceCoordinate projection scale

cmp119RegularESourceProjectionCompilerLevel : ProofLevel
cmp119RegularESourceProjectionCompilerLevel = machineChecked

-- Source authority: CMP119 Sect.2 explicitly identifies the regular E_k sector
-- inside the complete density and gives its localized analytic representation.
cmp119RegularESectorSourceLevel : ProofLevel
cmp119RegularESectorSourceLevel = standardImported

-- Repository/source realization leaf: bind the abstract beta-driven Density
-- carrier to that literal source projection.  This is strictly weaker than
-- constructing every T/A/R/B/vacuum coordinate of the complete density.
literalCMP119RegularESourceProjectionLevel : ProofLevel
literalCMP119RegularESourceProjectionLevel = conditional
