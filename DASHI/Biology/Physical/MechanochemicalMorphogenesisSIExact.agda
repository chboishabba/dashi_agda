module DASHI.Biology.Physical.MechanochemicalMorphogenesisSIExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
-- Alan M. Turing, "The Chemical Basis of Morphogenesis",
-- Philosophical Transactions of the Royal Society B 237 (1952), 37-72.
-- DOI: 10.1098/rstb.1952.0012.
--
-- DASHI CONTRIBUTION
-- Couple the existing continuum/reaction-diffusion owners to SI-typed tissue
-- mechanics and give a finite positional-information regression: organ type is
-- held fixed while morphogen-field geometry changes the decoded anchor.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Int using (pos; negsuc)

import DASHI.Physics.Units.SI as SI
import DASHI.Biology.Physical.SIBiologyDimensionsExact as BioSI
import DASHI.Physics.Laws.ContinuumMaterialLaws as Continuum
import DASHI.Biology.Morphogenesis.ReactionDiffusionModeSelection as Modes
import DASHI.Biology.Physical.DevelopmentalGoalFactorizationExact as Goal

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

MassDensity : SI.Dimension
MassDensity =
  SI.dim (negsuc (suc zero)) (pos (suc zero))
    (pos zero) (pos zero) (pos zero) (pos zero) (pos zero)

record TissueMechanicsSISignature : Set₁ where
  field
    density : Set
    velocity : Set
    stress : Set
    forceDensity : Set
    strain : Set

    densityDimension : SI.Dimension
    densityDimensionIsMassPerVolume : densityDimension ≡ MassDensity

    densityIsSI : density ≡ SI.Quantity MassDensity SI.unitScale
    velocityIsSI : velocity ≡ SI.Quantity SI.Velocity SI.unitScale
    stressIsSI : stress ≡ SI.Quantity SI.Pressure SI.unitScale
    forceDensityIsSI : forceDensity ≡ SI.Quantity BioSI.ForceDensity SI.unitScale
    strainIsDimensionless : strain ≡ SI.Quantity SI.Dimensionless SI.unitScale

open TissueMechanicsSISignature public

canonicalTissueMechanicsSISignature : TissueMechanicsSISignature
canonicalTissueMechanicsSISignature = record
  { density = SI.Quantity MassDensity SI.unitScale
  ; velocity = SI.Quantity SI.Velocity SI.unitScale
  ; stress = SI.Quantity SI.Pressure SI.unitScale
  ; forceDensity = SI.Quantity BioSI.ForceDensity SI.unitScale
  ; strain = SI.Quantity SI.Dimensionless SI.unitScale
  ; densityDimension = MassDensity
  ; densityDimensionIsMassPerVolume = refl
  ; densityIsSI = refl
  ; velocityIsSI = refl
  ; stressIsSI = refl
  ; forceDensityIsSI = refl
  ; strainIsDimensionless = refl
  }

------------------------------------------------------------------------
-- Finite spatial-field decoding.
------------------------------------------------------------------------

record TwoSiteMorphogenField : Set where
  constructor twoSiteMorphogenField
  field
    proximal distal : Bool

open TwoSiteMorphogenField public

decodeAnchor : TwoSiteMorphogenField → Bool
decodeAnchor (twoSiteMorphogenField proximal false) = false
decodeAnchor (twoSiteMorphogenField proximal true) = true

handGoalFromField : TwoSiteMorphogenField → Goal.DevelopmentalGoal
handGoalFromField field =
  Goal.developmentalGoal Goal.hand (decodeAnchor field) false Goal.leftSide 1

proximalField distalField : TwoSiteMorphogenField
proximalField = twoSiteMorphogenField true false
distalField = twoSiteMorphogenField true true

sameOrganDifferentFieldLocation :
  Goal.genericOrgan (handGoalFromField proximalField)
  ≡ Goal.genericOrgan (handGoalFromField distalField)
sameOrganDifferentFieldLocation = refl

fieldGeometryChangesAnchor :
  Goal.anchor (handGoalFromField proximalField)
  ≢ Goal.anchor (handGoalFromField distalField)
fieldGeometryChangesAnchor ()

------------------------------------------------------------------------
-- Existing owner boundary: continuum momentum balance and reaction-diffusion
-- instability remain in Continuum/Modes.  This module supplies the dimensional
-- and relational adapter, not a replacement constitutive law.
------------------------------------------------------------------------
