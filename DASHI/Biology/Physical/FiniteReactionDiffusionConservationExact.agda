module DASHI.Biology.Physical.FiniteReactionDiffusionConservationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Alan M. Turing,
-- "The Chemical Basis of Morphogenesis",
-- Philosophical Transactions of the Royal Society B 237 (1952), 37-72.
-- DOI: 10.1098/rstb.1952.0012.
--
-- DASHI CONTRIBUTION
--
-- A finite two-compartment transport/reaction regression.  Diffusion moves one
-- concentration quantum from the left compartment to the right when one is
-- available; the move conserves total material exactly.  A source operator is
-- then composed with transport and the resulting balance theorem states that
-- the total after one driven step is the previous total plus the declared
-- source.  This is the finite conservative core needed before importing richer
-- reaction-diffusion mode/Hodge machinery.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.Physical.SIBiologyDimensionsExact as BioSI
import DASHI.Physics.Units.SI as SI
import DASHI.Physics.Laws.ContinuumMaterialLaws as Continuum
import DASHI.Biology.Morphogenesis.ReactionDiffusionHodgeBridge as Hodge

record TwoCompartment : Set where
  constructor twoCompartment
  field
    left right : Nat

open TwoCompartment public

totalMaterial : TwoCompartment → Nat
totalMaterial (twoCompartment l r) = l + r

-- One directed Fick-like exchange quantum.  The theorem below is about exact
-- conservation, not about claiming this unit-step rule is a calibrated Fick
-- constitutive law.
diffuseLeftToRight : TwoCompartment → TwoCompartment
diffuseLeftToRight (twoCompartment zero r) = twoCompartment zero r
diffuseLeftToRight (twoCompartment (suc l) r) = twoCompartment l (suc r)

diffusionConservesTotal :
  (x : TwoCompartment) →
  totalMaterial (diffuseLeftToRight x) ≡ totalMaterial x
diffusionConservesTotal (twoCompartment zero r) = refl
diffusionConservesTotal (twoCompartment (suc l) r)
  rewrite +-suc l r = refl

sourceIntoLeft : Nat → TwoCompartment → TwoCompartment
sourceIntoLeft q (twoCompartment l r) = twoCompartment (q + l) r

sourceBalance :
  (q : Nat) (x : TwoCompartment) →
  totalMaterial (sourceIntoLeft q x) ≡ q + totalMaterial x
sourceBalance q (twoCompartment l r) = +-assoc q l r

drivenReactionDiffusionStep : Nat → TwoCompartment → TwoCompartment
drivenReactionDiffusionStep q x = sourceIntoLeft q (diffuseLeftToRight x)

drivenStepBalance :
  (q : Nat) (x : TwoCompartment) →
  totalMaterial (drivenReactionDiffusionStep q x)
    ≡ q + totalMaterial x
drivenStepBalance q x
  rewrite sourceBalance q (diffuseLeftToRight x)
        | diffusionConservesTotal x = refl

------------------------------------------------------------------------
-- SI signature of the continuum law that this finite regression approximates.
------------------------------------------------------------------------

record ReactionDiffusionSISignature : Set₁ where
  field
    concentration : Set
    molarFlux : Set
    diffusivity : Set
    reactionRate : Set

    concentrationIsSI : concentration ≡ SI.Quantity SI.MolarConcentration SI.unitScale
    molarFluxIsSI : molarFlux ≡ SI.Quantity BioSI.MolarFlux SI.unitScale
    diffusivityIsSI : diffusivity ≡ SI.Quantity BioSI.Diffusivity SI.unitScale
    reactionRateIsSI : reactionRate ≡ SI.Quantity BioSI.MolarReactionRate SI.unitScale

open ReactionDiffusionSISignature public

canonicalReactionDiffusionSISignature : ReactionDiffusionSISignature
canonicalReactionDiffusionSISignature = record
  { concentration = SI.Quantity SI.MolarConcentration SI.unitScale
  ; molarFlux = SI.Quantity BioSI.MolarFlux SI.unitScale
  ; diffusivity = SI.Quantity BioSI.Diffusivity SI.unitScale
  ; reactionRate = SI.Quantity BioSI.MolarReactionRate SI.unitScale
  ; concentrationIsSI = refl
  ; molarFluxIsSI = refl
  ; diffusivityIsSI = refl
  ; reactionRateIsSI = refl
  }

------------------------------------------------------------------------
-- Existing physics is imported rather than replaced:
-- Continuum.ReactionDiffusionLaw owns the general balance/closure surface and
-- Hodge owns the finite linearised coercivity bridge.
------------------------------------------------------------------------
