module DASHI.Physics.Chemistry.Nobel2026KaganSoaiAsymmetricAutocatalysisExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Chemistry.AsymmetricChiralDynamicsExact as Dynamics
import DASHI.Biology.Origins.AutocatalyticCompartmentBoundary as Origins

------------------------------------------------------------------------
-- 2026 NOBEL CHEMISTRY: KAGAN + SOAI
--
-- Source role is kept separate from theorem authority.  The formal layer below
-- captures finite exact consequences of a mirror-symmetric nonlinear response
-- and product-fed autocatalysis.  It does not reproduce the experimental rate
-- law, aggregation mechanism, organozinc chemistry or a universal origin-of-
-- life model.
------------------------------------------------------------------------

record SourceCoordinate : Set where
  constructor sourceCoordinate
  field
    label : String
    authors : String
    publication : String
    year : Nat
    doi : String
    sourceRole : String

nobel2026Source : SourceCoordinate
nobel2026Source =
  sourceCoordinate
    "2026 Nobel Prize in Chemistry"
    "Henri Kagan; Kenso Soai"
    "Royal Swedish Academy of Sciences / Nobel Prize announcement"
    2026
    "award citation: discovery of non-linear effects and autocatalysis in asymmetric organic synthesis"
    "award/attribution coordinate; does not import the experimental theorem into Agda"

kagan1986Source : SourceCoordinate
kagan1986Source =
  sourceCoordinate
    "Nonlinear effects in asymmetric synthesis"
    "C. Puchot; O. Samuel; E. Dunach; S. Zhao; C. Agami; H. B. Kagan"
    "Journal of the American Chemical Society 108(9), 2353-2357"
    1986
    "10.1021/ja00269a036"
    "primary nonlinear-effect source"

soai1995Source : SourceCoordinate
soai1995Source =
  sourceCoordinate
    "Asymmetric autocatalysis and amplification of enantiomeric excess of a chiral molecule"
    "Kenso Soai; Takanori Shibata; Hiroshi Morioka; Kaori Choji"
    "Nature 378, 767-768"
    1995
    "10.1038/378767a0"
    "primary asymmetric-autocatalysis source"

frank1953Source : SourceCoordinate
frank1953Source =
  sourceCoordinate
    "On spontaneous asymmetric synthesis"
    "F. C. Frank"
    "Biochimica et Biophysica Acta 11, 459-463"
    1953
    "10.1016/0006-3002(53)90082-1"
    "historical theoretical instability/autocatalysis precedent"

------------------------------------------------------------------------
-- FINITE KAGAN NONLINEAR-EFFECT WITNESS
--
-- The response keeps handedness but increases the finite magnitude code from
-- seed=1 to product=2.  That is enough to refute the identity/one-to-one copy
-- model on this fixture.  It is intentionally weaker than a theorem about a
-- continuous ee-response curve.
------------------------------------------------------------------------

data CatalystBias : Set where
  leftCatalystSeed : CatalystBias
  racemicCatalyst : CatalystBias
  rightCatalystSeed : CatalystBias

data ProductBias : Set where
  leftProductAmplified : ProductBias
  racemicProduct : ProductBias
  rightProductAmplified : ProductBias

mirrorCatalyst : CatalystBias → CatalystBias
mirrorCatalyst leftCatalystSeed = rightCatalystSeed
mirrorCatalyst racemicCatalyst = racemicCatalyst
mirrorCatalyst rightCatalystSeed = leftCatalystSeed

mirrorProduct : ProductBias → ProductBias
mirrorProduct leftProductAmplified = rightProductAmplified
mirrorProduct racemicProduct = racemicProduct
mirrorProduct rightProductAmplified = leftProductAmplified

kaganResponse : CatalystBias → ProductBias
kaganResponse leftCatalystSeed = leftProductAmplified
kaganResponse racemicCatalyst = racemicProduct
kaganResponse rightCatalystSeed = rightProductAmplified

kaganResponseMirrorEquivariant :
  (x : CatalystBias) →
  kaganResponse (mirrorCatalyst x) ≡ mirrorProduct (kaganResponse x)
kaganResponseMirrorEquivariant leftCatalystSeed = refl
kaganResponseMirrorEquivariant racemicCatalyst = refl
kaganResponseMirrorEquivariant rightCatalystSeed = refl

catalystMagnitudeCode : CatalystBias → Nat
catalystMagnitudeCode leftCatalystSeed = 1
catalystMagnitudeCode racemicCatalyst = 0
catalystMagnitudeCode rightCatalystSeed = 1

productMagnitudeCode : ProductBias → Nat
productMagnitudeCode leftProductAmplified = 2
productMagnitudeCode racemicProduct = 0
productMagnitudeCode rightProductAmplified = 2

leftPositiveNonlinearWitness :
  productMagnitudeCode (kaganResponse leftCatalystSeed) ≡ 2
leftPositiveNonlinearWitness = refl

rightPositiveNonlinearWitness :
  productMagnitudeCode (kaganResponse rightCatalystSeed) ≡ 2
rightPositiveNonlinearWitness = refl

------------------------------------------------------------------------
-- FINITE SOAI AUTOCATALYTIC WITNESS
--
-- Product handedness is fed back into the next catalyst state.  The resulting
-- state step is literally the reusable mirror-equivariant amplification owner.
------------------------------------------------------------------------

productToNextState : ProductBias → Dynamics.ChiralBiasState
productToNextState leftProductAmplified = Dynamics.leftAmplified
productToNextState racemicProduct = Dynamics.racemic
productToNextState rightProductAmplified = Dynamics.rightAmplified

seedToCatalyst : Dynamics.ChiralBiasState → CatalystBias
seedToCatalyst Dynamics.leftAmplified = leftCatalystSeed
seedToCatalyst Dynamics.leftSeed = leftCatalystSeed
seedToCatalyst Dynamics.racemic = racemicCatalyst
seedToCatalyst Dynamics.rightSeed = rightCatalystSeed
seedToCatalyst Dynamics.rightAmplified = rightCatalystSeed

soaiStep : Dynamics.ChiralBiasState → Dynamics.ChiralBiasState
soaiStep x = productToNextState (kaganResponse (seedToCatalyst x))

soaiLeftSeedAmplifies : soaiStep Dynamics.leftSeed ≡ Dynamics.leftAmplified
soaiLeftSeedAmplifies = refl

soaiRightSeedAmplifies : soaiStep Dynamics.rightSeed ≡ Dynamics.rightAmplified
soaiRightSeedAmplifies = refl

soaiRacemicFixed : soaiStep Dynamics.racemic ≡ Dynamics.racemic
soaiRacemicFixed = refl

soaiMirrorEquivariant :
  (x : Dynamics.ChiralBiasState) →
  soaiStep (Dynamics.mirrorBias x) ≡ Dynamics.mirrorBias (soaiStep x)
soaiMirrorEquivariant Dynamics.leftAmplified = refl
soaiMirrorEquivariant Dynamics.leftSeed = refl
soaiMirrorEquivariant Dynamics.racemic = refl
soaiMirrorEquivariant Dynamics.rightSeed = refl
soaiMirrorEquivariant Dynamics.rightAmplified = refl

------------------------------------------------------------------------
-- Origins-of-life boundary reuse.
------------------------------------------------------------------------

originBoundary : Origins.OriginPromotionBoundary → Origins.OriginPromotionBoundary
originBoundary x = x

record Nobel2026AsymmetricAutocatalysisBoundary : Set where
  constructor nobel2026AsymmetricAutocatalysisBoundary
  field
    nonlinearAmplificationRepresented : Bool
    nonlinearAmplificationRepresentedIsTrue :
      nonlinearAmplificationRepresented ≡ true

    productFedAutocatalysisRepresented : Bool
    productFedAutocatalysisRepresentedIsTrue :
      productFedAutocatalysisRepresented ≡ true

    lawCanRemainMirrorEquivariant : Bool
    lawCanRemainMirrorEquivariantIsTrue : lawCanRemainMirrorEquivariant ≡ true

    symmetricLawForcesSymmetricTrajectory : Bool
    symmetricLawForcesSymmetricTrajectoryIsFalse :
      symmetricLawForcesSymmetricTrajectory ≡ false

    nobelChemistryProvesBiologicalHomochiralityOrigin : Bool
    nobelChemistryProvesBiologicalHomochiralityOriginIsFalse :
      nobelChemistryProvesBiologicalHomochiralityOrigin ≡ false

    autocatalysisProvesLife : Bool
    autocatalysisProvesLifeIsFalse : autocatalysisProvesLife ≡ false

    finiteFixtureReproducesExperimentalKinetics : Bool
    finiteFixtureReproducesExperimentalKineticsIsFalse :
      finiteFixtureReproducesExperimentalKinetics ≡ false

canonicalNobel2026AsymmetricAutocatalysisBoundary :
  Nobel2026AsymmetricAutocatalysisBoundary
canonicalNobel2026AsymmetricAutocatalysisBoundary =
  nobel2026AsymmetricAutocatalysisBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
