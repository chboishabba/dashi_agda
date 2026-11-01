module DASHI.Physics.Closure.ChemistryRightLimitsQuotientCrossBandCandidate256Witness where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Product using (_×_; _,_)
open import Data.Vec using (Vec; _∷_; replicate)

open import DASHI.Physics.Closure.ChemistryRightLimitsQuotientCrossBandCandidate256Shape as Shape
open import DASHI.Physics.Closure.ChemistryRightLimitsQuotientCrossBandCouplingRequirement as Requirement
open import Ontology.DNA.ChemistryQuotient as CDQ
open import Ontology.DNA.ChemistryUVCoordinates as UV

------------------------------------------------------------------------
-- First fully concrete witness candidate for the active atomic blocker lane.
--
-- The current adapted defect/promoted observables are constant on the
-- canonical carrier, so a single-slot `u`-channel flip at fixed `v = purine`
-- is enough to witness genuine quotient and cross-band separation without
-- disturbing the already-landed pair.

rightU256 : CDQ.FeatureU
rightU256 = replicate 256 CDQ.weak

leftU256 : CDQ.FeatureU
leftU256 = CDQ.strong ∷ replicate 255 CDQ.weak

sharedV256 : CDQ.FeatureV
sharedV256 = replicate 256 CDQ.purine

rightUV256 : UV.UVCoordinates 256
rightUV256 = UV.uvCoordinates rightU256 sharedV256

leftUV256 : UV.UVCoordinates 256
leftUV256 = UV.uvCoordinates leftU256 sharedV256

canonicalQuotientCrossBandCandidate256Shape :
  Shape.QuotientCrossBandCandidate256Shape
canonicalQuotientCrossBandCandidate256Shape =
  record
    { index = 0
    ; sharedV = sharedV256
    ; leftU = leftU256
    ; rightU = rightU256
    ; leftUV = leftUV256
    ; rightUV = rightUV256
    }

strongCountSeparates : 1 ≢ 0
strongCountSeparates ()

crossBandCouplingSeparates : 255 ≢ 256
crossBandCouplingSeparates ()

canonicalQuotientCrossBandCouplingCandidate256Witness :
  Requirement.CanonicalQuotientCrossBandCouplingCandidate256
canonicalQuotientCrossBandCouplingCandidate256Witness =
  record
    { leftUV = leftUV256
    ; rightUV = rightUV256
    ; sameDefect = refl
    ; samePromoted = refl
    ; quotientSeparates = strongCountSeparates
    ; crossBandCouplingSeparates = crossBandCouplingSeparates
    }

canonicalQuotientCrossBandCouplingRequirementWitness :
  Requirement.ChemistryRightLimitsQuotientCrossBandCouplingRequirement
canonicalQuotientCrossBandCouplingRequirementWitness =
  Requirement.canonicalCandidate256ToRequirement
    canonicalQuotientCrossBandCouplingCandidate256Witness

canonicalQuotientCrossBandCouplingTheoremWitness :
  Requirement.ChemistryRightLimitsQuotientCrossBandCouplingTheorem
canonicalQuotientCrossBandCouplingTheoremWitness =
  Requirement.crossBandRequirementToTheorem
    canonicalQuotientCrossBandCouplingRequirementWitness

canonicalCandidate256ChemistryRightLimitsLaw :
  Requirement.ChemistryRightLimitsLaw
    canonicalQuotientCrossBandCouplingRequirementWitness
canonicalCandidate256ChemistryRightLimitsLaw =
  Requirement.requirementToChemistryRightLimitsLaw
    canonicalQuotientCrossBandCouplingRequirementWitness

canonicalCrossBandInvariant :
  CDQ.ChemistryFeature × CDQ.ChemistryFeature → Nat
canonicalCrossBandInvariant (f , g) =
  Requirement.canonicalCrossBandCoupling f
  +
  Requirement.canonicalCrossBandCoupling g

canonicalCrossBandInvariantSymmetricAtWitness :
  canonicalCrossBandInvariant
    (UV.feature256 leftUV256 , UV.feature256 rightUV256)
  ≡
  canonicalCrossBandInvariant
    (UV.feature256 rightUV256 , UV.feature256 leftUV256)
canonicalCrossBandInvariantSymmetricAtWitness = refl

canonicalCrossBandInvariantBandSensitive :
  canonicalCrossBandInvariant
    (UV.feature256 leftUV256 , UV.feature256 leftUV256)
  ≢
  canonicalCrossBandInvariant
    (UV.feature256 rightUV256 , UV.feature256 rightUV256)
canonicalCrossBandInvariantBandSensitive ()

canonicalCandidate256QuotientCrossBandLaw :
  Requirement.ChemistryRightLimitsQuotientCrossBandLaw
canonicalCandidate256QuotientCrossBandLaw =
  Requirement.requirementToQuotientCrossBandLaw
    canonicalQuotientCrossBandCouplingRequirementWitness
    canonicalCrossBandInvariant
    canonicalCrossBandInvariantSymmetricAtWitness
    canonicalCrossBandInvariantBandSensitive
