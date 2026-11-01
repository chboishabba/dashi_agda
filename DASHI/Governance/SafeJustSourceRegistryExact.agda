module DASHI.Governance.SafeJustSourceRegistryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE REGISTRY: SAFE-AND-JUST DEVELOPMENT / POST-GROWTH LINEAGE
--
-- Source roles are deliberately bounded.  Empirical association, allocation
-- conventions, review synthesis and normative transition proposals are not
-- interchangeable proof authorities.
------------------------------------------------------------------------

record SourceReference : Set where
  constructor sourceReference
  field
    authors : String
    title : String
    venue : String
    year : Nat
    doi : String
    sourceClass : String
    boundedRole : String

open SourceReference public

oneill2018 : SourceReference
oneill2018 = sourceReference
  "Daniel W. O'Neill; Andrew L. Fanning; William F. Lamb; Julia K. Steinberger"
  "A good life for all within planetary boundaries"
  "Nature Sustainability 1:88-95"
  2018
  "10.1038/s41893-018-0021-4"
  "peer-reviewed cross-national empirical study"
  "owns the seven-biophysical / eleven-social indicator analysis, equal-per-capita downscaling convention, OLS model comparison, and observed safe-and-just claims; does not prove a universal resource-to-wellbeing production law"

fanning2022 : SourceReference
fanning2022 = sourceReference
  "Andrew L. Fanning; Daniel W. O'Neill; Jason Hickel; Nicolas Roux"
  "The social shortfall and ecological overshoot of nations"
  "Nature Sustainability"
  2022
  "10.1038/s41893-021-00799-z"
  "peer-reviewed longitudinal/cross-national empirical study"
  "extends the safe-and-just indicator programme through social-shortfall and ecological-overshoot analysis; kept separate from the 2018 model and from later review synthesis"

kallis2025 : SourceReference
kallis2025 = sourceReference
  "Giorgos Kallis; Jason Hickel; Daniel W. O'Neill; Tim Jackson; Peter A. Victor; Kate Raworth; Juliet B. Schor; Julia K. Steinberger; Diana Urge-Vorsatz"
  "Post-growth: the science of wellbeing within planetary boundaries"
  "The Lancet Planetary Health"
  2025
  "10.1016/S2542-5196(24)00310-3"
  "peer-reviewed review/synthesis"
  "synthesizes post-growth evidence and policy research; does not retroactively turn the 2018/2022 associations into causal laws or make one political ideology definitionally equivalent to post-growth"

record SourceRoleBoundary : Set where
  constructor sourceRoleBoundary
  field
    crossNationalAssociationIsCausalLaw : Bool
    crossNationalAssociationIsCausalLawIsFalse :
      crossNationalAssociationIsCausalLaw ≡ false
    allocationConventionIsEarthSystemMeasurement : Bool
    allocationConventionIsEarthSystemMeasurementIsFalse :
      allocationConventionIsEarthSystemMeasurement ≡ false
    postGrowthReviewIsAnarchismByDefinition : Bool
    postGrowthReviewIsAnarchismByDefinitionIsFalse :
      postGrowthReviewIsAnarchismByDefinition ≡ false
    postGrowthReviewIsCommunismByDefinition : Bool
    postGrowthReviewIsCommunismByDefinitionIsFalse :
      postGrowthReviewIsCommunismByDefinition ≡ false

canonicalSourceRoleBoundary : SourceRoleBoundary
canonicalSourceRoleBoundary =
  sourceRoleBoundary false refl false refl false refl false refl
