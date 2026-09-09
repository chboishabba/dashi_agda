module DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGModelProvenanceBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Interop.SourceAttributionShapePolicyExact as Shape
import DASHI.Physics.ExoticGravity.LiTorr1991CombinedFieldSourceEntitlementExact as LT1991
import DASHI.Physics.ExoticGravity.LiTorr1992CoupledPotentialSourceEntitlementExact as LT1992
import DASHI.Physics.ExoticGravity.SuperconductingConstitutiveNegativeGScopeWeldExact as EffectiveG

------------------------------------------------------------------------
-- MODEL ORIGIN IS A FIRST-CLASS COORDINATE
--
-- The historical Li/Torr papers source-entitle bounded coupled-field / response
-- claim shapes.  DASHI's material-effective negative-G interpretation is a
-- downstream reconstruction over a constitutive sign hypothesis.  Unless an
-- inspected source explicitly states that stronger interpretation, it remains
-- DASHI-derived rather than an imported Li/Torr theorem.
------------------------------------------------------------------------

data ModelOrigin : Set where
  importedLiTorrHistoricalClaim : ModelOrigin
  dashiDerivedEffectiveCouplingHypothesis : ModelOrigin
  modelOriginUnresolved : ModelOrigin

data ModelFamily : Set where
  combinedFieldAttenuationFamily : ModelFamily
  coupledPotentialResponseFamily : ModelFamily
  materialEffectiveNegativeGCouplingFamily : ModelFamily

record ModelProvenanceReceipt : Set₁ where
  constructor model-provenance-receipt
  field
    modelFamily : ModelFamily
    origin : ModelOrigin
    provenanceCarrier : String
    boundedModelScope : String
    EntitlementOrProofLineage : Set
    entitlementOrProofLineage : EntitlementOrProofLineage

open ModelProvenanceReceipt public

liTorr1991HistoricalModelProvenance : ModelProvenanceReceipt
liTorr1991HistoricalModelProvenance = model-provenance-receipt
  combinedFieldAttenuationFamily
  importedLiTorrHistoricalClaim
  "DOI 10.1103/PhysRevD.43.457 / APS primary abstract"
  "historical combined B + (m/q) B_g attenuation claim only"
  LT1991.CombinedFieldAttenuationSourceWeld
  LT1991.canonicalCombinedFieldAttenuationSourceWeld

liTorr1992HistoricalModelProvenance : ModelProvenanceReceipt
liTorr1992HistoricalModelProvenance = model-provenance-receipt
  coupledPotentialResponseFamily
  importedLiTorrHistoricalClaim
  "DOI 10.1103/PhysRevB.46.5489 / inspected secondary full-text copy"
  "historical Eqs. (33)-(35) combined-potential response shape only"
  LT1992.CoupledPotentialSourceWeld
  LT1992.canonicalCoupledPotentialSourceWeld

record DASHIMaterialEffectiveGModelReceipt : Set₁ where
  constructor dashi-material-effective-g-model-receipt
  field
    effectiveGWeld : EffectiveG.ConstitutiveNegativeGReceipt
    proofLineageCarrier : String
    derivationScope : String
    InternalDerivationReceipt : Set
    internalDerivationReceipt : InternalDerivationReceipt

open DASHIMaterialEffectiveGModelReceipt public

------------------------------------------------------------------------
-- Introspective collision: all three may be described loosely as
-- "superconducting gravity coupling" while their provenance and semantics differ.
------------------------------------------------------------------------

data CoarseModelLabel : Set where
  superconductingGravityCoupling : CoarseModelLabel

data ModelFixture : Set where
  historicalCoupledPotentialFixture : ModelFixture
  dashiEffectiveGFixture : ModelFixture

coarseObserve : ModelFixture → CoarseModelLabel
coarseObserve _ = superconductingGravityCoupling

originConsumer : ModelFixture → ModelOrigin
originConsumer historicalCoupledPotentialFixture = importedLiTorrHistoricalClaim
originConsumer dashiEffectiveGFixture = dashiDerivedEffectiveCouplingHypothesis

coarseCollision :
  coarseObserve historicalCoupledPotentialFixture
    ≡ coarseObserve dashiEffectiveGFixture
coarseCollision = refl

coarseLabelDoesNotDetermineModelOrigin :
  originConsumer historicalCoupledPotentialFixture
    ≡ originConsumer dashiEffectiveGFixture → ⊥
coarseLabelDoesNotDetermineModelOrigin ()

------------------------------------------------------------------------
-- Attribution shape follows origin.
------------------------------------------------------------------------

requiredAttributionShapeForOrigin : ModelOrigin → Shape.RequiredAttributionShape
requiredAttributionShapeForOrigin importedLiTorrHistoricalClaim =
  Shape.requiredAttributionShape Shape.publishedScientificTheorem
requiredAttributionShapeForOrigin dashiDerivedEffectiveCouplingHypothesis =
  Shape.requiredAttributionShape Shape.internalDerivedTheorem
requiredAttributionShapeForOrigin modelOriginUnresolved =
  Shape.requiredAttributionShape Shape.internalDerivedTheorem

record ModelProvenanceBoundary : Set where
  constructor model-provenance-boundary
  field
    exactLiTorrEquationAutomaticallyEntitlesDASHIEffectiveGModel : Bool
    liTorrHistoricalClaimEqualsDASHIEffectiveGInterpretation : Bool
    dashiEffectiveGModelNeedsFreshBibliographicPretence : Bool
    dashiEffectiveGModelNeedsInternalProofLineage : Bool
    importedHistoricalClaimNeedsExternalSourceEntitlement : Bool
    sourceEntitlementProvesPhysicalCorrectness : Bool
    internalDerivationProvesPhysicalCorrectness : Bool
    unresolvedOriginMayBeGuessed : Bool

canonicalModelProvenanceBoundary : ModelProvenanceBoundary
canonicalModelProvenanceBoundary =
  model-provenance-boundary
    false false false true true false false false
