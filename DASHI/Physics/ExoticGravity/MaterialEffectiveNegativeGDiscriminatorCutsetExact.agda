module DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGDiscriminatorCutsetExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Interop.SourceAttributionShapePolicyExact as Shape
import DASHI.Physics.ExoticGravity.SuperconductingSourceVsConstitutiveEnhancementBidiExact as Split
import DASHI.Physics.ExoticGravity.SuperconductingResidualCouplingNegativeGInterpretationBidiExact as Interpretation
import DASHI.Physics.ExoticGravity.SuperconductingConstitutiveNegativeGScopeWeldExact as Weld
import DASHI.Physics.ExoticGravity.AntigravityNegativeGCouplingScopeProofSearchExact as ScopeSearch
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- MATERIAL-EFFECTIVE NEGATIVE-G DISCRIMINATOR CUTSET
--
-- A single signed field sample cannot identify whether the negative coordinate
-- came from source, additive residual, or constitutive response.  The minimum
-- experimental geometry therefore keeps source and material-regime variations
-- as independent axes.
------------------------------------------------------------------------

data CandidateInterpretation : Set where
  sourceChangeInterpretation : CandidateInterpretation
  additiveResidualInterpretation : CandidateInterpretation
  constitutiveSignReversalInterpretation : CandidateInterpretation

data SinglePointSurface : Set where
  sameNegativeFieldSample : SinglePointSurface

data InterpretationFixture : Set where
  sourceFixture additiveFixture constitutiveFixture : InterpretationFixture

singlePointObserve : InterpretationFixture → SinglePointSurface
singlePointObserve _ = sameNegativeFieldSample

fixtureInterpretation : InterpretationFixture → CandidateInterpretation
fixtureInterpretation sourceFixture = sourceChangeInterpretation
fixtureInterpretation additiveFixture = additiveResidualInterpretation
fixtureInterpretation constitutiveFixture = constitutiveSignReversalInterpretation

sourceVsConstitutiveSinglePointCollision :
  singlePointObserve sourceFixture ≡ singlePointObserve constitutiveFixture
sourceVsConstitutiveSinglePointCollision = refl

additiveVsConstitutiveSinglePointCollision :
  singlePointObserve additiveFixture ≡ singlePointObserve constitutiveFixture
additiveVsConstitutiveSinglePointCollision = refl

singlePointCannotIdentifySourceVsConstitutive :
  fixtureInterpretation sourceFixture
    ≡ fixtureInterpretation constitutiveFixture → ⊥
singlePointCannotIdentifySourceVsConstitutive ()

singlePointCannotIdentifyAdditiveVsConstitutive :
  fixtureInterpretation additiveFixture
    ≡ fixtureInterpretation constitutiveFixture → ⊥
singlePointCannotIdentifyAdditiveVsConstitutive ()

------------------------------------------------------------------------
-- Minimum two-axis cutset.
------------------------------------------------------------------------

data DiscriminatorAxis : Set where
  sourceAmplitudeAxis : DiscriminatorAxis
  materialRegimeAxis : DiscriminatorAxis
  sourceSignIdentityAxis : DiscriminatorAxis
  geometryIdentityAxis : DiscriminatorAxis
  backgroundClosureAxis : DiscriminatorAxis
  fieldSignAxis : DiscriminatorAxis
  replicationAxis : DiscriminatorAxis

record MaterialEffectiveNegativeGCutset : Set where
  constructor material-effective-negative-g-cutset
  field
    fixedSourceComparisonRequired : Bool
    sourceAmplitudeSweepRequired : Bool
    materialRegimeSweepRequired : Bool
    sourceSignIdentityRequired : Bool
    sameGeometryRequired : Bool
    ordinaryBackgroundClosureRequired : Bool
    measuredFieldSignRequired : Bool
    coefficientSignMappingRequired : Bool
    independentReplicationRequired : Bool
    singleOperatingPointSufficient : Bool

open MaterialEffectiveNegativeGCutset public

canonicalMaterialEffectiveNegativeGCutset : MaterialEffectiveNegativeGCutset
canonicalMaterialEffectiveNegativeGCutset =
  material-effective-negative-g-cutset
    true true true true true true true true true false

producerForAxis : DiscriminatorAxis → Search.ProducerClass
producerForAxis sourceAmplitudeAxis = Search.discriminatorProducer
producerForAxis materialRegimeAxis = Search.discriminatorProducer
producerForAxis sourceSignIdentityAxis = Search.identityProducer
producerForAxis geometryIdentityAxis = Search.identityProducer
producerForAxis backgroundClosureAxis = Search.empiricalEvidenceProducer
producerForAxis fieldSignAxis = Search.empiricalEvidenceProducer
producerForAxis replicationAxis = Search.empiricalEvidenceProducer

------------------------------------------------------------------------
-- Strong handoff: all upstream interpretations remain exact, not inferred from
-- the words "negative field" or "effective G".
------------------------------------------------------------------------

record MaterialEffectiveNegativeGDiscriminationReceipt : Set₁ where
  constructor material-effective-negative-g-discrimination-receipt
  field
    sourceConstitutiveFactorization : Split.SourceConstitutiveFactorization
    residualInterpretation : Interpretation.ResidualInterpretationReceipt
    constitutiveNegativeGWeld : Weld.ConstitutiveNegativeGReceipt
    scopeSearchTarget : ScopeSearch.MaterialEffectiveGExperimentTarget

    SourceAmplitudeSweepReceipt : Set
    sourceAmplitudeSweepReceipt : SourceAmplitudeSweepReceipt

    MaterialRegimeSweepReceipt : Set
    materialRegimeSweepReceipt : MaterialRegimeSweepReceipt

    SameMeasuredSourceIdentityReceipt : Set
    sameMeasuredSourceIdentityReceipt : SameMeasuredSourceIdentityReceipt

    SameGeometryReceipt : Set
    sameGeometryReceipt : SameGeometryReceipt

    BackgroundClosureReceipt : Set
    backgroundClosureReceipt : BackgroundClosureReceipt

    FieldSignReceipt : Set
    fieldSignReceipt : FieldSignReceipt

    IndependentReplicationReceipt : Set
    independentReplicationReceipt : IndependentReplicationReceipt

open MaterialEffectiveNegativeGDiscriminationReceipt public

------------------------------------------------------------------------
-- Attribution: this cutset is internal DASHI proof-search logic.
------------------------------------------------------------------------

attributionShape : Shape.RequiredAttributionShape
attributionShape = Shape.requiredAttributionShape Shape.internalDerivedTheorem

record MaterialEffectiveNegativeGDiscriminatorBoundary : Set where
  constructor material-effective-negative-g-discriminator-boundary
  field
    singleNegativeFieldSampleIdentifiesConstitutiveNegativeG : Bool
    sourceAndMaterialAxesMustBeVariedIndependently : Bool
    sourceIdentityCanBeInferredFromFieldSign : Bool
    additiveResidualAutomaticallyEqualsConstitutiveChange : Bool
    coefficientSignRequiresExplicitMapping : Bool
    independentReplicationRequiredBeforeInterpretation : Bool
    cutsetItselfProvesPhysicalNegativeG : Bool
    internalCutsetNeedsFreshExternalCitation : Bool

canonicalMaterialEffectiveNegativeGDiscriminatorBoundary :
  MaterialEffectiveNegativeGDiscriminatorBoundary
canonicalMaterialEffectiveNegativeGDiscriminatorBoundary =
  material-effective-negative-g-discriminator-boundary
    false true false false true true false false
