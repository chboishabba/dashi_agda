module DASHI.Physics.YangMills.BalabanClayNumericalIngredientDependencyAuditExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Numerical-ingredient dependency graph.
--
-- A displayed constant is not automatically a free parameter, and a theorem
-- is not automatically an empirical prediction.  Every ingredient is labelled
-- by epistemic role and linked to the Agda declaration that owns it.
------------------------------------------------------------------------

data NumericalIngredientKind : Set where
  axiom theorem definition empiricalCalibration dimensionalAnchor
  discreteModellingChoice normalisationConvention numericalSolution
  withheldPrediction : NumericalIngredientKind

data DependencyUse : Set where
  proves defines calibrates fixesUnits selectsConvention computes predicts
  audits : DependencyUse

record NumericalIngredient : Set where
  constructor ingredient
  field
    identifier : String
    displayedValueOrFormula : String
    kind : NumericalIngredientKind
    ownerModule : String
    ownerDeclaration : String
    sourceAuthors : String
    sourceTitle : String
    sourceIdentifier : String
    targetDataUsedInConstruction : Bool
    admissibleInPureYangMillsProof : Bool
    auditNote : String

open NumericalIngredient public

record IngredientDependency : Set where
  constructor edge
  field
    dependencySource : String
    dependencyTarget : String
    dependencyUse : DependencyUse
    justificationOwnerModule : String
    justificationDeclaration : String
    independentlyChecked : Bool

open IngredientDependency public

record NumericalDependencyGraph : Set₁ where
  field
    ingredients : List NumericalIngredient
    dependencies : List IngredientDependency
    everyIngredientHasOwner : Set
    everyEdgeHasJustification : Set
    calibrationsNotMisreportedAsPredictions : Set
    dimensionalOutputsHaveAnchors : Set
    discreteChoicesAreVisible : Set
    withheldPredictionsUseNoWithheldTargetData : Set

open NumericalDependencyGraph public

-- Existing DASHI constants are referenced at their current declaration owners;
-- this graph does not duplicate their values or promote conditional receipts.
fpCliqueValue : NumericalIngredient
fpCliqueValue = ingredient
  "T5.phiFP"
  "1 + 8 * (1/4) = 3"
  theorem
  "DASHI.Physics.YangMills.BalabanClayT2LiteralEightWayCliqueExact"
  "phiFP"
  "Roberto Fernández and Aldo Procacci"
  "Cluster Expansion for Abstract Polymer Models. New Bounds from an Old Approach"
  "DOI 10.1007/s00220-007-0279-2; arXiv:math-ph/0605041"
  false true
  "finite clique evaluation; not an empirical calibration"

fpMaximumActivity : NumericalIngredient
fpMaximumActivity = ingredient
  "T5.rhoFPMax"
  "(1/4) / 3 = 1/12"
  theorem
  "DASHI.Physics.YangMills.BalabanClayT2LiteralEightWayCliqueExact"
  "rhoFPMax"
  "Roberto Fernández and Aldo Procacci"
  "Cluster Expansion for Abstract Polymer Models. New Bounds from an Old Approach"
  "DOI 10.1007/s00220-007-0279-2"
  false true
  "derived comparison threshold"

oneLoopNormalization : NumericalIngredient
oneLoopNormalization = ingredient
  "T4.oneLoopNormalization"
  "(11/3) * (1/8) = 11/24"
  normalisationConvention
  "DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopConventionExact"
  "universalOneLoopNormalization"
  "Tadeusz Bałaban"
  "Renormalization Group Approach to Lattice Gauge Field Theories. I"
  "DOI 10.1007/BF01215223"
  false true
  "convention is frozen separately from the physical coefficient proof"

selectedTaylorGrid : NumericalIngredient
selectedTaylorGrid = ingredient
  "T4.generated240BoxGrid"
  "240 certified boxes"
  numericalSolution
  "DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact"
  "generatedBrillouinGrid"
  "DASHI generated certificate"
  "Deterministic Brillouin-zone interval subdivision"
  "repository-generated receipt"
  false true
  "finite computation whose theorem relevance is supplied by a separate enclosure proof"

record ExistingDASHINumericalAudit : Set₁ where
  field
    existingGraph : NumericalDependencyGraph
    fpThresholdDerivedFromClique : Set
    oneLoopConventionSeparatedFromCoefficientTheorem : Set
    generatedGridSeparatedFromAnalyticEnclosure : Set
    noConditionalPhysicalInputReclassifiedAsTheorem : Set

open ExistingDASHINumericalAudit public

------------------------------------------------------------------------
-- External-model suitability audit.  This can describe UIDT or any later
-- proposed model without importing it into the pure Yang--Mills proof graph.
------------------------------------------------------------------------

record ExternalModelNumericalAudit : Set₁ where
  field
    modelName : String
    externalGraph : NumericalDependencyGraph
    theoryMatchesPureYangMillsFieldContent : Bool
    pureSectorTransferTheoremOwner : String
    continuousParameterCountAudited : Set
    discreteChoiceCountAudited : Set
    dimensionalAnchorCountAudited : Set
    functionalFormSelectionAudited : Set
    fitTestSeparationAudited : Set
    schemeAndScaleTransportAudited : Set
    admissibleAsPureYangMillsAuthority : Bool

open ExternalModelNumericalAudit public

numericalIngredientVocabularyLevel : ProofLevel
numericalIngredientVocabularyLevel = machineChecked

existingNumericalReferenceSurfaceLevel : ProofLevel
existingNumericalReferenceSurfaceLevel = machineChecked

numericalDependencyGraphAuditInputsLevel : ProofLevel
numericalDependencyGraphAuditInputsLevel = conditional
