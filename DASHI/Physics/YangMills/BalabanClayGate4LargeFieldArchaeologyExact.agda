module DASHI.Physics.YangMills.BalabanClayGate4LargeFieldArchaeologyExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCriticalMapRGCutsetCompletion as ExistingRG
import DASHI.Physics.YangMills.BalabanClayLargeFieldVerifiedLiteratureExact as Literature

------------------------------------------------------------------------
-- Gate 4 archaeology: Balaban's large-field R-operation lane.
--
-- Primary sources:
-- Tadeusz Bałaban,
-- "Large Field Renormalization. I. The Basic Step of the R Operation",
-- Communications in Mathematical Physics 122 (1989), 175--202,
-- DOI: 10.1007/BF01257412.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392, DOI: 10.1007/BF01238433.
--
-- J. Dimock, "The Renormalization Group According to Balaban. II. Large
-- Fields", arXiv:1212.5562, is used only as scalar-model exposition.
------------------------------------------------------------------------

data ArchaeologyStatus : Set where
  existingExact existingConditional newCombinatorial newAnalytic
  externalExpositionOnly : ArchaeologyStatus

record Gate4Mechanism : Set where
  constructor mechanism
  field
    name : String
    balabanLocation : String
    existingDASHIModule : String
    existingDASHIDeclaration : String
    status : ArchaeologyStatus
    nextConsumer : String
    note : String

open Gate4Mechanism public

smallFieldCoordinates : Gate4Mechanism
smallFieldCoordinates = mechanism
  "small-field coordinate decomposition"
  "Balaban RG I; small-field effective action"
  "DASHI.Physics.YangMills.BalabanCriticalMapRGCutsetCompletion"
  "OneStepRGCutset.fluctuationCoordinatesExist"
  existingConditional
  "BalabanCombinedSmallLargeFieldRGStep"
  "existing small-field owner; no duplicate authority"

smallFieldIrrelevantContraction : Gate4Mechanism
smallFieldIrrelevantContraction = mechanism
  "localized irrelevant Taylor contraction"
  "Balaban RG I/II"
  "DASHI.Physics.YangMills.BalabanCriticalMapRGCutsetCompletion"
  "OneStepRGCutset.irrelevantTaylorRemainderContractive"
  existingConditional
  "BalabanCombinedSmallLargeFieldRGStep"
  "must be paired with the large-field contribution"

largeFieldRegionCarrier : Gate4Mechanism
largeFieldRegionCarrier = mechanism
  "large-field region and component carrier"
  "Large Field I, determining sets and large-field regions"
  ""
  ""
  newCombinatorial
  "BalabanROperationExact"
  "bad blocks, connected components, enlargements and collars"

determiningSetUpdate : Gate4Mechanism
determiningSetUpdate = mechanism
  "determining-set update and background redefinition"
  "Large Field II, new determining sets B'_k"
  "DASHI.Physics.YangMills.BalabanCriticalMapRGCutsetCompletion"
  "CriticalMapCutset.backgroundField"
  newAnalytic
  "BalabanLocalTOperationExact"
  "reuse the existing background carrier but prove the large-field update law"

firstSecondClassSplit : Gate4Mechanism
firstSecondClassSplit = mechanism
  "first-class and second-class localized-term split"
  "Large Field II, classification by intersection with the large-field region Z"
  ""
  ""
  newCombinatorial
  "BalabanLocalTOperationExact"
  "classification must preserve support and polymer ownership"

localTOperation : Gate4Mechanism
localTOperation = mechanism
  "localized T operation"
  "Large Field I equation (1.100) and Large Field II composition step"
  "DASHI.Physics.YangMills.BalabanCriticalMapRGCutsetCompletion"
  "OneStepRGCutset.polymerLocalizationStable"
  newAnalytic
  "BalabanROperationExact"
  "existing localization laws are inputs, not the T operation itself"

rOperation : Gate4Mechanism
rOperation = mechanism
  "large-field R operation"
  "Large Field I basic step; Large Field II completion"
  ""
  ""
  newAnalytic
  "BalabanRLocalizationExact"
  "must transform large-field-associated expressions without importing a completion claim"

rLocalization : Gate4Mechanism
rLocalization = mechanism
  "localization of R terms"
  "Large Field II localization"
  "DASHI.Physics.YangMills.BalabanCriticalMapRGCutsetCompletion"
  "OneStepRGCutset.localizationPreservesSupport"
  newAnalytic
  "BalabanRExponentiationExact"
  "reuse support and exponential-weight preservation"

rExponentiation : Gate4Mechanism
rExponentiation = mechanism
  "exponentiation of localized R terms"
  "Large Field II exponentiation"
  "DASHI.Physics.YangMills.BalabanCriticalMapRGCutsetCompletion"
  "OneStepRGCutset.jacobianPolymerLocalization"
  newAnalytic
  "BalabanLargeFieldPolymerBound"
  "must produce polymer activities compatible with the existing cluster lane"

boundaryTermReinjection : Gate4Mechanism
boundaryTermReinjection = mechanism
  "boundary-term generation and reinjection"
  "Large Field II, terms B^{l(k)}(X) returned to the next renormalization step"
  ""
  ""
  newAnalytic
  "BalabanCombinedSmallLargeFieldRGStep"
  "load-bearing mechanism distinct from localization and exponentiation"

admissibleCouplingDomain : Gate4Mechanism
admissibleCouplingDomain = mechanism
  "scale-uniform admissible effective-coupling domain"
  "Large Field II Theorem 1 hypothesis on the effective coupling sequence"
  "DASHI.Physics.YangMills.BalabanCriticalMapRGCutsetCompletion"
  "OneStepRGCutset.couplingRenormalization"
  newAnalytic
  "BalabanUltravioletStabilityIteration"
  "must show the coupling sequence remains in the invariant domain"

gate4Mechanisms : List Gate4Mechanism
gate4Mechanisms =
  smallFieldCoordinates ∷ smallFieldIrrelevantContraction ∷
  largeFieldRegionCarrier ∷ determiningSetUpdate ∷ firstSecondClassSplit ∷
  localTOperation ∷ rOperation ∷ rLocalization ∷ rExponentiation ∷
  boundaryTermReinjection ∷ admissibleCouplingDomain ∷ []

record BalabanLargeFieldRegionCarrier
    (Block Region : Set) : Set₁ where
  field
    LargeFieldBlock : Block → Set
    regionOf : Block → Region
    Connected Enlarged Collar : Region → Set
    decompositionExact : Set
    enlargementAndCollarFinite : Set

record BalabanROperationExact
    (Expression Region RExpression : Set) : Set₁ where
  field
    R : Region → Expression → RExpression
    localized : RExpression → Set
    exponentiable : RExpression → Set
    basicStepExact : Set
    gaugeCovariant : Set

record BalabanRBoundaryTermReinjection
    (RExpression BoundaryTerm EffectiveDensity : Set) : Set₁ where
  field
    classifyBoundary : RExpression → BoundaryTerm
    reinject : BoundaryTerm → EffectiveDensity → EffectiveDensity
    classificationExact : Set
    supportPreserved : Set
    nextScaleEffectiveActionExact : Set

record BalabanCombinedSmallLargeFieldRGStep
    (SmallFieldStep LargeFieldStep EffectiveDensity Coupling : Set) : Set₁ where
  field
    smallField : SmallFieldStep
    largeField : LargeFieldStep
    combine : SmallFieldStep → LargeFieldStep → EffectiveDensity
    AdmissibleCoupling : Coupling → Set
    oneStepStable : Set
    boundaryTermsReinjected : Set
    polymerNormClosed : Set

record BalabanUltravioletStabilityIteration
    (Scale EffectiveDensity Coupling : Set) : Set₁ where
  field
    densityAt : Scale → EffectiveDensity
    couplingAt : Scale → Coupling
    AdmissibleCoupling : Coupling → Set
    everyCouplingAdmissible : (scale : Scale) → AdmissibleCoupling (couplingAt scale)
    combinedStepCloses : Set
    partitionFunctionUniformlyBounded : Set
    matchesBalabanTheoremOneHypotheses : Set
    notYetContinuumOSOrMassGap : Set

largeFieldLiteratureMetadataLevel : ProofLevel
largeFieldLiteratureMetadataLevel = machineChecked

gate4ArchaeologyGraphLevel : ProofLevel
gate4ArchaeologyGraphLevel = machineChecked

largeFieldGeometryAndROperationInputsLevel : ProofLevel
largeFieldGeometryAndROperationInputsLevel = conditional

combinedUltravioletStabilityIterationInputsLevel : ProofLevel
combinedUltravioletStabilityIterationInputsLevel = conditional
