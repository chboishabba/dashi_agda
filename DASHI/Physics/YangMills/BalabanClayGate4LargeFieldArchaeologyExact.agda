module DASHI.Physics.YangMills.BalabanClayGate4LargeFieldArchaeologyExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCriticalMapRGCutsetCompletion as ExistingRG
import DASHI.Physics.YangMills.BalabanClayLargeFieldVerifiedLiteratureExact as Literature

------------------------------------------------------------------------
-- Gate 4 archaeology: Bałaban's large-field R-operation lane.
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
-- Fields", Journal of Mathematical Physics 54 (2013), 092301,
-- DOI: 10.1063/1.4821275, arXiv:1212.5562, is used only as scalar-model
-- exposition and not as gauge-theory theorem authority.
--
-- Exact equation/page transcriptions below remain pending direct primary-source
-- verification.  The Eriksson viXra documents are locators only.
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
  "Bałaban RG I; small-field effective action"
  "DASHI.Physics.YangMills.BalabanCriticalMapRGCutsetCompletion"
  "OneStepRGCutset.fluctuationCoordinatesExist"
  existingConditional
  "BalabanCombinedSmallLargeFieldRGStep"
  "existing small-field owner; no duplicate authority"

smallFieldIrrelevantContraction : Gate4Mechanism
smallFieldIrrelevantContraction = mechanism
  "localized irrelevant Taylor contraction"
  "Bałaban RG I/II"
  "DASHI.Physics.YangMills.BalabanCriticalMapRGCutsetCompletion"
  "OneStepRGCutset.irrelevantTaylorRemainderContractive"
  existingConditional
  "BalabanCombinedSmallLargeFieldRGStep"
  "must be paired with the large-field contribution"

largeFieldRegionCarrier : Gate4Mechanism
largeFieldRegionCarrier = mechanism
  "literal large-field block, connected component, enlargement and collar"
  "Large Field I/II; determining sets and enlarged large-field regions"
  "DASHI.Physics.YangMills.BalabanClayGate4LiteralWilsonLargeFieldPredicateExact"
  "literalWilsonBadBlockGeometry"
  newCombinatorial
  "BalabanClayGate4ComponentClassAndFiniteTOperationExact"
  "literal Wilson predicate and generic component algebra are proof-bearing; the physical adjacency/holonomy instance remains separate"

componentClassSplit : Gate4Mechanism
componentClassSplit = mechanism
  "first/small-field versus second/T-operation component class"
  "Large Field II, component-class convention near the large-field decomposition"
  "DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact"
  "SecondClassComponent"
  newCombinatorial
  "localizedTOperation"
  "this classifies connected components; it is distinct from localized-expression intersection classification"

localizedExpressionClassSplit : Gate4Mechanism
localizedExpressionClassSplit = mechanism
  "localized-expression regular/boundary split by large-field intersection"
  "Large Field II, localization and boundary extraction"
  "DASHI.Physics.YangMills.BalabanClayGate4TypedReuseAndFiniteGeometryExact"
  "classifyLocalizedTermExact"
  newCombinatorial
  "runROperation"
  "do not conflate this term classification with the component class controlling T"

determiningSetUpdate : Gate4Mechanism
determiningSetUpdate = mechanism
  "determining-set update and background redefinition"
  "Large Field II, new determining sets and boundary terms"
  "DASHI.Physics.YangMills.BalabanCriticalMapRGCutsetCompletion"
  "CriticalMapCutset.backgroundField"
  newAnalytic
  "BalabanClayGate4FiniteROperationAndDecayAssemblyExact"
  "reuse the existing background carrier but prove the large-field update and support law"

localTOperation : Gate4Mechanism
localTOperation = mechanism
  "localized T operation on certified second-class components"
  "Large Field II, equation (1.89), p. 387, pending primary-source check"
  "DASHI.Physics.YangMills.BalabanClayP3FiniteConstrainedIntegralExact"
  "constrainedIntegral"
  newAnalytic
  "ExactBalabanTOperationSmallFactor"
  "the finite T definition, positivity and monotonicity are internal; locality, covariance and the small-factor estimate remain analytic"

rOperation : Gate4Mechanism
rOperation = mechanism
  "finite R-operation expression pipeline"
  "Large Field I basic step; Large Field II localization/exponentiation"
  "DASHI.Physics.YangMills.BalabanClayGate4FiniteROperationAndDecayAssemblyExact"
  "runROperation"
  newCombinatorial
  "ROperationStructuralLaws"
  "the algebraic partition/localize/extract/exponentiate pipeline is concrete; physical expression operations remain inputs"

rLocalization : Gate4Mechanism
rLocalization = mechanism
  "localization of R terms"
  "Large Field II localization"
  "DASHI.Physics.YangMills.BalabanCriticalMapRGCutsetCompletion"
  "OneStepRGCutset.localizationPreservesSupport"
  newAnalytic
  "ROperationDecayDerivation"
  "reuse support and exponential-weight preservation through a representation adapter"

rExponentiation : Gate4Mechanism
rExponentiation = mechanism
  "exponentiation of localized R terms"
  "Large Field II exponentiation"
  "DASHI.Physics.YangMills.BalabanCriticalMapRGCutsetCompletion"
  "OneStepRGCutset.jacobianPolymerLocalization"
  newAnalytic
  "ROperationDecayDerivation.localizedExponentiationBound"
  "must produce activities compatible with the existing polymer norm"

rDecay : Gate4Mechanism
rDecay = mechanism
  "boundary-uniform R-polymer decay"
  "Large Field II, equation (1.100), p. 388, pending primary-source check"
  "DASHI.Physics.YangMills.BalabanClayGate4FiniteROperationAndDecayAssemblyExact"
  "rOperationDecayUniformInBoundary"
  newAnalytic
  "BalabanCombinedSmallLargeFieldRGStep"
  "transitive assembly is exact; component counting, localization and exponentiation inequalities remain inhabitants"

boundaryTermReinjection : Gate4Mechanism
boundaryTermReinjection = mechanism
  "boundary-term generation, support ownership and reinjection"
  "Large Field II, equation (1.69), p. 377, pending primary-source check"
  "DASHI.Physics.YangMills.BalabanClayGate4FiniteROperationAndDecayAssemblyExact"
  "nextBoundaryDensity"
  newAnalytic
  "BalabanCombinedSmallLargeFieldRGStep"
  "list reinjection is exact; analytic support and next-determining-set preservation remain inputs"

largeFieldAbsorption : Gate4Mechanism
largeFieldAbsorption = mechanism
  "large-field suppression absorbed into the small-field scale budget"
  "Large Field II p0-growth and inductive estimates, exact locations pending primary-source check"
  "DASHI.Physics.YangMills.BalabanClayGate4P0GrowthAbsorptionExact"
  "largeFieldAbsorbedBySmallFieldBudget"
  newAnalytic
  "BalabanCombinedSmallLargeFieldRGStep"
  "final transitive proof is exact once residual-envelope and polynomial-times-suppression estimates are supplied"

admissibleCouplingDomain : Gate4Mechanism
admissibleCouplingDomain = mechanism
  "scale-uniform admissible effective-coupling domain"
  "Large Field II Theorem 1, p. 388, pending primary-source check"
  "DASHI.Physics.YangMills.BalabanClayT4RunningCouplingConventionBridgeExact"
  "ConventionMatchedRunningCoupling"
  newAnalytic
  "Gate4UVCompletionPackage"
  "must preserve the existing fixed beta-function convention"

ultravioletIteration : Gate4Mechanism
ultravioletIteration = mechanism
  "combined one-step closure and all-scale ultraviolet induction"
  "Large Field II Theorem 1, p. 388, pending primary-source check"
  "DASHI.Physics.YangMills.BalabanClayGate4CombinedRGUVIterationExact"
  "allScaleAdmissible"
  newCombinatorial
  "partitionFunctionUniformBound"
  "the induction is exact; one-step analytic preservation and initial stability remain conditional"

gate4Mechanisms : List Gate4Mechanism
gate4Mechanisms =
  smallFieldCoordinates ∷ smallFieldIrrelevantContraction ∷
  largeFieldRegionCarrier ∷ componentClassSplit ∷
  localizedExpressionClassSplit ∷ determiningSetUpdate ∷ localTOperation ∷
  rOperation ∷ rLocalization ∷ rExponentiation ∷ rDecay ∷
  boundaryTermReinjection ∷ largeFieldAbsorption ∷
  admissibleCouplingDomain ∷ ultravioletIteration ∷ []

------------------------------------------------------------------------
-- Stable completion-package surfaces retained for downstream consumers.
------------------------------------------------------------------------

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
