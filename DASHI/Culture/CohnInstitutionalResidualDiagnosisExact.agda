module DASHI.Culture.CohnInstitutionalResidualDiagnosisExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.DiscriminatorSynthesisExact as Synthesis
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.FeministRechartingSourceBridgeExact as Feminist
import DASHI.Core.RepresentationSubjectPositionNonfactorabilityExact as Subject
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as TwoEyed
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as IK
import DASHI.Culture.CohnInstitutionalFeministTwoEyedCrossPollinationExact as Cross
import DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionExact as Acquisition1
import DASHI.Culture.CohnInstitutionalIbrahimDeweyAcquisitionExtensionTwoExact as Acquisition2

------------------------------------------------------------------------
-- CONSUMER-RELATIVE RESIDUAL DIAGNOSIS
--
-- Synthetic DASHI fixture over the already source-bounded candidate families.
-- External sources motivate candidate coordinate families only.  The world,
-- collision, residual functions, costs and discriminator minimality below are
-- repository-local constructions and are not attributed to any source author.
------------------------------------------------------------------------

data InstitutionalWorld : Set where
  representedAcceptedWorld : InstitutionalWorld
  originatingRefusedWorld : InstitutionalWorld

data CoarseInstitutionalDecision : Set where
  sameAcceptedDecision : CoarseInstitutionalDecision

coarseDecision : InstitutionalWorld → CoarseInstitutionalDecision
coarseDecision _ = sameAcceptedDecision

institutionalCollision : Synthesis.CurrentObserverCollision coarseDecision
institutionalCollision = Synthesis.currentObserverCollision
  representedAcceptedWorld
  originatingRefusedWorld
  refl

------------------------------------------------------------------------
-- Candidate residuals instantiated from the existing cross-pollination grammar.
------------------------------------------------------------------------

subjectPositionResidual : InstitutionalWorld → Subject.SubjectPosition
subjectPositionResidual representedAcceptedWorld = Subject.representedPosition
subjectPositionResidual originatingRefusedWorld = Subject.originatingPosition

provenanceResidual : InstitutionalWorld → TwoEyed.Provenance
provenanceResidual representedAcceptedWorld = TwoEyed.indigenousProvenance
provenanceResidual originatingRefusedWorld = TwoEyed.indigenousProvenance

permissionResidual : InstitutionalWorld → IK.PermissionStatus
permissionResidual representedAcceptedWorld = IK.restrictedPermission
permissionResidual originatingRefusedWorld = IK.restrictedPermission

ignoranceProductionResidual : InstitutionalWorld → Bool
ignoranceProductionResidual representedAcceptedWorld = false
ignoranceProductionResidual originatingRefusedWorld = false

hermeneuticalRefusalResidual : InstitutionalWorld → Bool
hermeneuticalRefusalResidual representedAcceptedWorld = false
hermeneuticalRefusalResidual originatingRefusedWorld = true

criticalUptakeResidual : InstitutionalWorld → Bool
criticalUptakeResidual representedAcceptedWorld = true
criticalUptakeResidual originatingRefusedWorld = true

------------------------------------------------------------------------
-- Candidate experiment bundles.  Costs are synthetic retained-coordinate
-- burdens for this finite fixture only; they are not empirical costs, truth
-- scores, source quality, moral ranking, legal merit or theory ranking.
------------------------------------------------------------------------

subjectPositionBundle : Synthesis.ExperimentBundle InstitutionalWorld
subjectPositionBundle = Synthesis.experimentBundle
  Subject.SubjectPosition
  subjectPositionResidual
  2
  "subject-position / originating-authority residual"
  "DASHI synthetic fixture; source-bounded feminist grammar only motivates the coordinate family"

provenanceBundle : Synthesis.ExperimentBundle InstitutionalWorld
provenanceBundle = Synthesis.experimentBundle
  TwoEyed.Provenance
  provenanceResidual
  1
  "knowledge-history / provenance residual"
  "DASHI synthetic fixture; Two-Eyed Seeing supplies a non-fusion analogue, not this world fact"

permissionBundle : Synthesis.ExperimentBundle InstitutionalWorld
permissionBundle = Synthesis.experimentBundle
  IK.PermissionStatus
  permissionResidual
  1
  "permission / standing residual"
  "DASHI synthetic fixture; Indigenous knowledge owner supplies the generic non-collapse boundary"

ignoranceProductionBundle : Synthesis.ExperimentBundle InstitutionalWorld
ignoranceProductionBundle = Synthesis.experimentBundle
  Bool
  ignoranceProductionResidual
  1
  "constructed-ignorance candidate residual"
  "Tuana is source context for the candidate family; fixture values are DASHI synthesis"

hermeneuticalRefusalBundle : Synthesis.ExperimentBundle InstitutionalWorld
hermeneuticalRefusalBundle = Synthesis.experimentBundle
  Bool
  hermeneuticalRefusalResidual
  1
  "hermeneutical-refusal candidate residual"
  "Pohlhaus is source context for the candidate family; fixture values are DASHI synthesis"

criticalUptakeBundle : Synthesis.ExperimentBundle InstitutionalWorld
criticalUptakeBundle = Synthesis.experimentBundle
  Bool
  criticalUptakeResidual
  1
  "critical-uptake candidate residual"
  "Anderson is source context for the candidate family; fixture values are DASHI synthesis"

------------------------------------------------------------------------
-- Which candidates actually distinguish this collision?
------------------------------------------------------------------------

subjectPositionBundleSeparates :
  Synthesis.BundleSeparates
    subjectPositionBundle representedAcceptedWorld originatingRefusedWorld
subjectPositionBundleSeparates = Synthesis.bundleSeparates (λ ())

hermeneuticalRefusalBundleSeparates :
  Synthesis.BundleSeparates
    hermeneuticalRefusalBundle representedAcceptedWorld originatingRefusedWorld
hermeneuticalRefusalBundleSeparates = Synthesis.bundleSeparates (λ ())

subjectPositionSeparates : Bool
subjectPositionSeparates = true

provenanceSeparates : Bool
provenanceSeparates = false

permissionSeparates : Bool
permissionSeparates = false

ignoranceProductionSeparates : Bool
ignoranceProductionSeparates = false

hermeneuticalRefusalSeparates : Bool
hermeneuticalRefusalSeparates = true

criticalUptakeSeparates : Bool
criticalUptakeSeparates = false

------------------------------------------------------------------------
-- Declared finite candidate family and least separator.
------------------------------------------------------------------------

data DeclaredResidualBundle :
  Synthesis.ExperimentBundle InstitutionalWorld → Set where
  subjectPositionDeclared : DeclaredResidualBundle subjectPositionBundle
  provenanceDeclared : DeclaredResidualBundle provenanceBundle
  permissionDeclared : DeclaredResidualBundle permissionBundle
  ignoranceProductionDeclared : DeclaredResidualBundle ignoranceProductionBundle
  hermeneuticalRefusalDeclared : DeclaredResidualBundle hermeneuticalRefusalBundle
  criticalUptakeDeclared : DeclaredResidualBundle criticalUptakeBundle

minimalRefusalCost :
  (alternative : Synthesis.ExperimentBundle InstitutionalWorld) →
  DeclaredResidualBundle alternative →
  Synthesis.BundleSeparates alternative representedAcceptedWorld originatingRefusedWorld →
  Synthesis.cost hermeneuticalRefusalBundle ≤ Synthesis.cost alternative
minimalRefusalCost .subjectPositionBundle subjectPositionDeclared separates =
  s≤s z≤n
minimalRefusalCost .provenanceBundle provenanceDeclared separates =
  ≤-refl
minimalRefusalCost .permissionBundle permissionDeclared separates =
  ≤-refl
minimalRefusalCost .ignoranceProductionBundle ignoranceProductionDeclared separates =
  ≤-refl
minimalRefusalCost .hermeneuticalRefusalBundle hermeneuticalRefusalDeclared separates =
  ≤-refl
minimalRefusalCost .criticalUptakeBundle criticalUptakeDeclared separates =
  ≤-refl

minimalResidualDiagnosis :
  Synthesis.MinimalDiscriminator coarseDecision DeclaredResidualBundle
minimalResidualDiagnosis = Synthesis.minimalDiscriminator
  institutionalCollision
  hermeneuticalRefusalBundle
  hermeneuticalRefusalDeclared
  hermeneuticalRefusalBundleSeparates
  minimalRefusalCost
  "within the declared candidate family and synthetic retained-coordinate cost, hermeneutical-refusal is a least-cost separator of this coarse institutional collision; this does not rank theories or establish a real-world refusal"

selectedResidualIsHermeneuticalRefusal : Bool
selectedResidualIsHermeneuticalRefusal = true

------------------------------------------------------------------------
-- Existing theory reuse and attribution firewall.
------------------------------------------------------------------------

intersectionalRepairGrammar :
  INF.NonFactorabilityWitness INF.flatProjection INF.relationalOutcome
intersectionalRepairGrammar = INF.canonicalIntersectionalNonFactorability

positiveResidualGrammar : Feminist.PositiveRecharting Feminist.inheritedChart
positiveResidualGrammar = Feminist.canonicalPositiveRecharting

crossPollinationBoundary : Cross.CrossPollinationBoundary
crossPollinationBoundary = Cross.canonicalCrossPollinationBoundary

acquisitionOneBoundary : Acquisition1.AcquisitionAttributionBoundary
acquisitionOneBoundary = Acquisition1.canonicalAcquisitionAttributionBoundary

acquisitionTwoBoundary : Acquisition2.AcquisitionTwoAttributionBoundary
acquisitionTwoBoundary = Acquisition2.canonicalAcquisitionTwoAttributionBoundary

genericRepairGrammarReused : Bool
genericRepairGrammarReused = true

sourceLabelAutomaticallySelectsRepair : Bool
sourceLabelAutomaticallySelectsRepair = false

syntheticFixtureProvesRealInstitutionalBadFaith : Bool
syntheticFixtureProvesRealInstitutionalBadFaith = false

record ResidualDiagnosisBoundary : Set where
  constructor residualDiagnosisBoundary
  field
    sameCoarseDecisionMayHideMultipleCandidateResiduals : Bool
    oneCandidateFamilyAlwaysSeparatesEveryCollision : Bool
    sourceConceptIdentityEqualsDashiResidualFunction : Bool
    minimalSyntheticCostMeansBestTheory : Bool
    nonSeparatingCandidateIsThereforeFalseTheory : Bool
    selectedSeparatorCreatesHistoricalInfluenceClaim : Bool
    candidateTestingCanNarrowRepairDebt : Bool

open ResidualDiagnosisBoundary public

canonicalResidualDiagnosisBoundary : ResidualDiagnosisBoundary
canonicalResidualDiagnosisBoundary = residualDiagnosisBoundary
  true false false false false false true
