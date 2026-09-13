module DASHI.Core.PluralOperationalRealisationDiscrepancyExact where

------------------------------------------------------------------------
-- PLURAL OPERATIONAL REALISATION DISCREPANCY
--
-- Generic operational compiler for the proposition:
--
--   what a system declares/reports != what its repeated operation realises
--   != what an affected community identifies as the relevant outcome.
--
-- Source-specific POSIWID, Two-Eyed Seeing, Indigenous knowledge, feminist,
-- legal and remedy interpretations remain upstream.  The finite theorem shapes
-- below are DASHI constructions and do not prove private intent or legitimacy.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.PluralEpistemicOperationalClosureExact as Operational
import DASHI.Core.DominantChartEpistemicCompressionExact as Compression
import DASHI.Core.ObserverRefinementLatticeExact as Observer

------------------------------------------------------------------------
-- Three non-interchangeable operational surfaces.
------------------------------------------------------------------------

data OperationalSurfaceKind : Set where
  declaredPurposeSurface
  institutionalSelfReportSurface
  realisedMaterialEffectSurface
  affectedCommunityOutcomeSurface
  correctionResponseSurface
  : OperationalSurfaceKind

record RealisationDiscrepancyReceipt : Set₁ where
  constructor realisation-discrepancy-receipt
  field
    declarationReference : String
    institutionalReportReference : String
    realisedEffectReference : String
    communityOutcomeReference : String
    correctionReference : String
    declarationMatchesInstitutionalReport : Bool
    realisedEffectMatchesDeclaredPurpose : Bool
    communityOutcomeMatchesInstitutionalReport : Bool
    correctionChangesRealisedOperation : Bool
    privateIntentProved : Bool
    privateIntentProvedIsFalse : privateIntentProved ≡ false
    legitimacyProved : Bool
    legitimacyProvedIsFalse : legitimacyProved ≡ false

open RealisationDiscrepancyReceipt public

------------------------------------------------------------------------
-- A system-realisation discrepancy is paid only by realised/community outcome
-- evidence.  More declaration/reporting cannot pay the missing coordinate.
------------------------------------------------------------------------

data DiscrepancyClass : Set where
  declarationRealisationAligned
  reportRealisationMismatch
  reportCommunityMismatch
  correctionNonResponsive
  sourceUnresolvedDiscrepancy
  : DiscrepancyClass

classifyDiscrepancy : RealisationDiscrepancyReceipt → DiscrepancyClass
classifyDiscrepancy receipt with realisedEffectMatchesDeclaredPurpose receipt
... | false = reportRealisationMismatch
... | true with communityOutcomeMatchesInstitutionalReport receipt
...   | false = reportCommunityMismatch
...   | true with correctionChangesRealisedOperation receipt
...     | false = correctionNonResponsive
...     | true = declarationRealisationAligned

------------------------------------------------------------------------
-- Finite witness: same declaration + same self-report, different material and
-- community outcomes.  This blocks State/institutional self-report as a
-- sufficient observer for the richer operational consumer.
------------------------------------------------------------------------

data DemoState : Set where
  sameReportResidualPersists
  sameReportRelationTransforms
  : DemoState

data DemoDeclaration : Set where sameDeclaredReform : DemoDeclaration
data DemoInstitutionalReport : Set where sameReportedSuccess : DemoInstitutionalReport
data DemoMaterialEffect : Set where effectResidual effectTransformed : DemoMaterialEffect
data DemoCommunityOutcome : Set where communityResidual communityTransformed : DemoCommunityOutcome

demoDeclaration : DemoState → DemoDeclaration
demoDeclaration _ = sameDeclaredReform

demoInstitutionalReport : DemoState → DemoInstitutionalReport
demoInstitutionalReport _ = sameReportedSuccess

demoMaterialEffect : DemoState → DemoMaterialEffect
demoMaterialEffect sameReportResidualPersists = effectResidual
demoMaterialEffect sameReportRelationTransforms = effectTransformed

demoCommunityOutcome : DemoState → DemoCommunityOutcome
demoCommunityOutcome sameReportResidualPersists = communityResidual
demoCommunityOutcome sameReportRelationTransforms = communityTransformed

institutionalReportsCollide :
  demoInstitutionalReport sameReportResidualPersists
  ≡ demoInstitutionalReport sameReportRelationTransforms
institutionalReportsCollide = refl

materialEffectsDiffer :
  demoMaterialEffect sameReportResidualPersists
  ≡ demoMaterialEffect sameReportRelationTransforms → ⊥
materialEffectsDiffer ()

communityOutcomesDiffer :
  demoCommunityOutcome sameReportResidualPersists
  ≡ demoCommunityOutcome sameReportRelationTransforms → ⊥
communityOutcomesDiffer ()

institutionalReportCannotRecoverMaterialEffect :
  INF.FactorsThrough demoInstitutionalReport demoMaterialEffect → ⊥
institutionalReportCannotRecoverMaterialEffect =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      sameReportResidualPersists
      sameReportRelationTransforms
      institutionalReportsCollide
      materialEffectsDiffer)

institutionalReportCannotRecoverCommunityOutcome :
  INF.FactorsThrough demoInstitutionalReport demoCommunityOutcome → ⊥
institutionalReportCannotRecoverCommunityOutcome =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      sameReportResidualPersists
      sameReportRelationTransforms
      institutionalReportsCollide
      communityOutcomesDiffer)

institutionalReportCompression :
  Compression.ProjectionInadequacyReceipt demoInstitutionalReport demoCommunityOutcome
institutionalReportCompression = Compression.projection-inadequacy-receipt
  Compression.juridicalRecognitionCompression
  "institutional self-report / progress surface"
  "affected-community-defined operational outcome consumer"
  "same self-report can coexist with residual or transformed community outcome"
  (INF.nonFactorabilityWitness
    sameReportResidualPersists
    sameReportRelationTransforms
    institutionalReportsCollide
    communityOutcomesDiffer)
  true refl
  false refl
  false refl
  false refl

posthocRewordingCannotRecoverCommunityOutcome :
  ∀ {Recharted : Set} →
  (rechart : DemoInstitutionalReport → Recharted) →
  INF.FactorsThrough
    (λ state → rechart (demoInstitutionalReport state))
    demoCommunityOutcome → ⊥
posthocRewordingCannotRecoverCommunityOutcome =
  Compression.projectionCannotBeRepairedByPostcomposition institutionalReportCompression

------------------------------------------------------------------------
-- Positive repair: add a genuinely new realised/community coordinate.
------------------------------------------------------------------------

communityOutcomeRepair :
  Compression.ResidualRepair demoInstitutionalReport
communityOutcomeRepair = Compression.residual-repair
  demoCommunityOutcome
  sameReportResidualPersists
  sameReportRelationTransforms
  refl
  communityOutcomesDiffer

communityOutcomeRepairStrictlyRefinesInstitutionalReport :
  Observer.StrictRefinement
    demoInstitutionalReport
    (Observer.pairObserver demoInstitutionalReport demoCommunityOutcome)
communityOutcomeRepairStrictlyRefinesInstitutionalReport =
  Compression.residualRepairStrictlyRefines communityOutcomeRepair

------------------------------------------------------------------------
-- Operational closure relation.
------------------------------------------------------------------------

record OperationalDiscrepancyBoundary : Set where
  constructor operational-discrepancy-boundary
  field
    institutionalSelfReportMayBeUseful : Bool
    institutionalSelfReportMayBeUsefulIsTrue :
      institutionalSelfReportMayBeUseful ≡ true
    institutionalSelfReportExhaustsRealisedEffect : Bool
    institutionalSelfReportExhaustsRealisedEffectIsFalse :
      institutionalSelfReportExhaustsRealisedEffect ≡ false
    institutionalSelfReportExhaustsCommunityOutcome : Bool
    institutionalSelfReportExhaustsCommunityOutcomeIsFalse :
      institutionalSelfReportExhaustsCommunityOutcome ≡ false
    repeatedOperationMayReopenDeclaredSuccess : Bool
    repeatedOperationMayReopenDeclaredSuccessIsTrue :
      repeatedOperationMayReopenDeclaredSuccess ≡ true
    correctionResponseCountsAsSystemOperation : Bool
    correctionResponseCountsAsSystemOperationIsTrue :
      correctionResponseCountsAsSystemOperation ≡ true
    affectedCommunityOutcomeCanBeIndependentClosureCoordinate : Bool
    affectedCommunityOutcomeCanBeIndependentClosureCoordinateIsTrue :
      affectedCommunityOutcomeCanBeIndependentClosureCoordinate ≡ true
    stateReportGetsMetaObserverPriorityByDefault : Bool
    stateReportGetsMetaObserverPriorityByDefaultIsFalse :
      stateReportGetsMetaObserverPriorityByDefault ≡ false

open OperationalDiscrepancyBoundary public

canonicalOperationalDiscrepancyBoundary : OperationalDiscrepancyBoundary
canonicalOperationalDiscrepancyBoundary = operational-discrepancy-boundary
  true refl
  false refl
  false refl
  true refl
  true refl
  true refl
  false refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data DeclaredPurposeEqualsRealisedEffect : Set where
data InstitutionalSelfReportEqualsCommunityOutcome : Set where
data MoreReportingClosesMaterialResidual : Set where
data DiscrepancyProvesPrivateBadFaith : Set where
data CommunityOutcomeErasesAllInstitutionalEvidence : Set where

declaredPurposeDoesNotEqualRealisedEffect : DeclaredPurposeEqualsRealisedEffect → ⊥
declaredPurposeDoesNotEqualRealisedEffect ()

selfReportDoesNotEqualCommunityOutcome : InstitutionalSelfReportEqualsCommunityOutcome → ⊥
selfReportDoesNotEqualCommunityOutcome ()

moreReportingDoesNotCloseMaterialResidual : MoreReportingClosesMaterialResidual → ⊥
moreReportingDoesNotCloseMaterialResidual ()

discrepancyDoesNotProvePrivateBadFaith : DiscrepancyProvesPrivateBadFaith → ⊥
discrepancyDoesNotProvePrivateBadFaith ()

communityOutcomeDoesNotEraseAllInstitutionalEvidence :
  CommunityOutcomeErasesAllInstitutionalEvidence → ⊥
communityOutcomeDoesNotEraseAllInstitutionalEvidence ()
