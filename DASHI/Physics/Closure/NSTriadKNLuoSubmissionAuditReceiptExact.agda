module DASHI.Physics.Closure.NSTriadKNLuoSubmissionAuditReceiptExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Charles L. Fefferman.
-- Title: "Existence and Smoothness of the Navier--Stokes Equation".
-- Clay Mathematics Institute Millennium Prize Problem description, 2000.
-- DOI: not assigned to the official problem description.
--
-- PURPOSE
-- Provide machine-readable structures for the assumption, circularity,
-- source-fidelity, manuscript-crosswalk and reproducibility audits required
-- before a formal global-regularity theorem can be called submission-ready.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)

record SourceFidelityEntry : Set where
  field
    authorOrAuthors : String
    title : String
    venueAndYear : String
    doiOrStableIdentifier : String
    theoremOrLemmaNumber : String
    exactHypotheses : String
    domainConvention : String
    fourierConvention : String
    viscosityConvention : String
    endpointConvention : String
    proofStatus : String

open SourceFidelityEntry public

record DependencyInventory : Set where
  field
    postulates : List String
    standardImportedTheorems : List String
    classicalPrinciples : List String
    choicePrinciples : List String
    excludedMiddleUses : List String
    quotientOrExtensionalityUses : List String
    realAnalysisAuthorities : List String
    finiteSupportAssumptions : List String
    boundednessFields : List String
    targetShapedFields : List String

open DependencyInventory public

record NoCircularityReceipt : Set₁ where
  field
    NoGlobalSmoothnessAssumed : Set
    noGlobalSmoothnessAssumed : NoGlobalSmoothnessAssumed

    NoFiniteBKMIntegralAssumed : Set
    noFiniteBKMIntegralAssumed : NoFiniteBKMIntegralAssumed

    NoContinuationBeyondMaximalTimeAssumed : Set
    noContinuationBeyondMaximalTimeAssumed :
      NoContinuationBeyondMaximalTimeAssumed

    NoUniformHighShellDecayAssumed : Set
    noUniformHighShellDecayAssumed :
      NoUniformHighShellDecayAssumed

    NoLocalizedCriterionAssumed : Set
    noLocalizedCriterionAssumed : NoLocalizedCriterionAssumed

    NoSection4ConclusionAssumed : Set
    noSection4ConclusionAssumed : NoSection4ConclusionAssumed

    NoFixedShiftDecayConclusionAssumed : Set
    noFixedShiftDecayConclusionAssumed :
      NoFixedShiftDecayConclusionAssumed

    NoGloballyDefinedOfficialSolutionAssumed : Set
    noGloballyDefinedOfficialSolutionAssumed :
      NoGloballyDefinedOfficialSolutionAssumed

open NoCircularityReceipt public

record ManuscriptFormalCrosswalkEntry : Set where
  field
    manuscriptLemma : String
    formalModule : String
    formalDeclaration : String
    dependencyBoundary : String
    proofStatus : String

open ManuscriptFormalCrosswalkEntry public

record ReproducibilityReceipt : Set₁ where
  field
    agdaVersion : String
    standardLibraryRevision : String
    repositoryRevision : String
    buildCommand : String
    artifactHashInventory : List String

    CleanBuildFromEmptyEnvironment : Set
    cleanBuildFromEmptyEnvironment :
      CleanBuildFromEmptyEnvironment

    NoHolesUnresolvedMetasOrUnsafeFlags : Set
    noHolesUnresolvedMetasOrUnsafeFlags :
      NoHolesUnresolvedMetasOrUnsafeFlags

    FullDependencyGraphGenerated : Set
    fullDependencyGraphGenerated : FullDependencyGraphGenerated

    FullTheoremInventoryGenerated : Set
    fullTheoremInventoryGenerated : FullTheoremInventoryGenerated

    SourceProvenanceInventoryGenerated : Set
    sourceProvenanceInventoryGenerated :
      SourceProvenanceInventoryGenerated

    FiniteInfiniteBoundaryReportGenerated : Set
    finiteInfiniteBoundaryReportGenerated :
      FiniteInfiniteBoundaryReportGenerated

    RationalRealBoundaryReportGenerated : Set
    rationalRealBoundaryReportGenerated :
      RationalRealBoundaryReportGenerated

open ReproducibilityReceipt public

record CompleteSubmissionAuditReceipt : Set₁ where
  field
    dependencyInventory : DependencyInventory
    noCircularity : NoCircularityReceipt
    sourceFidelity : List SourceFidelityEntry
    manuscriptCrosswalk : List ManuscriptFormalCrosswalkEntry
    reproducibility : ReproducibilityReceipt

open CompleteSubmissionAuditReceipt public

completeSubmissionAuditReceipt :
  DependencyInventory →
  NoCircularityReceipt →
  List SourceFidelityEntry →
  List ManuscriptFormalCrosswalkEntry →
  ReproducibilityReceipt →
  CompleteSubmissionAuditReceipt
completeSubmissionAuditReceipt inventory circularity sources crosswalk reproducibility =
  record
    { dependencyInventory = inventory
    ; noCircularity = circularity
    ; sourceFidelity = sources
    ; manuscriptCrosswalk = crosswalk
    ; reproducibility = reproducibility
    }

sourceFidelitySchemaConstructed : Bool
sourceFidelitySchemaConstructed = true

noCircularitySchemaConstructed : Bool
noCircularitySchemaConstructed = true

submissionAuditSchemaConstructed : Bool
submissionAuditSchemaConstructed = true

sourceFidelitySchemaConstructedIsTrue :
  sourceFidelitySchemaConstructed ≡ true
sourceFidelitySchemaConstructedIsTrue = refl

noCircularitySchemaConstructedIsTrue :
  noCircularitySchemaConstructed ≡ true
noCircularitySchemaConstructedIsTrue = refl

submissionAuditSchemaConstructedIsTrue :
  submissionAuditSchemaConstructed ≡ true
submissionAuditSchemaConstructedIsTrue = refl
