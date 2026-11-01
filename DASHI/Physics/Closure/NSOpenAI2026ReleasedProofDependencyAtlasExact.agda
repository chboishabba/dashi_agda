module DASHI.Physics.Closure.NSOpenAI2026ReleasedProofDependencyAtlasExact where

------------------------------------------------------------------------
-- OPENAI 2026 RELEASED NS PROOF / CAUSAL DEPENDENCY ATLAS
--
-- This file extends the EXISTING released-proof BIDI lane.  It does not create
-- another source/provenance ontology and does not import the external theorem
-- as a DASHI proof.
--
-- External Lean source inspected:
--   openai/NavierStokesAndEuler
--
-- Whole-space theorem spine:
--   NavierStokes/R3/Theorem.lean
--     -> R3/ActualCandidate.lean
--     -> R3/CandidateBreakdown.lean
--     -> R3/ViscosityScaling.lean
--     -> R3/IntegratedDissipation.lean
--
-- ActualCandidate in turn consumes the selected physical construction through
-- ActualCandidateAssembly and applies spatial/time localization plus a smooth
-- positive-time force.
--
-- Periodic theorem spine:
--   NavierStokes/PeriodicPaperTheorem.lean
--     -> R3/Theorem
--     -> R3/ParabolicScaling
--     -> PeriodizePDE
--     -> PeriodicViscosity
--     -> CandidateConsequences.
--
-- The atlas records dependency PURPOSE and current DASHI relationship.  A name
-- match or structural resemblance never creates a same-object weld.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSClayFourAlternativeReleasedProofBidiExact as Clay4
import DASHI.Physics.Closure.NSOpenAI2026ReleasedClayCDTorus369BidiExact as Release
import DASHI.Physics.Closure.NSOpenAI2026GluedStagePants369CrossPollinationExact as Stage
import DASHI.Physics.Closure.NSReleasedCDToR406AdversarialUpdateBidiExact as R406Bidi

------------------------------------------------------------------------
-- 1. External dependency coordinates.
------------------------------------------------------------------------

data ReleasedDependencyKind : Set where
  selectedCorrectionConstruction : ReleasedDependencyKind
  literalPhysicalCandidateAssembly : ReleasedDependencyKind
  compactSpatialLocalization : ReleasedDependencyKind
  positiveTimeForceLocalization : ReleasedDependencyKind
  candidateBreakdownExclusion : ReleasedDependencyKind
  viscosityScaling : ReleasedDependencyKind
  integratedDissipation : ReleasedDependencyKind
  parabolicCompression : ReleasedDependencyKind
  periodicization : ReleasedDependencyKind
  periodicCompetitorExclusion : ReleasedDependencyKind
  candidateConsequences : ReleasedDependencyKind

data DASHIRelationship : Set where
  sameObjectWeldClosed : DASHIRelationship
  structuralDonorOnly : DASHIRelationship
  representationAdapterOpen : DASHIRelationship
  differentEquationClass : DASHIRelationship
  noRecoveredMatch : DASHIRelationship

record ReleasedDependencyRow : Set where
  constructor released-dependency-row
  field
    externalOwner : String
    dependencyKind : ReleasedDependencyKind
    role : String
    dashiRelationship : DASHIRelationship
    dashiCoordinate : String
    boundary : String

open ReleasedDependencyRow public

releasedRows : List ReleasedDependencyRow
releasedRows =
  released-dependency-row
    "NavierStokes/ActualCandidateConstruction.lean"
    selectedCorrectionConstruction
    "iterates the initialized correction cycle while retaining carrier, phase, band and state identities"
    structuralDonorOnly
    "NSOpenAI2026GluedStagePants369CrossPollinationExact"
    "DASHI records the common preserve-components-before-composition discipline, but no exact external-stage -> DASHI field weld is closed"
  ∷ released-dependency-row
    "NavierStokes/ActualCandidateAssembly.lean"
    literalPhysicalCandidateAssembly
    "assembles the selected physical candidate from actual initial, mean, wave, exterior and glued-stage data"
    representationAdapterOpen
    "NSOpenAI2026ReleasedClayCDTorus369BidiExact.firstReleasedToDASHIResidualOAI2026"
    "the literal released fields have not yet been transported to DASHI Fourier coefficients"
  ∷ released-dependency-row
    "NavierStokes/R3/ActualCandidate.lean"
    compactSpatialLocalization
    "localizes the selected velocity/pressure and proves compact spatial support"
    structuralDonorOnly
    "periodized/kernel/localization owners in the historical DASHI NS programme"
    "shared localization grammar is not field identity"
  ∷ released-dependency-row
    "NavierStokes/R3/PositiveTimeForce.lean"
    positiveTimeForceLocalization
    "smoothly localizes the external PDE body force away from the initial time"
    differentEquationClass
    "NSReleasedCDToR406AdversarialUpdateBidiExact"
    "external body force is not the internal state-dependent R406 companion"
  ∷ released-dependency-row
    "NavierStokes/R3/CandidateBreakdown.lean"
    candidateBreakdownExclusion
    "converts the constructed singular candidate into nonexistence of a global smooth finite-energy competitor"
    noRecoveredMatch
    "released C/D source alignment only"
    "no same-object DASHI reconstruction of the released comparison theorem is currently recorded"
  ∷ released-dependency-row
    "NavierStokes/R3/ViscosityScaling.lean"
    viscosityScaling
    "rescales the viscosity-one candidate to every positive viscosity"
    structuralDonorOnly
    "generic scaling/parabolic machinery elsewhere in DASHI"
    "no released-candidate same-object transport has been recovered"
  ∷ released-dependency-row
    "NavierStokes/R3/IntegratedDissipation.lean"
    integratedDissipation
    "adds the finite-energy/dissipation conclusions for the same forced candidate"
    noRecoveredMatch
    "none assigned in the canonical released-proof lane"
    "not needed to establish source alignment of Clay C/D; useful for full reconstruction"
  ∷ released-dependency-row
    "NavierStokes/R3/ParabolicScaling.lean"
    parabolicCompression
    "compresses the whole-space candidate while preserving singular time for the periodic construction"
    structuralDonorOnly
    "existing DASHI scale/periodic representation infrastructure"
    "structural scaling analogy does not identify the external fields"
  ∷ released-dependency-row
    "NavierStokes/PeriodizePDE.lean"
    periodicization
    "periodizes the compact whole-space candidate and transports the PDE locally before singular time"
    representationAdapterOpen
    "R531 periodic Fourier/Base369 carrier plus released-field-to-Fourier residual"
    "the public periodic theorem is located, but released continuum fields -> DASHI Fourier coefficients is still open"
  ∷ released-dependency-row
    "NavierStokes/PeriodicViscosity.lean"
    periodicCompetitorExclusion
    "excludes a global smooth periodic competitor for the same force and initial datum"
    noRecoveredMatch
    "Clay D statement/source alignment"
    "statement alignment is closed; construction reconstruction is not"
  ∷ released-dependency-row
    "NavierStokes/CandidateConsequences.lean"
    candidateConsequences
    "derives force-derivative decay and paper-facing consequences from the constructed candidate"
    structuralDonorOnly
    "source/receipt and decay infrastructure"
    "downstream consequence structure is not the core blowup construction"
  ∷ []

------------------------------------------------------------------------
-- 2. Canonical existing BIDI state.
------------------------------------------------------------------------

releasedDependencyAtlasConstructed : Bool
releasedDependencyAtlasConstructed = true

releasedWholeSpaceCandidateDependencyRecorded : Bool
releasedWholeSpaceCandidateDependencyRecorded = true

releasedPeriodicCompilerDependencyRecorded : Bool
releasedPeriodicCompilerDependencyRecorded = true

releasedCAndDSourceAlignmentAlreadyClosed : Bool
releasedCAndDSourceAlignmentAlreadyClosed =
  R406Bidi.releasedSourceToClaySideClosed

releasedStageComponentDisciplineAlreadyRecorded : Bool
releasedStageComponentDisciplineAlreadyRecorded =
  Stage.commonExactSeamDisciplineIdentified

------------------------------------------------------------------------
-- 3. First residual remains representation, not vocabulary.
------------------------------------------------------------------------

firstRepresentationResidualStillReleasedFieldToDASHIFourier : Bool
firstRepresentationResidualStillReleasedFieldToDASHIFourier = true

firstRepresentationResidual : Release.ReleasedToDASHIResidualOAI2026
firstRepresentationResidual = Release.firstReleasedToDASHIResidualOAI2026

vocabularyMatchCreatesSameObjectWeld : Bool
vocabularyMatchCreatesSameObjectWeld = false

------------------------------------------------------------------------
-- 4. Firewalls for the two proof programmes.
------------------------------------------------------------------------

fullPublishedForcedBreakdownProofReconstructedInDASHI : Bool
fullPublishedForcedBreakdownProofReconstructedInDASHI = false

publishedProofPaysUnforcedR568 : Bool
publishedProofPaysUnforcedR568 = false

unforcedPeriodicBInternallyPaid : Bool
unforcedPeriodicBInternallyPaid = Clay4.roundBInternallyPaid4

unforcedPeriodicBStillOpenInDASHI : Bool
unforcedPeriodicBStillOpenInDASHI = true

releasedDependencyAtlasConstructedIsTrue :
  releasedDependencyAtlasConstructed ≡ true
releasedDependencyAtlasConstructedIsTrue = refl

firstRepresentationResidualStillReleasedFieldToDASHIFourierIsTrue :
  firstRepresentationResidualStillReleasedFieldToDASHIFourier ≡ true
firstRepresentationResidualStillReleasedFieldToDASHIFourierIsTrue = refl

vocabularyMatchCreatesSameObjectWeldIsFalse :
  vocabularyMatchCreatesSameObjectWeld ≡ false
vocabularyMatchCreatesSameObjectWeldIsFalse = refl

fullPublishedForcedBreakdownProofReconstructedInDASHIIsFalse :
  fullPublishedForcedBreakdownProofReconstructedInDASHI ≡ false
fullPublishedForcedBreakdownProofReconstructedInDASHIIsFalse = refl

publishedProofPaysUnforcedR568IsFalse : publishedProofPaysUnforcedR568 ≡ false
publishedProofPaysUnforcedR568IsFalse = refl

unforcedPeriodicBInternallyPaidIsFalse : unforcedPeriodicBInternallyPaid ≡ false
unforcedPeriodicBInternallyPaidIsFalse = Clay4.roundBInternallyPaid4IsFalse
