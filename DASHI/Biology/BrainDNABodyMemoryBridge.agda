module DASHI.Biology.BrainDNABodyMemoryBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Biology.BodyKeepsScoreResidualBridge as BodyScore
import Ontology.Brain.BrainRegionAutomatonSurface as Region
open import Ontology.Brain.BrainVocabularySurface using (BrainState)
import Ontology.BrainDNA.BrainDnaRepresentationMap as Map

------------------------------------------------------------------------
-- Candidate-only BrainDNA/body-memory bridge.
--
-- BrainDNA representation semantics provide a typed encoding/semantics
-- surface. Body-memory residuals provide a candidate fibre/residual surface.
-- This bridge only aligns those surfaces as bounded interpretive grammar.
--
-- It explicitly does not promote:
-- - genetic determinism
-- - trauma proof from BrainDNA representation
-- - diagnosis or treatment authority
-- - factorization/recovery of hidden body charts
-- - clinical authority

data Never : Set where

data BrainDNABodyMemoryRoute : Set where
  candidateRepresentationBridgeRoute : BrainDNABodyMemoryRoute
  geneticDeterminismRoute : BrainDNABodyMemoryRoute
  traumaProofRoute : BrainDNABodyMemoryRoute
  diagnosisRoute : BrainDNABodyMemoryRoute
  treatmentRoute : BrainDNABodyMemoryRoute
  hiddenChartFactorizationRoute : BrainDNABodyMemoryRoute
  clinicalAuthorityRoute : BrainDNABodyMemoryRoute

AdmissibleBrainDNABodyMemoryRoute :
  BrainDNABodyMemoryRoute →
  Set
AdmissibleBrainDNABodyMemoryRoute candidateRepresentationBridgeRoute = ⊤
AdmissibleBrainDNABodyMemoryRoute geneticDeterminismRoute = Never
AdmissibleBrainDNABodyMemoryRoute traumaProofRoute = Never
AdmissibleBrainDNABodyMemoryRoute diagnosisRoute = Never
AdmissibleBrainDNABodyMemoryRoute treatmentRoute = Never
AdmissibleBrainDNABodyMemoryRoute hiddenChartFactorizationRoute = Never
AdmissibleBrainDNABodyMemoryRoute clinicalAuthorityRoute = Never

geneticDeterminismRejected :
  AdmissibleBrainDNABodyMemoryRoute geneticDeterminismRoute →
  Never
geneticDeterminismRejected impossible = impossible

traumaProofRejected :
  AdmissibleBrainDNABodyMemoryRoute traumaProofRoute →
  Never
traumaProofRejected impossible = impossible

diagnosisRejected :
  AdmissibleBrainDNABodyMemoryRoute diagnosisRoute →
  Never
diagnosisRejected impossible = impossible

treatmentRejected :
  AdmissibleBrainDNABodyMemoryRoute treatmentRoute →
  Never
treatmentRejected impossible = impossible

hiddenChartFactorizationRejected :
  AdmissibleBrainDNABodyMemoryRoute hiddenChartFactorizationRoute →
  Never
hiddenChartFactorizationRejected impossible = impossible

clinicalAuthorityRejected :
  AdmissibleBrainDNABodyMemoryRoute clinicalAuthorityRoute →
  Never
clinicalAuthorityRejected impossible = impossible

data BrainDNARepresentationBodyMemoryRole : Set where
  representationSemanticsRole : BrainDNARepresentationBodyMemoryRole
  encodedAdmissibilityRole : BrainDNARepresentationBodyMemoryRole
  emittedAdmissibilityRole : BrainDNARepresentationBodyMemoryRole
  bodyFibreCarrierRole : BrainDNARepresentationBodyMemoryRole
  residualMismatchRole : BrainDNARepresentationBodyMemoryRole
  governanceBoundaryRole : BrainDNARepresentationBodyMemoryRole

data BrainDNABodyMemoryBoundary : Set where
  representationNotGenomeDestinyBoundary : BrainDNABodyMemoryBoundary
  representationNotTraumaProofBoundary : BrainDNABodyMemoryBoundary
  representationNotDiagnosisBoundary : BrainDNABodyMemoryBoundary
  representationNotTreatmentBoundary : BrainDNABodyMemoryBoundary
  representationNotHiddenChartFactorizationBoundary : BrainDNABodyMemoryBoundary
  representationNotClinicalAuthorityBoundary : BrainDNABodyMemoryBoundary

canonicalBrainDNABodyMemoryRoles :
  List BrainDNARepresentationBodyMemoryRole
canonicalBrainDNABodyMemoryRoles =
  representationSemanticsRole
  ∷ encodedAdmissibilityRole
  ∷ emittedAdmissibilityRole
  ∷ bodyFibreCarrierRole
  ∷ residualMismatchRole
  ∷ governanceBoundaryRole
  ∷ []

canonicalBrainDNABodyMemoryBoundaries :
  List BrainDNABodyMemoryBoundary
canonicalBrainDNABodyMemoryBoundaries =
  representationNotGenomeDestinyBoundary
  ∷ representationNotTraumaProofBoundary
  ∷ representationNotDiagnosisBoundary
  ∷ representationNotTreatmentBoundary
  ∷ representationNotHiddenChartFactorizationBoundary
  ∷ representationNotClinicalAuthorityBoundary
  ∷ []

record BrainDNABodyMemoryBridge (n : Nat) : Set₁ where
  constructor brainDNABodyMemoryBridge
  field
    brainState :
      BrainState n

    brainRegion :
      Region.BrainRegion

    representationSemantics :
      Map.BrainDnaRepresentationSemantics n

    bodyScoreResidual :
      BodyScore.BodyKeepsScoreResidualBridge

    route :
      BrainDNABodyMemoryRoute

    routeIsCandidateOnly :
      route ≡ candidateRepresentationBridgeRoute

    routeAdmissible :
      AdmissibleBrainDNABodyMemoryRoute route

    roles :
      List BrainDNARepresentationBodyMemoryRole

    rolesAreCanonical :
      roles ≡ canonicalBrainDNABodyMemoryRoles

    boundaries :
      List BrainDNABodyMemoryBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalBrainDNABodyMemoryBoundaries

    encodedAdmissibility :
      Bool

    encodedAdmissibilityIsSemantic :
      encodedAdmissibility
      ≡
      Map.BrainDnaRepresentationSemantics.encodedAdmissibility
        representationSemantics

    emittedAdmissibility :
      Bool

    emittedAdmissibilityIsSemantic :
      emittedAdmissibility
      ≡
      Map.BrainDnaRepresentationSemantics.emittedAdmissibility
        representationSemantics

    geneticDeterminismBlocked :
      Bool

    geneticDeterminismBlockedIsFalse :
      geneticDeterminismBlocked ≡ false

    traumaProofBlocked :
      Bool

    traumaProofBlockedIsFalse :
      traumaProofBlocked ≡ false

    diagnosisBlocked :
      Bool

    diagnosisBlockedIsFalse :
      diagnosisBlocked ≡ false

    treatmentBlocked :
      Bool

    treatmentBlockedIsFalse :
      treatmentBlocked ≡ false

    hiddenChartFactorizationBlocked :
      Bool

    hiddenChartFactorizationBlockedIsFalse :
      hiddenChartFactorizationBlocked ≡ false

    clinicalAuthorityBlocked :
      Bool

    clinicalAuthorityBlockedIsFalse :
      clinicalAuthorityBlocked ≡ false

    bridgeReading :
      String

open BrainDNABodyMemoryBridge public

brainDNABodyMemoryBridgeOf :
  ∀ {n} →
  (st : BrainState n) →
  (r : Region.BrainRegion) →
  BrainDNABodyMemoryBridge n
brainDNABodyMemoryBridgeOf st r =
  brainDNABodyMemoryBridge
    st
    r
    (Map.representationSemanticsOf st r)
    BodyScore.canonicalBodyKeepsScoreResidualBridge
    candidateRepresentationBridgeRoute
    refl
    tt
    canonicalBrainDNABodyMemoryRoles
    refl
    canonicalBrainDNABodyMemoryBoundaries
    refl
    (Map.BrainDnaRepresentationSemantics.encodedAdmissibility
      (Map.representationSemanticsOf st r))
    refl
    (Map.BrainDnaRepresentationSemantics.emittedAdmissibility
      (Map.representationSemanticsOf st r))
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    "BrainDNA representation semantics may index body-memory residual vocabulary, but they do not prove trauma, determine destiny, diagnose, treat, factor hidden charts, or promote clinical authority."

brainDNABodyMemoryRouteCandidate :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainDNABodyMemoryBridge.route (brainDNABodyMemoryBridgeOf st r)
    ≡
  candidateRepresentationBridgeRoute
brainDNABodyMemoryRouteCandidate st r = refl

brainDNABodyMemoryEncodedAdmissibilityExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainDNABodyMemoryBridge.encodedAdmissibility
    (brainDNABodyMemoryBridgeOf st r)
    ≡
  Map.BrainDnaRepresentationSemantics.encodedAdmissibility
    (Map.representationSemanticsOf st r)
brainDNABodyMemoryEncodedAdmissibilityExact st r = refl

brainDNABodyMemoryEmittedAdmissibilityExact :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainDNABodyMemoryBridge.emittedAdmissibility
    (brainDNABodyMemoryBridgeOf st r)
    ≡
  Map.BrainDnaRepresentationSemantics.emittedAdmissibility
    (Map.representationSemanticsOf st r)
brainDNABodyMemoryEmittedAdmissibilityExact st r = refl

brainDNABodyMemoryNoDiagnosis :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainDNABodyMemoryBridge.diagnosisBlocked
    (brainDNABodyMemoryBridgeOf st r)
    ≡
  false
brainDNABodyMemoryNoDiagnosis st r = refl

brainDNABodyMemoryNoClinicalAuthority :
  ∀ {n} (st : BrainState n) (r : Region.BrainRegion) →
  BrainDNABodyMemoryBridge.clinicalAuthorityBlocked
    (brainDNABodyMemoryBridgeOf st r)
    ≡
  false
brainDNABodyMemoryNoClinicalAuthority st r = refl

record BrainDNABodyMemoryBridgeSurface : Set₁ where
  field
    route :
      BrainDNABodyMemoryRoute

    routeAdmissible :
      AdmissibleBrainDNABodyMemoryRoute route

    bridge :
      ∀ {n} → BrainState n → Region.BrainRegion → BrainDNABodyMemoryBridge n

    surfaceReading :
      String

brainDNABodyMemoryBridgeSurface :
  BrainDNABodyMemoryBridgeSurface
brainDNABodyMemoryBridgeSurface = record
  { route = candidateRepresentationBridgeRoute
  ; routeAdmissible = tt
  ; bridge = brainDNABodyMemoryBridgeOf
  ; surfaceReading =
      "Candidate-only BrainDNA/body-memory surface: representation semantics can align with residual vocabulary, but cannot promote destiny, trauma proof, diagnosis, treatment, hidden-chart factorization, or clinical authority."
  }
