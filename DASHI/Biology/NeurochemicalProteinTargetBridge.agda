module DASHI.Biology.NeurochemicalProteinTargetBridge where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Biology.BioactiveMolecularRecognitionBridge as Bioactive
import DASHI.Biology.CellDifferentiationCommunicationBridge as Cell
import DASHI.Biology.ProteinHormoneChemistryCellBridge as ProteinCell
import DASHI.Biology.NeurochemicalTransmissionBridge as Neurochemical
import DASHI.Promotion.NeurochemicalAuthorityBoundary as Boundary

------------------------------------------------------------------------
-- Protein target bridge.
--
-- This bridge stays candidate-only.  It records protein target context
-- over receptor subtype, transporter, enzyme, ion-channel complex, and
-- binding-site candidates, plus conformation/action candidate and a
-- downstream-signaling residual.  Folding authority, receptor-action
-- identity, efficacy, pathway, therapeutic, clinical, and prescribing
-- authority are blocked.

data Never : Set where

data ProteinTargetContextKind : Set where
  receptorSubtypeTargetContext : ProteinTargetContextKind
  transporterTargetContext : ProteinTargetContextKind
  enzymeTargetContext : ProteinTargetContextKind
  ionChannelComplexTargetContext : ProteinTargetContextKind
  bindingSiteTargetContext : ProteinTargetContextKind

data ProteinTargetActionCandidate : Set where
  targetEngagementCandidate : ProteinTargetActionCandidate
  receptorSubtypeEngagementCandidate : ProteinTargetActionCandidate
  transporterEngagementCandidate : ProteinTargetActionCandidate
  enzymeEngagementCandidate : ProteinTargetActionCandidate
  ionChannelComplexEngagementCandidate : ProteinTargetActionCandidate
  bindingSiteEngagementCandidate : ProteinTargetActionCandidate
  conformationShiftCandidate : ProteinTargetActionCandidate
  downstreamSignalCandidate : ProteinTargetActionCandidate

data ProteinTargetResidualKind : Set where
  downstreamSignalingResidualKind : ProteinTargetResidualKind

data ProteinTargetGuard : Set where
  NoFoldingAuthorityClaim : ProteinTargetGuard
  NoReceptorActionIdentityAuthorityClaim : ProteinTargetGuard
  NoEfficacyAuthorityClaim : ProteinTargetGuard
  NoPathwayAuthorityClaim : ProteinTargetGuard
  NoTherapeuticAuthorityClaim : ProteinTargetGuard
  NoClinicalAuthorityClaim : ProteinTargetGuard
  NoPrescribingAuthorityClaim : ProteinTargetGuard

data ProteinTargetAuthorityClaim : Set where
  foldingAuthorityClaim : ProteinTargetAuthorityClaim
  receptorActionIdentityAuthorityClaim : ProteinTargetAuthorityClaim
  efficacyAuthorityClaim : ProteinTargetAuthorityClaim
  pathwayAuthorityClaim : ProteinTargetAuthorityClaim
  therapeuticAuthorityClaim : ProteinTargetAuthorityClaim
  clinicalAuthorityClaim : ProteinTargetAuthorityClaim
  prescribingAuthorityClaim : ProteinTargetAuthorityClaim

data ProteinTargetRoute : Set where
  boundedProteinTargetReceiptRoute : ProteinTargetRoute
  foldingAuthorityRoute : ProteinTargetRoute
  receptorActionIdentityRoute : ProteinTargetRoute
  efficacyRoute : ProteinTargetRoute
  pathwayRoute : ProteinTargetRoute
  therapeuticRoute : ProteinTargetRoute
  clinicalRoute : ProteinTargetRoute
  prescribingRoute : ProteinTargetRoute

AdmissibleProteinTargetRoute : ProteinTargetRoute -> Set
AdmissibleProteinTargetRoute boundedProteinTargetReceiptRoute = ⊤
AdmissibleProteinTargetRoute foldingAuthorityRoute = Never
AdmissibleProteinTargetRoute receptorActionIdentityRoute = Never
AdmissibleProteinTargetRoute efficacyRoute = Never
AdmissibleProteinTargetRoute pathwayRoute = Never
AdmissibleProteinTargetRoute therapeuticRoute = Never
AdmissibleProteinTargetRoute clinicalRoute = Never
AdmissibleProteinTargetRoute prescribingRoute = Never

foldingAuthorityRejected :
  AdmissibleProteinTargetRoute foldingAuthorityRoute -> Never
foldingAuthorityRejected impossible = impossible

receptorActionIdentityRejected :
  AdmissibleProteinTargetRoute receptorActionIdentityRoute -> Never
receptorActionIdentityRejected impossible = impossible

efficacyRejected :
  AdmissibleProteinTargetRoute efficacyRoute -> Never
efficacyRejected impossible = impossible

pathwayRejected :
  AdmissibleProteinTargetRoute pathwayRoute -> Never
pathwayRejected impossible = impossible

therapeuticRejected :
  AdmissibleProteinTargetRoute therapeuticRoute -> Never
therapeuticRejected impossible = impossible

clinicalRejected :
  AdmissibleProteinTargetRoute clinicalRoute -> Never
clinicalRejected impossible = impossible

prescribingRejected :
  AdmissibleProteinTargetRoute prescribingRoute -> Never
prescribingRejected impossible = impossible

canonicalProteinTargetContextKinds :
  List ProteinTargetContextKind
canonicalProteinTargetContextKinds =
  receptorSubtypeTargetContext
  ∷ transporterTargetContext
  ∷ enzymeTargetContext
  ∷ ionChannelComplexTargetContext
  ∷ bindingSiteTargetContext
  ∷ []

canonicalProteinTargetActionCandidates :
  List ProteinTargetActionCandidate
canonicalProteinTargetActionCandidates =
  targetEngagementCandidate
  ∷ receptorSubtypeEngagementCandidate
  ∷ transporterEngagementCandidate
  ∷ enzymeEngagementCandidate
  ∷ ionChannelComplexEngagementCandidate
  ∷ bindingSiteEngagementCandidate
  ∷ conformationShiftCandidate
  ∷ downstreamSignalCandidate
  ∷ []

canonicalProteinTargetResidualKinds :
  List ProteinTargetResidualKind
canonicalProteinTargetResidualKinds =
  downstreamSignalingResidualKind
  ∷ []

canonicalProteinTargetGuards :
  List ProteinTargetGuard
canonicalProteinTargetGuards =
  NoFoldingAuthorityClaim
  ∷ NoReceptorActionIdentityAuthorityClaim
  ∷ NoEfficacyAuthorityClaim
  ∷ NoPathwayAuthorityClaim
  ∷ NoTherapeuticAuthorityClaim
  ∷ NoClinicalAuthorityClaim
  ∷ NoPrescribingAuthorityClaim
  ∷ []

canonicalProteinTargetAuthorityClaims :
  List ProteinTargetAuthorityClaim
canonicalProteinTargetAuthorityClaims =
  foldingAuthorityClaim
  ∷ receptorActionIdentityAuthorityClaim
  ∷ efficacyAuthorityClaim
  ∷ pathwayAuthorityClaim
  ∷ therapeuticAuthorityClaim
  ∷ clinicalAuthorityClaim
  ∷ prescribingAuthorityClaim
  ∷ []

canonicalProteinTargetRoutes :
  List ProteinTargetRoute
canonicalProteinTargetRoutes =
  boundedProteinTargetReceiptRoute
  ∷ foldingAuthorityRoute
  ∷ receptorActionIdentityRoute
  ∷ efficacyRoute
  ∷ pathwayRoute
  ∷ therapeuticRoute
  ∷ clinicalRoute
  ∷ prescribingRoute
  ∷ []

record NeurochemicalProteinTargetSurface : Set₁ where
  field
    ProteinCandidate : Set
    TargetContext : Set
    ReceptorSubtypeCandidate : Set
    TransporterCandidate : Set
    EnzymeCandidate : Set
    IonChannelComplexCandidate : Set
    BindingSiteCandidate : Set
    ConformationCandidate : Set
    ActionCandidate : Set
    DownstreamSignalingResidual : Set
    ObservationTrace : Set
    Receipt : Set
    ProvenanceNode : Set
    ObserverProtocol : Set
    BoundedProteinTargetMeaning : Set

    observeProteinTarget :
      ProteinCandidate ->
      TargetContext ->
      ObservationTrace

    observedTargetKinds :
      ObservationTrace -> List ProteinTargetContextKind

    observedActions :
      ObservationTrace -> List ProteinTargetActionCandidate

    observedResidualKinds :
      ObservationTrace -> List ProteinTargetResidualKind

    proteinCandidateFromTrace :
      ObservationTrace -> ProteinCandidate

    targetContextFromTrace :
      ObservationTrace -> TargetContext

    receptorSubtypeCandidateFromTrace :
      ObservationTrace -> ReceptorSubtypeCandidate

    transporterCandidateFromTrace :
      ObservationTrace -> TransporterCandidate

    enzymeCandidateFromTrace :
      ObservationTrace -> EnzymeCandidate

    ionChannelComplexCandidateFromTrace :
      ObservationTrace -> IonChannelComplexCandidate

    bindingSiteCandidateFromTrace :
      ObservationTrace -> BindingSiteCandidate

    conformationCandidateFromTrace :
      ObservationTrace -> ConformationCandidate

    actionCandidateFromTrace :
      ObservationTrace -> ActionCandidate

    downstreamSignalingResidualFromTrace :
      ObservationTrace -> DownstreamSignalingResidual

    admissibilityReceipt :
      ObservationTrace -> Receipt

    provenanceTrail :
      Receipt -> List ProvenanceNode

    observerProtocol :
      Receipt -> ObserverProtocol

    promoteBoundedProteinTargetMeaning :
      ObservationTrace ->
      Receipt ->
      BoundedProteinTargetMeaning

    observationGate :
      ObservationTrace -> Receipt -> Set

    provenanceGate :
      Receipt -> Set

    nonPromotionGuards :
      List ProteinTargetGuard

    surfaceReading :
      String

open NeurochemicalProteinTargetSurface public

record NeurochemicalProteinTargetBridge : Setω where
  field
    bioactiveRecognitionBridge :
      Bioactive.BioactiveMolecularRecognitionBridge

    bioactiveRecognitionBridgeIsCanonical :
      bioactiveRecognitionBridge
      ≡
      Bioactive.canonicalBioactiveMolecularRecognitionBridge

    proteinHormoneChemistryCellBridge :
      ProteinCell.ProteinHormoneChemistryCellBridge

    cellDifferentiationCommunicationBridge :
      Cell.CellDifferentiationCommunicationBridge

    cellDifferentiationCommunicationBridgeIsCanonical :
      cellDifferentiationCommunicationBridge
      ≡
      Cell.canonicalCellDifferentiationCommunicationBridge

    neurochemicalTransmissionBridge :
      Neurochemical.NeurochemicalTransmissionBridge

    neurochemicalTransmissionBridgeIsCanonical :
      neurochemicalTransmissionBridge
      ≡
      Neurochemical.canonicalNeurochemicalTransmissionBridge

    authorityBoundary :
      Boundary.NeurochemicalAuthorityBoundary

    authorityBoundaryIsCanonical :
      authorityBoundary
      ≡
      Boundary.canonicalNeurochemicalAuthorityBoundary

    surface :
      NeurochemicalProteinTargetSurface

    proteinCandidate :
      ProteinCandidate surface

    targetContext :
      TargetContext surface

    receptorSubtypeCandidate :
      ReceptorSubtypeCandidate surface

    transporterCandidate :
      TransporterCandidate surface

    enzymeCandidate :
      EnzymeCandidate surface

    ionChannelComplexCandidate :
      IonChannelComplexCandidate surface

    bindingSiteCandidate :
      BindingSiteCandidate surface

    conformationCandidate :
      ConformationCandidate surface

    actionCandidate :
      ActionCandidate surface

    downstreamSignalingResidual :
      DownstreamSignalingResidual surface

    targetKinds :
      List ProteinTargetContextKind

    targetKindsAreCanonical :
      targetKinds ≡ canonicalProteinTargetContextKinds

    actionKinds :
      List ProteinTargetActionCandidate

    actionKindsAreCanonical :
      actionKinds ≡ canonicalProteinTargetActionCandidates

    residualKinds :
      List ProteinTargetResidualKind

    residualKindsAreCanonical :
      residualKinds ≡ canonicalProteinTargetResidualKinds

    guards :
      List ProteinTargetGuard

    guardsAreCanonical :
      guards ≡ canonicalProteinTargetGuards

    authorityClaims :
      List ProteinTargetAuthorityClaim

    authorityClaimsAreCanonical :
      authorityClaims ≡ canonicalProteinTargetAuthorityClaims

    foldingAuthorityClaimFlag :
      Bool

    foldingAuthorityClaimFlagIsFalse :
      foldingAuthorityClaimFlag ≡ false

    receptorActionIdentityAuthorityClaimFlag :
      Bool

    receptorActionIdentityAuthorityClaimFlagIsFalse :
      receptorActionIdentityAuthorityClaimFlag ≡ false

    efficacyAuthorityClaimFlag :
      Bool

    efficacyAuthorityClaimFlagIsFalse :
      efficacyAuthorityClaimFlag ≡ false

    pathwayAuthorityClaimFlag :
      Bool

    pathwayAuthorityClaimFlagIsFalse :
      pathwayAuthorityClaimFlag ≡ false

    therapeuticAuthorityClaimFlag :
      Bool

    therapeuticAuthorityClaimFlagIsFalse :
      therapeuticAuthorityClaimFlag ≡ false

    clinicalAuthorityClaimFlag :
      Bool

    clinicalAuthorityClaimFlagIsFalse :
      clinicalAuthorityClaimFlag ≡ false

    prescribingAuthorityClaimFlag :
      Bool

    prescribingAuthorityClaimFlagIsFalse :
      prescribingAuthorityClaimFlag ≡ false

    route :
      ProteinTargetRoute

    routeIsBounded :
      route ≡ boundedProteinTargetReceiptRoute

    routeAdmissible :
      AdmissibleProteinTargetRoute route

    bridgeReading :
      String

open NeurochemicalProteinTargetBridge public

canonicalNeurochemicalProteinTargetSurface :
  NeurochemicalProteinTargetSurface
canonicalNeurochemicalProteinTargetSurface =
  record
    { ProteinCandidate = ⊤
    ; TargetContext = ⊤
    ; ReceptorSubtypeCandidate = ⊤
    ; TransporterCandidate = ⊤
    ; EnzymeCandidate = ⊤
    ; IonChannelComplexCandidate = ⊤
    ; BindingSiteCandidate = ⊤
    ; ConformationCandidate = ⊤
    ; ActionCandidate = ⊤
    ; DownstreamSignalingResidual = ⊤
    ; ObservationTrace = ⊤
    ; Receipt = ⊤
    ; ProvenanceNode = ⊤
    ; ObserverProtocol = ⊤
    ; BoundedProteinTargetMeaning = ⊤
    ; observeProteinTarget = λ _ _ -> tt
    ; observedTargetKinds = λ _ -> canonicalProteinTargetContextKinds
    ; observedActions = λ _ -> canonicalProteinTargetActionCandidates
    ; observedResidualKinds = λ _ -> canonicalProteinTargetResidualKinds
    ; proteinCandidateFromTrace = λ _ -> tt
    ; targetContextFromTrace = λ _ -> tt
    ; receptorSubtypeCandidateFromTrace = λ _ -> tt
    ; transporterCandidateFromTrace = λ _ -> tt
    ; enzymeCandidateFromTrace = λ _ -> tt
    ; ionChannelComplexCandidateFromTrace = λ _ -> tt
    ; bindingSiteCandidateFromTrace = λ _ -> tt
    ; conformationCandidateFromTrace = λ _ -> tt
    ; actionCandidateFromTrace = λ _ -> tt
    ; downstreamSignalingResidualFromTrace = λ _ -> tt
    ; admissibilityReceipt = λ _ -> tt
    ; provenanceTrail = λ _ -> tt ∷ []
    ; observerProtocol = λ _ -> tt
    ; promoteBoundedProteinTargetMeaning = λ _ _ -> tt
    ; observationGate = λ _ _ -> ⊤
    ; provenanceGate = λ _ -> ⊤
    ; nonPromotionGuards = canonicalProteinTargetGuards
    ; surfaceReading =
        "Protein target candidates are recorded only as bounded receptor subtype, transporter, enzyme, ion-channel complex, and binding-site context, with conformation/action candidates and downstream-signaling residuals; folding, receptor-action identity, efficacy, pathway, therapeutic, clinical, and prescribing authority remain blocked."
    }

canonicalNeurochemicalProteinTargetBridge :
  NeurochemicalProteinTargetBridge
canonicalNeurochemicalProteinTargetBridge =
  record
    { bioactiveRecognitionBridge =
        Bioactive.canonicalBioactiveMolecularRecognitionBridge
    ; bioactiveRecognitionBridgeIsCanonical =
        refl
    ; proteinHormoneChemistryCellBridge =
        ProteinCell.canonicalProteinHormoneChemistryCellBridge
    ; cellDifferentiationCommunicationBridge =
        Cell.canonicalCellDifferentiationCommunicationBridge
    ; cellDifferentiationCommunicationBridgeIsCanonical =
        refl
    ; neurochemicalTransmissionBridge =
        Neurochemical.canonicalNeurochemicalTransmissionBridge
    ; neurochemicalTransmissionBridgeIsCanonical =
        refl
    ; authorityBoundary =
        Boundary.canonicalNeurochemicalAuthorityBoundary
    ; authorityBoundaryIsCanonical =
        refl
    ; surface =
        canonicalNeurochemicalProteinTargetSurface
    ; proteinCandidate =
        tt
    ; targetContext =
        tt
    ; receptorSubtypeCandidate =
        tt
    ; transporterCandidate =
        tt
    ; enzymeCandidate =
        tt
    ; ionChannelComplexCandidate =
        tt
    ; bindingSiteCandidate =
        tt
    ; conformationCandidate =
        tt
    ; actionCandidate =
        tt
    ; downstreamSignalingResidual =
        tt
    ; targetKinds =
        canonicalProteinTargetContextKinds
    ; targetKindsAreCanonical =
        refl
    ; actionKinds =
        canonicalProteinTargetActionCandidates
    ; actionKindsAreCanonical =
        refl
    ; residualKinds =
        canonicalProteinTargetResidualKinds
    ; residualKindsAreCanonical =
        refl
    ; guards =
        canonicalProteinTargetGuards
    ; guardsAreCanonical =
        refl
    ; authorityClaims =
        canonicalProteinTargetAuthorityClaims
    ; authorityClaimsAreCanonical =
        refl
    ; foldingAuthorityClaimFlag =
        false
    ; foldingAuthorityClaimFlagIsFalse =
        refl
    ; receptorActionIdentityAuthorityClaimFlag =
        false
    ; receptorActionIdentityAuthorityClaimFlagIsFalse =
        refl
    ; efficacyAuthorityClaimFlag =
        false
    ; efficacyAuthorityClaimFlagIsFalse =
        refl
    ; pathwayAuthorityClaimFlag =
        false
    ; pathwayAuthorityClaimFlagIsFalse =
        refl
    ; therapeuticAuthorityClaimFlag =
        false
    ; therapeuticAuthorityClaimFlagIsFalse =
        refl
    ; clinicalAuthorityClaimFlag =
        false
    ; clinicalAuthorityClaimFlagIsFalse =
        refl
    ; prescribingAuthorityClaimFlag =
        false
    ; prescribingAuthorityClaimFlagIsFalse =
        refl
    ; route =
        boundedProteinTargetReceiptRoute
    ; routeIsBounded =
        refl
    ; routeAdmissible =
        tt
    ; bridgeReading =
        "The protein target bridge keeps bioactive molecular recognition and neurochemical transmission in candidate-only receipt form, with receptor subtype, transporter, enzyme, ion-channel complex, and binding-site context available, while folding, receptor-action identity, efficacy, pathway, therapeutic, clinical, and prescribing authority stay blocked."
    }
