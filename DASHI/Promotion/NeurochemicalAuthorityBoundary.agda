module DASHI.Promotion.NeurochemicalAuthorityBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

open import DASHI.Constants.Registry as Registry

------------------------------------------------------------------------
-- Neurochemical promotion/authority boundary.
--
-- This module enumerates the concrete authority gaps that keep neurochemical
-- claims from being promoted through to empirical or clinical validity.
-- Rows are concrete surfaces: each names owner surface, source/consumer
-- receipts, required calibrations/adapters, and missing evidence kinds.

data NeurochemicalDomain : Set where
  kineticTransportCalibrationDomain : NeurochemicalDomain
  receptorBindingDomain : NeurochemicalDomain
  doseResponseDomain : NeurochemicalDomain
  pharmacologicalMechanismDomain : NeurochemicalDomain
  interventionCounterfactualDomain : NeurochemicalDomain
  clinicalUtilityDomain : NeurochemicalDomain
  biomarkerProtocolDomain : NeurochemicalDomain
  brainStateRecoveryDomain : NeurochemicalDomain

data NeurochemicalObligationKind : Set where
  kineticsConcentrationTransportCalibrationObligation : NeurochemicalObligationKind
  receptorBindingAuthorityObligation : NeurochemicalObligationKind
  doseResponseObligation : NeurochemicalObligationKind
  pharmacologicalMechanismObligation : NeurochemicalObligationKind
  interventionCounterfactualObligation : NeurochemicalObligationKind
  clinicalValidityUtilityObligation : NeurochemicalObligationKind
  biomarkerProtocolProvenanceObligation : NeurochemicalObligationKind
  brainStateRecoveryObligation : NeurochemicalObligationKind

data PromotionGuard : Set where
  guardKineticsConcentrationTransportPromoted : PromotionGuard
  guardReceptorBindingAuthorityPromoted : PromotionGuard
  guardDoseResponsePromoted : PromotionGuard
  guardPharmacologicalMechanismPromoted : PromotionGuard
  guardInterventionCounterfactualPromoted : PromotionGuard
  guardClinicalUtilityPromoted : PromotionGuard
  guardBiomarkerProtocolPromoted : PromotionGuard
  guardBrainStateRecoveryPromoted : PromotionGuard

data BoundaryStatus : Set where
  authorityTokenMissing : BoundaryStatus
  adapterProofMissing : BoundaryStatus
  replicationMissing : BoundaryStatus
  policyReceiptMissing : BoundaryStatus

record NeurochemicalBoundaryRow : Set where
  field
    rowLabel : String
    domain : NeurochemicalDomain
    obligationKind : NeurochemicalObligationKind
    targetGuard : PromotionGuard
    missingRequirement : String
    ownerSurface : String
    sourceReceipt : String
    consumingReceipt : String
    requiredCarrier : String
    requiredAuthorityInputs : List String
    requiredAdapterReceipts : List String
    requiredProofTokens : List String
    requiredValidation : List String
    promotionBlockedBy : List String
    status : BoundaryStatus
    promotesNeurochemicalClaim : Bool
    promotesNeurochemicalClaimIsFalse : promotesNeurochemicalClaim ≡ false

open NeurochemicalBoundaryRow public

mkBoundaryRow :
  String ->
  NeurochemicalDomain ->
  NeurochemicalObligationKind ->
  PromotionGuard ->
  String ->
  String ->
  String ->
  String ->
  String ->
  List String ->
  List String ->
  List String ->
  List String ->
  List String ->
  BoundaryStatus ->
  NeurochemicalBoundaryRow
mkBoundaryRow
  label
  domain
  kind
  guard
  missing
  owner
  source
  consumer
  carrier
  authorities
  adapters
  proofs
  validation
  blockers
  status =
  record
    { rowLabel = label
    ; domain = domain
    ; obligationKind = kind
    ; targetGuard = guard
    ; missingRequirement = missing
    ; ownerSurface = owner
    ; sourceReceipt = source
    ; consumingReceipt = consumer
    ; requiredCarrier = carrier
    ; requiredAuthorityInputs = authorities
    ; requiredAdapterReceipts = adapters
    ; requiredProofTokens = proofs
    ; requiredValidation = validation
    ; promotionBlockedBy = blockers
    ; status = status
    ; promotesNeurochemicalClaim = false
    ; promotesNeurochemicalClaimIsFalse = refl
    }

rowCount : List NeurochemicalBoundaryRow -> Nat
rowCount [] = zero
rowCount (_ ∷ xs) = suc (rowCount xs)

stringCount : List String -> Nat
stringCount [] = zero
stringCount (_ ∷ xs) = suc (stringCount xs)

neurochemicalAuthorityBoundaryRows : List NeurochemicalBoundaryRow
neurochemicalAuthorityBoundaryRows =
  mkBoundaryRow
    "kinetics, concentration, and transport calibration"
    kineticTransportCalibrationDomain
    kineticsConcentrationTransportCalibrationObligation
    guardKineticsConcentrationTransportPromoted
    "Neurochemical kinetics/concentration/transport claims are held to calibrated assay authority."
    "Ontology/ClinicalDiagnostics/TransportAndUncertainty.agda"
    "canonicalChemistryKnownInputsReferenceReceipt"
    "canonicalAuthorityConsumptionPolicyReceipt"
    "kinetic rate, concentration manifold, and transport carrier with assay geometry and unit semantics"
    ( "diffusion coefficients, permeabilities, binding constants, and concentration standard curves with version/checksum"
    ∷ "temperature, ionic-strength, pH, and redox context authority"
    ∷ "assay lot, protocol, and instrument calibration provenance"
    ∷ []
    )
    ( "kinetics law projection adapter"
    ∷ "concentration normalization adapter"
    ∷ "transport differential-equation adapter"
    ∷ "unit/uncertainty propagation adapter"
    ∷ []
    )
    ( "calibration replay token"
    ∷ "concentration/transport law preservation token"
    ∷ "unit consistency token on rate and permeability carriers"
    ∷ []
    )
    ( "agda -i . DASHI/Promotion/ChemistryBiologyObligations.agda"
    ∷ "agda -i . DASHI/Constants/Registry.agda"
    ∷ "agda -i . DASHI/Interop/ObservationTransportSpine.agda"
    ∷ []
    )
    ( "kineticsConcentrationTransportPromoted=false"
    ∷ "calibration authority missing"
    ∷ "transport boundary law unproven"
    ∷ []
    )
    authorityTokenMissing
  ∷ mkBoundaryRow
    "receptor binding authority"
    receptorBindingDomain
    receptorBindingAuthorityObligation
    guardReceptorBindingAuthorityPromoted
    "Receptor binding authority must be explicit for kinetic/occupancy claims."
    "Ontology/DNA/SupervoxelChemistryCouplingLaws.agda"
    "canonicalChemistryKnownInputsReferenceReceipt"
    "canonicalBiologyKnownInputsReferenceReceipt"
    "receptor occupancy, affinity, and dissociation constant carrier with subtype context"
    ( "measured binding affinities and EC50/Ki source/version/checksum"
    ∷ "receptor subtype identity and post-translational state authority"
    ∷ "dose-range dependent occupancy authority"
    ∷ []
    )
    ( "binding model to receptor occupancy adapter"
    ∷ "allosteric and competition model adapter"
    ∷ "subtype/provenance normalization adapter"
    ∷ []
    )
    ( "receptor binding authority token"
    ∷ "binding-law identifiability token"
    ∷ "counterexample boundary for subtype collapse"
    ∷ []
    )
    ( "agda -i . DASHI/Biology/ProteinHormoneChemistryCellBridge.agda"
    ∷ "agda -i . DASHI/Interop/ObservationTransportSpine.agda"
    ∷ []
    )
    ( "receptorBindingAuthorityPromoted=false"
    ∷ "binding context or subtype token absent"
    ∷ "receptor occupancy normalization proof missing"
    ∷ []
    )
    adapterProofMissing
  ∷ mkBoundaryRow
    "dose-response authority"
    doseResponseDomain
    doseResponseObligation
    guardDoseResponsePromoted
    "Dose-response parameters require calibrated concentration-response authority, design metadata, and transfer boundary checks."
    "DASHI/Biology/RetinalPerturbationObservationBridge.agda"
    "canonicalBiologyKnownInputsReferenceReceipt"
    "canonicalEmpiricalRuntimeKnownInputsReferenceReceipt"
    "dose vector, response surface, exposure duration, and endpoint carrier"
    ( "dose preparation protocol/source authority"
    ∷ "administration-route and bioavailability context authority"
    ∷ "response endpoint selection and threshold protocol"
    ∷ []
    )
    ( "dose-response regression adapter"
    ∷ "time-course and saturation boundary adapter"
    ∷ "counterfactual and missingness adapter"
    ∷ []
    )
    ( "dose-response curve identification token"
    ∷ "threshold safety bound token"
    ∷ "non-monotonicity boundary token"
    ∷ []
    )
    ( "agda -i . DASHI/Promotion/ChemistryBiologyObligations.agda"
    ∷ "agda -i . DASHI/Interop/ObservationTransportSpine.agda"
    ∷ []
    )
    ( "doseResponsePromoted=false"
    ∷ "dose calibration or route authority absent"
    ∷ "dose-response identifiability boundary unresolved"
    ∷ []
    )
    policyReceiptMissing
  ∷ mkBoundaryRow
    "pharmacological mechanism authority"
    pharmacologicalMechanismDomain
    pharmacologicalMechanismObligation
    guardPharmacologicalMechanismPromoted
    "Mechanistic claim requires receptor-to-pathway mapping and off-target authority."
    "DASHI/Biology/CellDifferentiationCommunicationBridge.agda"
    "canonicalBiologyKnownInputsReferenceReceipt"
    "canonicalAuthorityConsumptionPolicyReceipt"
    "target-pathway chain, intermediate state, and effect-size carrier"
    ( "pathway map and assay ontology authority"
    ∷ "off-target and compensatory pathway authority"
    ∷ "dose-response/kinetics coupling authority"
    ∷ []
    )
    ( "mechanism graph to outcome adapter"
    ∷ "off-target boundary adapter"
    ∷ "causality and mediation proof adapter"
    ∷ []
    )
    ( "pharmacological mechanism closure token"
    ∷ "pathway identifiability token"
    ∷ "mediator/control structure token"
    ∷ []
    )
    ( "agda -i . DASHI/Biology/CellDifferentiationCommunicationBridge.agda"
    ∷ "agda -i . DASHI/Interop/ObservationTransportSpine.agda"
    ∷ []
    )
    ( "pharmacologicalMechanismPromoted=false"
    ∷ "mechanism graph proof absent"
    ∷ "off-target boundary unconsumed"
    ∷ []
    )
    adapterProofMissing
  ∷ mkBoundaryRow
    "intervention and counterfactual authority"
    interventionCounterfactualDomain
    interventionCounterfactualObligation
    guardInterventionCounterfactualPromoted
    "Intervention and counterfactual neurochemical claims require assignment, protocol, and attribution authority."
    "DASHI/Physics/Closure/DevelopmentalGenomicInverseBridge.agda"
    "canonicalBiologyKnownInputsReferenceReceipt"
    "canonicalEmpiricalRuntimeKnownInputsReferenceReceipt"
    "intervention, randomization, comparator, safety boundary, and counterfactual outcome carriers"
    ( "intervention protocol versioned authority"
    ∷ "dose timing/course provenance"
    ∷ "control arm and randomization attribution receipts"
    ∷ []
    )
    ( "do-operator and assignment adapter"
    ∷ "counterfactual comparison adapter"
    ∷ "causal identifiability boundary adapter"
    ∷ "safety and ethics boundary adapter"
    ∷ []
    )
    ( "intervention effect token"
    ∷ "counterfactual validity token"
    ∷ "attribution and confound boundary token"
    ∷ []
    )
    ( "agda -i . DASHI/Promotion/ChemistryBiologyObligations.agda"
    ∷ "agda -i . DASHI/Biology/GenomeSensorimotorConnectomeBridge.agda"
    ∷ []
    )
    ( "interventionCounterfactualPromoted=false"
    ∷ "trial structure and counterfactual boundary missing"
    ∷ "causal assignment token absent"
    ∷ []
    )
    authorityTokenMissing
  ∷ mkBoundaryRow
    "clinical validity and utility authority"
    clinicalUtilityDomain
    clinicalValidityUtilityObligation
    guardClinicalUtilityPromoted
    "Clinical claims must be explicitly grounded in validity, utility, and regulatory authority."
    "Ontology/ClinicalDiagnostics/ClinicalDiagnosticsCore.agda"
    "canonicalBiologyKnownInputsReferenceReceipt"
    "canonicalAuthorityConsumptionPolicyReceipt"
    "clinical endpoint, cohort, threshold, utility, and risk/benefit carriers"
    ( "clinical validity authority"
    ∷ "clinical utility/recommendation authority"
    ∷ "cohort/population provenance"
    ∷ "adverse-event and follow-up protocol receipts"
    ∷ []
    )
    ( "diagnostic/prognostic comparison law adapter"
    ∷ "risk-benefit and utility policy adapter"
    ∷ "regulatory/ethics authority adapter"
    ∷ []
    )
    ( "clinical utility token"
    ∷ "clinical validity token"
    ∷ "population transferability token"
    ∷ []
    )
    ( "agda -i . DASHI/Promotion/ChemistryBiologyObligations.agda"
    ∷ "agda -i . Ontology/ClinicalDiagnostics/ClinicalDiagnosticsCore.agda"
    ∷ []
    )
    ( "clinicalUtilityPromoted=false"
    ∷ "clinical validity and utility token absent"
    ∷ "regulatory authority binding absent"
    ∷ []
    )
    policyReceiptMissing
  ∷ mkBoundaryRow
    "biomarker protocol and provenance"
    biomarkerProtocolDomain
    biomarkerProtocolProvenanceObligation
    guardBiomarkerProtocolPromoted
    "Biomarker claims require protocol, chain-of-custody, and provenance authority."
    "DASHI/Interop/ObservationTransportSpine.agda"
    "canonicalBiologyKnownInputsReferenceReceipt"
    "canonicalEmpiricalRuntimeKnownInputsReferenceReceipt"
    "biomarker assay, sample, storage, and metadata provenance carrier"
    ( "assay protocol authority"
    ∷ "sample/reagent/lot provenance"
    ∷ "pre-registered analysis and processing protocol"
    ∷ "biomarker panel checksum and access log"
    ∷ []
    )
    ( "assay-to-biomarker projection adapter"
    ∷ "provenance trace adapter"
    ∷ "negative/positive control adapter"
    ∷ "batch effect and drift adapter"
    ∷ []
    )
    ( "biomarker protocol token"
    ∷ "provenance audit token"
    ∷ "assay-chain reproducibility token"
    ∷ []
    )
    ( "agda -i . DASHI/Interop/ObservationTransportSpine.agda"
    ∷ "agda -i . Ontology/ClinicalDiagnostics/BridgeFromExistingReceipts.agda"
    ∷ []
    )
    ( "biomarkerProtocolPromoted=false"
    ∷ "provenance integrity token absent"
    ∷ "assay-chain authority token absent"
    ∷ []
    )
    replicationMissing
  ∷ mkBoundaryRow
    "brain-state recovery authority"
    brainStateRecoveryDomain
    brainStateRecoveryObligation
    guardBrainStateRecoveryPromoted
    "Brain-state recovery remains external unless connectome, BIDS/FAIR, and identifiability authority are consumed."
    "DASHI/Biology/GenomeSensorimotorConnectomeBridge.agda"
    "canonicalBiologyKnownInputsReferenceReceipt"
    "canonicalEmpiricalRuntimeKnownInputsReferenceReceipt"
    "subject/session/task/modality/connectome, parcellation, and latent-state recovery carriers"
    ( "connectome/BIDS/FAIR provenance authority"
    ∷ "dataset checksum and selection/subject-level provenance"
    ∷ "reconstruction and recovery identifiability authority"
    ∷ []
    )
    ( "connectome parsing/reconstruction adapter"
    ∷ "latent-state recovery projection adapter"
    ∷ "non-identifiability boundary adapter"
    ∷ []
    )
    ( "brain-state recovery token"
    ∷ "validation holdout token"
    ∷ "dataset-replay token"
    ∷ []
    )
    ( "agda -i . DASHI/Biology/GenomeSensorimotorConnectomeBridge.agda"
    ∷ "agda -i . Ontology/ClinicalDiagnostics/ClinicalDiagnosticsCore.agda"
    ∷ []
    )
    ( "brainStateRecoveryPromoted=false"
    ∷ "connectome/BIDS provenance missing"
    ∷ "latent recovery proof absent"
    ∷ []
    )
    adapterProofMissing
  ∷ []

record NeurochemicalAuthorityBoundary : Set₁ where
  field
    chemistryReceipt : Registry.ChemistryKnownInputsReferenceReceipt
    biologyReceipt : Registry.BiologyKnownInputsReferenceReceipt
    authorityPolicyReceipt : Registry.AuthorityConsumptionPolicyReceipt
    empiricalRuntimeReceipt : Registry.EmpiricalRuntimeKnownInputsReferenceReceipt
    missingRequirements : List String
    missingRequirementCount : Nat
    missingRequirementCountIs8 : missingRequirementCount ≡ 8
    chemistryAdapterGaps : List String
    biologyAdapterGaps : List String
    boundaryRows : List NeurochemicalBoundaryRow
    boundaryRowCount : Nat
    boundaryRowCountMatches : boundaryRowCount ≡ rowCount boundaryRows

    kineticsConcentrationTransportCalibrationPromoted : Bool
    kineticsConcentrationTransportCalibrationPromotedIsFalse :
      kineticsConcentrationTransportCalibrationPromoted ≡ false
    receptorBindingAuthorityPromoted : Bool
    receptorBindingAuthorityPromotedIsFalse : receptorBindingAuthorityPromoted ≡ false
    doseResponsePromoted : Bool
    doseResponsePromotedIsFalse : doseResponsePromoted ≡ false
    pharmacologicalMechanismPromoted : Bool
    pharmacologicalMechanismPromotedIsFalse :
      pharmacologicalMechanismPromoted ≡ false
    interventionCounterfactualPromoted : Bool
    interventionCounterfactualPromotedIsFalse :
      interventionCounterfactualPromoted ≡ false
    clinicalValidityAccepted : Bool
    clinicalValidityAcceptedIsFalse : clinicalValidityAccepted ≡ false
    biomarkerProtocolPromoted : Bool
    biomarkerProtocolPromotedIsFalse : biomarkerProtocolPromoted ≡ false
    brainStateRecoveryPromoted : Bool
    brainStateRecoveryPromotedIsFalse : brainStateRecoveryPromoted ≡ false

    biologyCausationPromoted : Bool
    biologyCausationPromotedIsFalse : biologyCausationPromoted ≡ false
    interventionPromoted : Bool
    interventionPromotedIsFalse : interventionPromoted ≡ false
    clinicalValidityFromRegistry : Bool
    clinicalValidityFromRegistryIsFalse : clinicalValidityFromRegistry ≡ false
    brainStateRecoveryFromRegistry : Bool
    brainStateRecoveryFromRegistryIsFalse : brainStateRecoveryFromRegistry ≡ false
    chemistryExternalInputOnly : Bool
    chemistryExternalInputOnlyIsTrue : chemistryExternalInputOnly ≡ true
    biologyExternalInputOnly : Bool
    biologyExternalInputOnlyIsTrue : biologyExternalInputOnly ≡ true

    validationCommand : String

open NeurochemicalAuthorityBoundary public

canonicalNeurochemicalAuthorityBoundary :
  NeurochemicalAuthorityBoundary
canonicalNeurochemicalAuthorityBoundary = record
  { chemistryReceipt = Registry.canonicalChemistryKnownInputsReferenceReceipt
  ; biologyReceipt = Registry.canonicalBiologyKnownInputsReferenceReceipt
  ; authorityPolicyReceipt =
      Registry.canonicalAuthorityConsumptionPolicyReceipt
  ; empiricalRuntimeReceipt =
      Registry.canonicalEmpiricalRuntimeKnownInputsReferenceReceipt
  ; missingRequirements =
      "kinetics/concentration/transport calibration"
      ∷ "receptor binding authority"
      ∷ "dose-response evidence and calibration"
      ∷ "pharmacological mechanism decomposition"
      ∷ "intervention/counterfactual attribution"
      ∷ "clinical validity and utility"
      ∷ "biomarker protocol and provenance"
      ∷ "brain-state recovery"
      ∷ []
  ; missingRequirementCount =
      stringCount
        ( "kinetics/concentration/transport calibration"
        ∷ "receptor binding authority"
        ∷ "dose-response evidence and calibration"
        ∷ "pharmacological mechanism decomposition"
        ∷ "intervention/counterfactual attribution"
        ∷ "clinical validity and utility"
        ∷ "biomarker protocol and provenance"
        ∷ "brain-state recovery"
        ∷ []
        )
  ; missingRequirementCountIs8 = refl
  ; chemistryAdapterGaps =
      Registry.ChemistryKnownInputsReferenceReceipt.missingChemistryAdapters
        Registry.canonicalChemistryKnownInputsReferenceReceipt
  ; biologyAdapterGaps =
      Registry.BiologyKnownInputsReferenceReceipt.missingBiologyAdapters
        Registry.canonicalBiologyKnownInputsReferenceReceipt
  ; boundaryRows = neurochemicalAuthorityBoundaryRows
  ; boundaryRowCount = rowCount neurochemicalAuthorityBoundaryRows
  ; boundaryRowCountMatches = refl
  ; kineticsConcentrationTransportCalibrationPromoted = false
  ; kineticsConcentrationTransportCalibrationPromotedIsFalse = refl
  ; receptorBindingAuthorityPromoted = false
  ; receptorBindingAuthorityPromotedIsFalse = refl
  ; doseResponsePromoted = false
  ; doseResponsePromotedIsFalse = refl
  ; pharmacologicalMechanismPromoted = false
  ; pharmacologicalMechanismPromotedIsFalse = refl
  ; interventionCounterfactualPromoted = false
  ; interventionCounterfactualPromotedIsFalse = refl
  ; clinicalValidityAccepted = false
  ; clinicalValidityAcceptedIsFalse = refl
  ; biomarkerProtocolPromoted = false
  ; biomarkerProtocolPromotedIsFalse = refl
  ; brainStateRecoveryPromoted = false
  ; brainStateRecoveryPromotedIsFalse = refl
  ; biologyCausationPromoted =
      Registry.BiologyKnownInputsReferenceReceipt.biologyCausationPromoted
        Registry.canonicalBiologyKnownInputsReferenceReceipt
  ; biologyCausationPromotedIsFalse =
      Registry.BiologyKnownInputsReferenceReceipt.biologyCausationPromotedIsFalse
        Registry.canonicalBiologyKnownInputsReferenceReceipt
  ; interventionPromoted =
      Registry.BiologyKnownInputsReferenceReceipt.interventionPromoted
        Registry.canonicalBiologyKnownInputsReferenceReceipt
  ; interventionPromotedIsFalse =
      Registry.BiologyKnownInputsReferenceReceipt.interventionPromotedIsFalse
        Registry.canonicalBiologyKnownInputsReferenceReceipt
  ; clinicalValidityFromRegistry =
      Registry.BiologyKnownInputsReferenceReceipt.clinicalValidityAccepted
        Registry.canonicalBiologyKnownInputsReferenceReceipt
  ; clinicalValidityFromRegistryIsFalse =
      Registry.BiologyKnownInputsReferenceReceipt.clinicalValidityAcceptedIsFalse
        Registry.canonicalBiologyKnownInputsReferenceReceipt
  ; brainStateRecoveryFromRegistry =
      Registry.BiologyKnownInputsReferenceReceipt.brainStateRecoveryPromoted
        Registry.canonicalBiologyKnownInputsReferenceReceipt
  ; brainStateRecoveryFromRegistryIsFalse =
      Registry.BiologyKnownInputsReferenceReceipt.brainStateRecoveryPromotedIsFalse
        Registry.canonicalBiologyKnownInputsReferenceReceipt
  ; chemistryExternalInputOnly =
      Registry.ChemistryKnownInputsReferenceReceipt.externalInputOnly
        Registry.canonicalChemistryKnownInputsReferenceReceipt
  ; chemistryExternalInputOnlyIsTrue =
      Registry.ChemistryKnownInputsReferenceReceipt.externalInputOnlyIsTrue
        Registry.canonicalChemistryKnownInputsReferenceReceipt
  ; biologyExternalInputOnly =
      Registry.BiologyKnownInputsReferenceReceipt.externalInputOnly
        Registry.canonicalBiologyKnownInputsReferenceReceipt
  ; biologyExternalInputOnlyIsTrue =
      Registry.BiologyKnownInputsReferenceReceipt.externalInputOnlyIsTrue
        Registry.canonicalBiologyKnownInputsReferenceReceipt
  ; validationCommand =
      "agda -i . DASHI/Promotion/NeurochemicalAuthorityBoundary.agda"
  }

canonicalNeurochemicalBoundaryRowCountIs8 :
  NeurochemicalAuthorityBoundary.boundaryRowCount
    canonicalNeurochemicalAuthorityBoundary
  ≡
  8
canonicalNeurochemicalBoundaryRowCountIs8 = refl

canonicalKineticsConcentrationTransportCalibrationProjectionIsFalse :
  NeurochemicalAuthorityBoundary.kineticsConcentrationTransportCalibrationPromoted
    canonicalNeurochemicalAuthorityBoundary
  ≡ false
canonicalKineticsConcentrationTransportCalibrationProjectionIsFalse = refl

canonicalReceptorBindingProjectionIsFalse :
  NeurochemicalAuthorityBoundary.receptorBindingAuthorityPromoted
    canonicalNeurochemicalAuthorityBoundary
  ≡ false
canonicalReceptorBindingProjectionIsFalse = refl

canonicalDoseResponseProjectionIsFalse :
  NeurochemicalAuthorityBoundary.doseResponsePromoted
    canonicalNeurochemicalAuthorityBoundary
  ≡ false
canonicalDoseResponseProjectionIsFalse = refl

canonicalPharmacologicalMechanismProjectionIsFalse :
  NeurochemicalAuthorityBoundary.pharmacologicalMechanismPromoted
    canonicalNeurochemicalAuthorityBoundary
  ≡ false
canonicalPharmacologicalMechanismProjectionIsFalse = refl

canonicalInterventionCounterfactualProjectionIsFalse :
  NeurochemicalAuthorityBoundary.interventionCounterfactualPromoted
    canonicalNeurochemicalAuthorityBoundary
  ≡ false
canonicalInterventionCounterfactualProjectionIsFalse = refl

canonicalClinicalValidityProjectionIsFalse :
  NeurochemicalAuthorityBoundary.clinicalValidityAccepted
    canonicalNeurochemicalAuthorityBoundary
  ≡ false
canonicalClinicalValidityProjectionIsFalse = refl

canonicalBiomarkerProtocolProjectionIsFalse :
  NeurochemicalAuthorityBoundary.biomarkerProtocolPromoted
    canonicalNeurochemicalAuthorityBoundary
  ≡ false
canonicalBiomarkerProtocolProjectionIsFalse = refl

canonicalBrainStateRecoveryProjectionIsFalse :
  NeurochemicalAuthorityBoundary.brainStateRecoveryPromoted
    canonicalNeurochemicalAuthorityBoundary
  ≡ false
canonicalBrainStateRecoveryProjectionIsFalse = refl
