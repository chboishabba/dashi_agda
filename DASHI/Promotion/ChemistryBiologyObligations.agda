module DASHI.Promotion.ChemistryBiologyObligations where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

open import DASHI.Constants.Registry as Registry

------------------------------------------------------------------------
-- Chemistry and biology promotion obligation index.
--
-- This module is a compiling obligation surface for the currently false
-- chemistry/biology promotion guards.  It is not a skeleton: each canonical
-- row records the concrete owner surface, adapter package, authority package,
-- proof token target, validation surface, and guard that must be discharged
-- before a promotion flag can be flipped.

data PromotionDomain : Set where
  physicalChemistryDomain : PromotionDomain
  spectroscopyDomain : PromotionDomain
  bondingDomain : PromotionDomain
  wetLabChemistryDomain : PromotionDomain
  biologyCausationDomain : PromotionDomain
  biologyInterventionDomain : PromotionDomain
  clinicalValidityDomain : PromotionDomain
  brainStateRecoveryDomain : PromotionDomain

data ObligationKind : Set where
  scaleSettingObligation : ObligationKind
  hamiltonianSpectralObservableObligation : ObligationKind
  bondingPreservationObligation : ObligationKind
  authorityBindingObligation : ObligationKind
  instrumentCalibrationObligation : ObligationKind
  wetLabProtocolReplicationObligation : ObligationKind
  organismCellTissueSessionProvenanceObligation : ObligationKind
  causalModelObligation : ObligationKind
  interventionCounterfactualObligation : ObligationKind
  clinicalValidityUtilityObligation : ObligationKind
  neuroimagingConnectomeProvenanceObligation : ObligationKind

data PromotionGuard : Set where
  guardPhysicalChemistryPromoted : PromotionGuard
  guardSpectroscopyPromoted : PromotionGuard
  guardBondingInterpretationPromoted : PromotionGuard
  guardWetLabValidationAccepted : PromotionGuard
  guardBiologyCausationPromoted : PromotionGuard
  guardInterventionPromoted : PromotionGuard
  guardClinicalValidityAccepted : PromotionGuard
  guardBrainStateRecoveryPromoted : PromotionGuard

data ObligationStatus : Set where
  obligationOpen : ObligationStatus
  authorityTokenMissing : ObligationStatus
  adapterProofMissing : ObligationStatus
  replicationMissing : ObligationStatus

record PromotionObligationRow : Set₁ where
  field
    rowLabel : String
    domain : PromotionDomain
    obligationKind : ObligationKind
    targetGuard : PromotionGuard
    ownerSurface : String
    sourceReceipt : String
    consumingReceipt : String
    requiredCarrier : String
    requiredAuthorityInputs : List String
    requiredAdapterReceipts : List String
    requiredProofTokens : List String
    requiredValidation : List String
    promotionBlockedBy : List String
    status : ObligationStatus
    promotesClaim : Bool
    promotesClaimIsFalse : promotesClaim ≡ false

open PromotionObligationRow public

mkObligation :
  String →
  PromotionDomain →
  ObligationKind →
  PromotionGuard →
  String →
  String →
  String →
  String →
  List String →
  List String →
  List String →
  List String →
  List String →
  ObligationStatus →
  PromotionObligationRow
mkObligation label domain kind guard owner source consumer carrier
  authorities adapters proofs validation blockers status =
  record
    { rowLabel = label
    ; domain = domain
    ; obligationKind = kind
    ; targetGuard = guard
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
    ; promotesClaim = false
    ; promotesClaimIsFalse = refl
    }

rowCount : List PromotionObligationRow → Nat
rowCount [] = zero
rowCount (_ ∷ xs) = suc (rowCount xs)

chemistryPromotionObligations : List PromotionObligationRow
chemistryPromotionObligations =
  mkObligation
    "physical chemistry scale-setting"
    physicalChemistryDomain
    scaleSettingObligation
    guardPhysicalChemistryPromoted
    "DASHI/Physics/Closure/ChemistryStrictPhysicalSemanticsBlocker.agda"
    "canonicalChemistryKnownInputsReferenceReceipt"
    "canonicalAuthorityConsumptionPolicyReceipt"
    "physical unit, length, time, charge, energy, temperature, amount, and concentration scale carrier for quotient classes"
    ( "BIPM/NIST exact SI source for c, h, e, k_B, N_A"
    ∷ "CODATA source for alpha, m_e, m_p, epsilon_0, mu_0, R_infinity, a_0, E_h"
    ∷ "NIST Chemistry WebBook or provider source for thermochemical state variables"
    ∷ []
    )
    ( "unit-convention receipt"
    ∷ "scale-setting functor from definitional quotient carrier to physical quantity carrier"
    ∷ "dimensional-analysis preservation receipt"
    ∷ "rounding and uncertainty propagation policy"
    ∷ []
    )
    ( "scale-setting law inhabited for every consumed quotient class"
    ∷ "numeric measured constants consumed through authority policy"
    ∷ "no unit-free physical-chemistry claim remains"
    ∷ []
    )
    ( "agda -i . DASHI/Promotion/ChemistryBiologyObligations.agda"
    ∷ "agda -i . DASHI/Constants/Registry.agda"
    ∷ "agda -i . DASHI/Physics/Closure/ChemistryStrictPhysicalSemanticsBlocker.agda"
    ∷ []
    )
    ( "physicalChemistryPromoted=false"
    ∷ "numeric measured constants not promoted"
    ∷ "scale-setting law absent at consuming quotient sites"
    ∷ []
    )
    adapterProofMissing
  ∷ mkObligation
    "Hamiltonian to spectral observable map"
    spectroscopyDomain
    hamiltonianSpectralObservableObligation
    guardSpectroscopyPromoted
    "Ontology/DNA/ChemistrySheetHamiltonian.agda"
    "canonicalChemistryKnownInputsReferenceReceipt"
    "canonicalPhysicsAdapterKnownInputsReferenceReceipt"
    "atomic or molecular Hamiltonian carrier with spectral observable and instrument response target"
    ( "exact h, hbar, c, e"
    ∷ "CODATA alpha, m_e, nuclear/isotopic mass authority"
    ∷ "NIST spectral line or WebBook spectrum authority"
    ∷ []
    )
    ( "self-adjoint Hamiltonian/domain receipt at molecular scale"
    ∷ "eigenvalue or transition observable projection"
    ∷ "line broadening, selection-rule, and instrument-response adapter"
    ∷ "wavelength/frequency/energy unit convention"
    ∷ []
    )
    ( "spectral observable map preservation law"
    ∷ "source spectrum checksum consumed"
    ∷ "comparison residual and tolerance law"
    ∷ []
    )
    ( "agda -i . DASHI/Promotion/ChemistryBiologyObligations.agda"
    ∷ "agda -i . DASHI/Constants/Registry.agda"
    ∷ []
    )
    ( "spectroscopyPromoted=false"
    ∷ "physical Hilbert/Hamiltonian adapter incomplete"
    ∷ "instrument comparison law absent"
    ∷ []
    )
    adapterProofMissing
  ∷ mkObligation
    "bonding interpretation preservation"
    bondingDomain
    bondingPreservationObligation
    guardBondingInterpretationPromoted
    "DASHI/Physics/Closure/AtomicChemistryRecoveryTheorem.agda"
    "canonicalChemistryKnownInputsReferenceReceipt"
    "canonicalPhysicsAdapterKnownInputsReferenceReceipt"
    "bond graph, orbital, electron-density, or energy-partition carrier with explicit interpretation semantics"
    ( "CODATA electron/proton/nuclear mass and electromagnetic constants"
    ∷ "domain authority for molecular geometry, charge state, and reference method"
    ∷ "thermochemistry or structural database checksum where consumed"
    ∷ []
    )
    ( "bonding carrier extraction receipt"
    ∷ "gauge/basis invariance or convention-boundary receipt"
    ∷ "preservation map from Hamiltonian/supervoxel carrier to bond semantics"
    ∷ "counterexample boundary for noncanonical bonding decompositions"
    ∷ []
    )
    ( "bonding interpretation preservation theorem"
    ∷ "chosen convention and validity regime inhabited"
    ∷ "non-uniqueness boundary accepted by consuming claim"
    ∷ []
    )
    ( "agda -i . DASHI/Promotion/ChemistryBiologyObligations.agda"
    ∷ "agda -i . DASHI/Physics/Closure/AtomicChemistryRecoveryTheorem.agda"
    ∷ []
    )
    ( "bondingInterpretationPromoted=false"
    ∷ "bonding carrier and preservation law absent"
    ∷ "basis/gauge/convention boundary not consumed"
    ∷ []
    )
    adapterProofMissing
  ∷ mkObligation
    "NIST WebBook CODATA chemistry authority binding"
    physicalChemistryDomain
    authorityBindingObligation
    guardPhysicalChemistryPromoted
    "DASHI/Constants/Registry.agda"
    "canonicalAuthorityConsumptionPolicyReceipt"
    "canonicalChemistryKnownInputsReferenceReceipt"
    "per-constant and per-property authority binding carrier"
    ( "NIST Chemistry WebBook URI/version/checksum"
    ∷ "NIST CODATA version/checksum/access date"
    ∷ "BIPM/NIST SI source and unit convention"
    ∷ []
    )
    ( "authorityVersion field"
    ∷ "sourceChecksum field"
    ∷ "sourceAccessDate field"
    ∷ "valueUncertainty field"
    ∷ "roundingPolicy field"
    ∷ "unitConvention field"
    ∷ "validityRegime field"
    ∷ []
    )
    ( "accepted authority token for each consumed measured value"
    ∷ "property-to-law target binding proof"
    ∷ "consumer cites the exact authority slot"
    ∷ []
    )
    ( "agda -i . DASHI/Constants/Registry.agda"
    ∷ "agda -i . DASHI/Promotion/ChemistryBiologyObligations.agda"
    ∷ []
    )
    ( "acceptedAuthorityTokenPresent=false"
    ∷ "numericValuePromoted=false"
    ∷ "modelLawPromoted=false"
    ∷ []
    )
    authorityTokenMissing
  ∷ mkObligation
    "instrument calibration and chemistry comparison law"
    spectroscopyDomain
    instrumentCalibrationObligation
    guardSpectroscopyPromoted
    "DASHI/Physics/Closure/Candidate256PhysicalCalibrationExternalReceipt.agda"
    "canonicalChemistryKnownInputsReferenceReceipt"
    "canonicalEmpiricalRuntimeKnownInputsReferenceReceipt"
    "instrument state, calibration artifact, observable transform, covariance, and residual carrier"
    ( "instrument certificate or provider receipt"
    ∷ "calibration standard authority"
    ∷ "observable unit and covariance metadata"
    ∷ []
    )
    ( "instrument-response transform"
    ∷ "baseline/noise/covariance adapter"
    ∷ "comparison law and residual acceptance criterion"
    ∷ "calibration replay or audit receipt"
    ∷ []
    )
    ( "calibration token accepted by consumer"
    ∷ "comparison law inhabited"
    ∷ "holdout or replicate spectrum accepted"
    ∷ []
    )
    ( "agda -i . DASHI/Promotion/ChemistryBiologyObligations.agda"
    ∷ []
    )
    ( "calibrationPromoted=false"
    ∷ "covarianceCalibrationPromoted=false"
    ∷ "comparisonLawPromoted=false"
    ∷ []
    )
    authorityTokenMissing
  ∷ mkObligation
    "wet-lab protocol and replication"
    wetLabChemistryDomain
    wetLabProtocolReplicationObligation
    guardWetLabValidationAccepted
    "DASHI/Physics/Closure/ChemistryPhysicalHandoffDiagnostic.agda"
    "canonicalChemistryKnownInputsReferenceReceipt"
    "canonicalEmpiricalRuntimeKnownInputsReferenceReceipt"
    "protocol, sample, reagent, instrument, replicate, and acceptance carrier"
    ( "protocol registry or lab notebook checksum"
    ∷ "sample/reagent lot provenance"
    ∷ "instrument run metadata"
    ∷ "replicate dataset checksum"
    ∷ []
    )
    ( "protocol-to-observable projection"
    ∷ "replicate comparison law"
    ∷ "negative/positive control adapter"
    ∷ "pre-registered acceptance threshold"
    ∷ []
    )
    ( "replication accepted token"
    ∷ "control-pass token"
    ∷ "wet-lab provenance audit token"
    ∷ []
    )
    ( "agda -i . DASHI/Promotion/ChemistryBiologyObligations.agda"
    ∷ []
    )
    ( "wetLabValidationAccepted=false"
    ∷ "holdoutValidationAccepted=false"
    ∷ "semanticAdequacyAccepted=false"
    ∷ []
    )
    replicationMissing
  ∷ []

biologyPromotionObligations : List PromotionObligationRow
biologyPromotionObligations =
  mkObligation
    "organism cell tissue session provenance"
    biologyCausationDomain
    organismCellTissueSessionProvenanceObligation
    guardBiologyCausationPromoted
    "DASHI/Biology/ProteinHormoneChemistryCellBridge.agda"
    "canonicalBiologyKnownInputsReferenceReceipt"
    "canonicalAuthorityConsumptionPolicyReceipt"
    "organism, genotype, cell-line, tissue, environment, session, and assay context carrier"
    ( "organism taxonomy/sample authority"
    ∷ "cell-line authentication and passage metadata"
    ∷ "tissue source, consent/ethics, and phenotype context"
    ∷ "assay/session source URI, version, checksum, and access date"
    ∷ []
    )
    ( "sample identity adapter"
    ∷ "context normalization adapter"
    ∷ "assay protocol projection"
    ∷ "batch and confound boundary receipt"
    ∷ []
    )
    ( "provenance completeness token"
    ∷ "context compatibility token"
    ∷ "assay-source checksum accepted by consumer"
    ∷ []
    )
    ( "agda -i . DASHI/Promotion/ChemistryBiologyObligations.agda"
    ∷ "agda -i . DASHI/Constants/Registry.agda"
    ∷ []
    )
    ( "biologyCausationPromoted=false"
    ∷ "organism/cell/tissue/session provenance incomplete"
    ∷ "context-free translation remains blocked"
    ∷ []
    )
    authorityTokenMissing
  ∷ mkObligation
    "biology causal model identification"
    biologyCausationDomain
    causalModelObligation
    guardBiologyCausationPromoted
    "DASHI/Biology/CellDifferentiationCommunicationBridge.agda"
    "canonicalBiologyKnownInputsReferenceReceipt"
    "canonicalEmpiricalRuntimeKnownInputsReferenceReceipt"
    "directed causal graph, structural equation, intervention set, confound set, and outcome carrier"
    ( "observational dataset checksum"
    ∷ "assay protocol and sampling frame authority"
    ∷ "covariate, confound, and environment provenance"
    ∷ []
    )
    ( "causal graph declaration receipt"
    ∷ "identification criterion receipt"
    ∷ "confounding and selection-bias boundary receipt"
    ∷ "effect-size and uncertainty policy"
    ∷ []
    )
    ( "backdoor/frontdoor/randomization or equivalent identification proof"
    ∷ "causal estimand-to-observable map"
    ∷ "sensitivity-analysis boundary token"
    ∷ []
    )
    ( "agda -i . DASHI/Promotion/ChemistryBiologyObligations.agda"
    ∷ []
    )
    ( "biologyCausationPromoted=false"
    ∷ "causal identification proof missing"
    ∷ "observational bridge remains non-causal"
    ∷ []
    )
    adapterProofMissing
  ∷ mkObligation
    "intervention and counterfactual validation"
    biologyInterventionDomain
    interventionCounterfactualObligation
    guardInterventionPromoted
    "DASHI/Physics/Closure/DevelopmentalGenomicInverseBridge.agda"
    "canonicalBiologyKnownInputsReferenceReceipt"
    "canonicalEmpiricalRuntimeKnownInputsReferenceReceipt"
    "intervention, dose/time, perturbation, counterfactual, outcome, and safety-boundary carrier"
    ( "intervention protocol authority"
    ∷ "dose/time/course provenance"
    ∷ "control group and assignment receipt"
    ∷ "outcome assay checksum"
    ∷ []
    )
    ( "do-operator or randomized-assignment adapter"
    ∷ "counterfactual comparison law"
    ∷ "safety/ethics boundary receipt"
    ∷ "holdout or replication adapter"
    ∷ []
    )
    ( "intervention effect token"
    ∷ "counterfactual validity token"
    ∷ "replication or holdout pass token"
    ∷ []
    )
    ( "agda -i . DASHI/Promotion/ChemistryBiologyObligations.agda"
    ∷ []
    )
    ( "interventionPromoted=false"
    ∷ "holdoutValidationAccepted=false"
    ∷ "counterfactual boundary uninhabited"
    ∷ []
    )
    adapterProofMissing
  ∷ mkObligation
    "clinical validity and utility"
    clinicalValidityDomain
    clinicalValidityUtilityObligation
    guardClinicalValidityAccepted
    "DASHI/Biology/GenomeSensorimotorConnectomeBridge.agda"
    "canonicalBiologyKnownInputsReferenceReceipt"
    "canonicalAuthorityConsumptionPolicyReceipt"
    "clinical endpoint, population, decision threshold, utility, risk, and regulatory boundary carrier"
    ( "clinical validity authority"
    ∷ "clinical utility or guideline authority"
    ∷ "cohort/population provenance"
    ∷ "endpoint and adverse-event source checksum"
    ∷ []
    )
    ( "diagnostic/prognostic comparison law"
    ∷ "population applicability adapter"
    ∷ "risk-benefit and intervention utility boundary"
    ∷ "regulatory/ethics authority adapter"
    ∷ []
    )
    ( "clinical validity accepted token"
    ∷ "clinical utility accepted token"
    ∷ "population validity and calibration token"
    ∷ []
    )
    ( "agda -i . DASHI/Promotion/ChemistryBiologyObligations.agda"
    ∷ []
    )
    ( "clinicalValidityAccepted=false"
    ∷ "clinical utility not inferred from biological structure"
    ∷ "regulatory authority token absent"
    ∷ []
    )
    authorityTokenMissing
  ∷ mkObligation
    "neuroimaging connectome BIDS FAIR checksum"
    brainStateRecoveryDomain
    neuroimagingConnectomeProvenanceObligation
    guardBrainStateRecoveryPromoted
    "DASHI/Biology/GenomeSensorimotorConnectomeBridge.agda"
    "canonicalBiologyKnownInputsReferenceReceipt"
    "canonicalEmpiricalRuntimeKnownInputsReferenceReceipt"
    "subject/session/task/modality/connectome/parcellation/feature and latent-state carrier"
    ( "BIDS dataset metadata"
    ∷ "FAIR provenance metadata"
    ∷ "connectome dataset checksum"
    ∷ "neuroimaging acquisition and preprocessing receipt"
    ∷ []
    )
    ( "BIDS validator receipt"
    ∷ "preprocessing pipeline replay receipt"
    ∷ "connectome parcellation and feature projection adapter"
    ∷ "latent-state non-identifiability boundary receipt"
    ∷ []
    )
    ( "dataset checksum accepted token"
    ∷ "pipeline replay accepted token"
    ∷ "brain-state recovery identifiability proof"
    ∷ "holdout decoding/replication token"
    ∷ []
    )
    ( "agda -i . DASHI/Promotion/ChemistryBiologyObligations.agda"
    ∷ "agda -i . DASHI/Constants/Registry.agda"
    ∷ []
    )
    ( "brainStateRecoveryPromoted=false"
    ∷ "genomeToConnectomeClosurePromoted=false"
    ∷ "neuroimaging/connectome source accepted token absent"
    ∷ "latent brain-state identifiability proof absent"
    ∷ []
    )
    adapterProofMissing
  ∷ []

allChemistryBiologyPromotionObligations :
  List PromotionObligationRow
allChemistryBiologyPromotionObligations =
  chemistryPromotionObligations ++ biologyPromotionObligations
  where
    _++_ : List PromotionObligationRow → List PromotionObligationRow →
           List PromotionObligationRow
    [] ++ ys = ys
    (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

record ChemistryBiologyPromotionObligationIndex : Set₁ where
  field
    chemistryReceipt : Registry.ChemistryKnownInputsReferenceReceipt
    biologyReceipt : Registry.BiologyKnownInputsReferenceReceipt
    authorityPolicy : Registry.AuthorityConsumptionPolicyReceipt
    obligations : List PromotionObligationRow
    obligationCount : Nat
    obligationCountMatches : obligationCount ≡ rowCount obligations

    physicalChemistryPromoted : Bool
    physicalChemistryPromotedIsFalse : physicalChemistryPromoted ≡ false
    spectroscopyPromoted : Bool
    spectroscopyPromotedIsFalse : spectroscopyPromoted ≡ false
    bondingInterpretationPromoted : Bool
    bondingInterpretationPromotedIsFalse :
      bondingInterpretationPromoted ≡ false
    wetLabValidationAccepted : Bool
    wetLabValidationAcceptedIsFalse : wetLabValidationAccepted ≡ false

    biologyCausationPromoted : Bool
    biologyCausationPromotedIsFalse : biologyCausationPromoted ≡ false
    interventionPromoted : Bool
    interventionPromotedIsFalse : interventionPromoted ≡ false
    clinicalValidityAccepted : Bool
    clinicalValidityAcceptedIsFalse : clinicalValidityAccepted ≡ false
    brainStateRecoveryPromoted : Bool
    brainStateRecoveryPromotedIsFalse : brainStateRecoveryPromoted ≡ false

    promotionProtocol : List String
    validationCommand : String

open ChemistryBiologyPromotionObligationIndex public

canonicalChemistryBiologyPromotionObligationIndex :
  ChemistryBiologyPromotionObligationIndex
canonicalChemistryBiologyPromotionObligationIndex = record
  { chemistryReceipt =
      Registry.canonicalChemistryKnownInputsReferenceReceipt
  ; biologyReceipt =
      Registry.canonicalBiologyKnownInputsReferenceReceipt
  ; authorityPolicy =
      Registry.canonicalAuthorityConsumptionPolicyReceipt
  ; obligations =
      allChemistryBiologyPromotionObligations
  ; obligationCount =
      rowCount allChemistryBiologyPromotionObligations
  ; obligationCountMatches =
      refl
  ; physicalChemistryPromoted =
      Registry.ChemistryKnownInputsReferenceReceipt.physicalChemistryPromoted
        Registry.canonicalChemistryKnownInputsReferenceReceipt
  ; physicalChemistryPromotedIsFalse =
      Registry.ChemistryKnownInputsReferenceReceipt.physicalChemistryPromotedIsFalse
        Registry.canonicalChemistryKnownInputsReferenceReceipt
  ; spectroscopyPromoted =
      Registry.ChemistryKnownInputsReferenceReceipt.spectroscopyPromoted
        Registry.canonicalChemistryKnownInputsReferenceReceipt
  ; spectroscopyPromotedIsFalse =
      Registry.ChemistryKnownInputsReferenceReceipt.spectroscopyPromotedIsFalse
        Registry.canonicalChemistryKnownInputsReferenceReceipt
  ; bondingInterpretationPromoted =
      Registry.ChemistryKnownInputsReferenceReceipt.bondingInterpretationPromoted
        Registry.canonicalChemistryKnownInputsReferenceReceipt
  ; bondingInterpretationPromotedIsFalse =
      Registry.ChemistryKnownInputsReferenceReceipt.bondingInterpretationPromotedIsFalse
        Registry.canonicalChemistryKnownInputsReferenceReceipt
  ; wetLabValidationAccepted =
      Registry.ChemistryKnownInputsReferenceReceipt.wetLabValidationAccepted
        Registry.canonicalChemistryKnownInputsReferenceReceipt
  ; wetLabValidationAcceptedIsFalse =
      Registry.ChemistryKnownInputsReferenceReceipt.wetLabValidationAcceptedIsFalse
        Registry.canonicalChemistryKnownInputsReferenceReceipt
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
  ; clinicalValidityAccepted =
      Registry.BiologyKnownInputsReferenceReceipt.clinicalValidityAccepted
        Registry.canonicalBiologyKnownInputsReferenceReceipt
  ; clinicalValidityAcceptedIsFalse =
      Registry.BiologyKnownInputsReferenceReceipt.clinicalValidityAcceptedIsFalse
        Registry.canonicalBiologyKnownInputsReferenceReceipt
  ; brainStateRecoveryPromoted =
      Registry.BiologyKnownInputsReferenceReceipt.brainStateRecoveryPromoted
        Registry.canonicalBiologyKnownInputsReferenceReceipt
  ; brainStateRecoveryPromotedIsFalse =
      Registry.BiologyKnownInputsReferenceReceipt.brainStateRecoveryPromotedIsFalse
        Registry.canonicalBiologyKnownInputsReferenceReceipt
  ; promotionProtocol =
      "consume authority policy for every measured constant or domain property"
      ∷ "consume lane adapter receipt before interpreting model law physically"
      ∷ "consume proof token or authority token before flipping a guard"
      ∷ "run validation target and update claim surface only after guard flip"
      ∷ "never infer wet-lab, clinical, causal, or brain-state validity from populated reference inputs alone"
      ∷ []
  ; validationCommand =
      "agda -i . DASHI/Promotion/ChemistryBiologyObligations.agda"
  }

canonicalChemistryBiologyObligationCountIs11 :
  ChemistryBiologyPromotionObligationIndex.obligationCount
    canonicalChemistryBiologyPromotionObligationIndex
  ≡
  suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
canonicalChemistryBiologyObligationCountIs11 =
  refl
