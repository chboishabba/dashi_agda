module DASHI.Promotion.ChemistryQuantitativeAdapter where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

open import DASHI.Constants.Registry as Registry
open import DASHI.Promotion.ChemistryBiologyObligations as ChemBio

------------------------------------------------------------------------
-- Quantitative chemistry adapter surface.
--
-- This module narrows the physical-chemistry/spectroscopy/bonding/wet-lab
-- blockers into typed quantitative carriers.  It records exact reference
-- slots, symbolic law carriers, authority/proof-token requirements, and
-- fail-closed promotion guards.  It does not promote physical chemistry,
-- spectroscopy, bonding interpretation, or wet-lab validation.

data QuantitativeAdapterLane : Set where
  stoichiometryLane : QuantitativeAdapterLane
  idealGasLane : QuantitativeAdapterLane
  massActionLane : QuantitativeAdapterLane
  beerLambertLane : QuantitativeAdapterLane
  nernstLane : QuantitativeAdapterLane
  spectroscopyLane : QuantitativeAdapterLane
  bondingLane : QuantitativeAdapterLane
  wetLabLane : QuantitativeAdapterLane

data QuantitativeRequirementKind : Set where
  exactReferenceSlotRequired : QuantitativeRequirementKind
  symbolicLawCarrierRequired : QuantitativeRequirementKind
  measuredAuthorityRequired : QuantitativeRequirementKind
  observableAdapterRequired : QuantitativeRequirementKind
  preservationTokenRequired : QuantitativeRequirementKind
  protocolProvenanceRequired : QuantitativeRequirementKind
  replicationEvidenceRequired : QuantitativeRequirementKind

data AdapterClaimStatus : Set where
  adapterPopulatedNonPromoting : AdapterClaimStatus

record QuantitativeRequirement : Set₁ where
  field
    requirementLabel : String
    lane : QuantitativeAdapterLane
    requirementKind : QuantitativeRequirementKind
    sourceSlotOrToken : String
    consumingCarrier : String
    dischargeSurface : String
    blocksGuard : String

open QuantitativeRequirement public

mkRequirement :
  String →
  QuantitativeAdapterLane →
  QuantitativeRequirementKind →
  String →
  String →
  String →
  String →
  QuantitativeRequirement
mkRequirement label lane kind source consumer discharge guard =
  record
    { requirementLabel = label
    ; lane = lane
    ; requirementKind = kind
    ; sourceSlotOrToken = source
    ; consumingCarrier = consumer
    ; dischargeSurface = discharge
    ; blocksGuard = guard
    }

requirementCount : List QuantitativeRequirement → Nat
requirementCount [] = zero
requirementCount (_ ∷ xs) = suc (requirementCount xs)

record StoichiometryMoleculeCountAdapter : Set₁ where
  field
    adapterLabel : String
    avogadroSlotLabel : String
    avogadroSymbol : String
    avogadroAuthorityClass : String
    amountCarrier : String
    moleculeCountCarrier : String
    exactMoleculeCountExpression : String
    balancedReactionCarrier : String
    conservationTarget : String
    exactReferenceOnly : Bool
    exactReferenceOnlyIsTrue : exactReferenceOnly ≡ true
    wetLabYieldPromoted : Bool
    wetLabYieldPromotedIsFalse : wetLabYieldPromoted ≡ false

open StoichiometryMoleculeCountAdapter public

record SymbolicLawCarrier : Set₁ where
  field
    lawLabel : String
    registryLawSlot : String
    symbolicForm : String
    variableCarrier : List String
    exactReferenceInputs : List String
    measuredAuthorityInputs : List String
    validityRegimeRequired : String
    observableTarget : String
    modelLawPromoted : Bool
    modelLawPromotedIsFalse : modelLawPromoted ≡ false

open SymbolicLawCarrier public

mkSymbolicLawCarrier :
  String →
  String →
  String →
  List String →
  List String →
  List String →
  String →
  String →
  SymbolicLawCarrier
mkSymbolicLawCarrier label slot form variables exact measured regime target =
  record
    { lawLabel = label
    ; registryLawSlot = slot
    ; symbolicForm = form
    ; variableCarrier = variables
    ; exactReferenceInputs = exact
    ; measuredAuthorityInputs = measured
    ; validityRegimeRequired = regime
    ; observableTarget = target
    ; modelLawPromoted = false
    ; modelLawPromotedIsFalse = refl
    }

lawCarrierCount : List SymbolicLawCarrier → Nat
lawCarrierCount [] = zero
lawCarrierCount (_ ∷ xs) = suc (lawCarrierCount xs)

record SpectroscopyObservableAdapter : Set₁ where
  field
    adapterLabel : String
    hSlotLabel : String
    cSlotLabel : String
    hbarSlotLabel : String
    spectralAuthoritySlot : String
    transitionEnergyCarrier : String
    frequencyCarrier : String
    wavelengthCarrier : String
    hFrequencyExpression : String
    hcOverLambdaExpression : String
    hbarAngularFrequencyExpression : String
    instrumentResponseCarrier : String
    measuredSpectrumChecksumRequired : Bool
    measuredSpectrumChecksumRequiredIsTrue :
      measuredSpectrumChecksumRequired ≡ true
    spectroscopyPromoted : Bool
    spectroscopyPromotedIsFalse : spectroscopyPromoted ≡ false

open SpectroscopyObservableAdapter public

record BondingInterpretationPreservationToken : Set₁ where
  field
    tokenLabel : String
    sourceCarrier : String
    targetInterpretation : String
    preservedStructure : List String
    conventionBoundary : List String
    requiredProofToken : String
    tokenAccepted : Bool
    tokenAcceptedIsFalse : tokenAccepted ≡ false
    bondingInterpretationPromoted : Bool
    bondingInterpretationPromotedIsFalse :
      bondingInterpretationPromoted ≡ false

open BondingInterpretationPreservationToken public

record WetLabProtocolReplicationReceipt : Set₁ where
  field
    protocolIdField : String
    sampleProvenanceField : String
    reagentLotField : String
    instrumentCalibrationField : String
    environmentMetadataField : String
    operatorOrAutomationField : String
    rawDataChecksumField : String
    analysisPipelineChecksumField : String
    replicateSetField : String
    acceptanceCriterionField : String
    independentReplicationField : String
    protocolProvenanceComplete : Bool
    protocolProvenanceCompleteIsFalse :
      protocolProvenanceComplete ≡ false
    replicationAccepted : Bool
    replicationAcceptedIsFalse : replicationAccepted ≡ false
    wetLabValidationAccepted : Bool
    wetLabValidationAcceptedIsFalse :
      wetLabValidationAccepted ≡ false

open WetLabProtocolReplicationReceipt public

record ChemistryQuantitativeAdapter : Set₁ where
  field
    registryReceipt :
      Registry.ChemistryKnownInputsReferenceReceipt
    chemistryBiologyObligationIndex :
      ChemBio.ChemistryBiologyPromotionObligationIndex
    stoichiometryAdapter :
      StoichiometryMoleculeCountAdapter
    symbolicLawCarriers :
      List SymbolicLawCarrier
    symbolicLawCarrierCount :
      Nat
    symbolicLawCarrierCountMatches :
      symbolicLawCarrierCount ≡ lawCarrierCount symbolicLawCarriers
    spectroscopyObservableAdapter :
      SpectroscopyObservableAdapter
    bondingPreservationToken :
      BondingInterpretationPreservationToken
    wetLabProtocolReplication :
      WetLabProtocolReplicationReceipt
    requirements :
      List QuantitativeRequirement
    requirementCountField :
      Nat
    requirementCountMatches :
      requirementCountField ≡ requirementCount requirements
    status :
      AdapterClaimStatus
    physicalChemistryPromoted :
      Bool
    physicalChemistryPromotedIsFalse :
      physicalChemistryPromoted ≡ false
    spectroscopyPromoted :
      Bool
    spectroscopyPromotedIsFalse :
      spectroscopyPromoted ≡ false
    bondingInterpretationPromoted :
      Bool
    bondingInterpretationPromotedIsFalse :
      bondingInterpretationPromoted ≡ false
    wetLabValidationAccepted :
      Bool
    wetLabValidationAcceptedIsFalse :
      wetLabValidationAccepted ≡ false
    validationCommand :
      String

open ChemistryQuantitativeAdapter public

canonicalStoichiometryMoleculeCountAdapter :
  StoichiometryMoleculeCountAdapter
canonicalStoichiometryMoleculeCountAdapter = record
  { adapterLabel =
      "exact stoichiometry molecule-count adapter"
  ; avogadroSlotLabel =
      "Avogadro constant"
  ; avogadroSymbol =
      "N_A"
  ; avogadroAuthorityClass =
      "exactSIDefiningConstant"
  ; amountCarrier =
      "amount-of-substance carrier n with unit mol"
  ; moleculeCountCarrier =
      "molecule-count carrier N"
  ; exactMoleculeCountExpression =
      "N = n * N_A"
  ; balancedReactionCarrier =
      "integer stoichiometric coefficient vector over species"
  ; conservationTarget =
      "atom-count and charge-count conservation for balanced reactions"
  ; exactReferenceOnly =
      true
  ; exactReferenceOnlyIsTrue =
      refl
  ; wetLabYieldPromoted =
      false
  ; wetLabYieldPromotedIsFalse =
      refl
  }

canonicalSymbolicLawCarriers : List SymbolicLawCarrier
canonicalSymbolicLawCarriers =
  mkSymbolicLawCarrier
    "ideal gas law carrier"
    "ideal gas law"
    "p V = n R T"
    ( "pressure p"
    ∷ "volume V"
    ∷ "amount n"
    ∷ "temperature T"
    ∷ []
    )
    ( "R : exact derived expression N_A k_B"
    ∷ "N_A : exact SI Avogadro constant"
    ∷ "k_B : exact SI Boltzmann constant"
    ∷ []
    )
    ( "equation-of-state authority"
    ∷ "pressure/volume/temperature calibration"
    ∷ []
    )
    "dilute gas or explicitly supplied EOS-validity regime"
    "state-variable prediction/comparison adapter"
  ∷ mkSymbolicLawCarrier
    "law of mass action carrier"
    "law of mass action"
    "rate or equilibrium target as product of activities/concentrations"
    ( "stoichiometric coefficients"
    ∷ "activity or concentration vector"
    ∷ "rate or equilibrium constant"
    ∷ "temperature"
    ∷ []
    )
    ( "N_A : exact SI Avogadro constant for concentration/count bridge"
    ∷ "R : exact derived expression where thermodynamic form consumes it"
    ∷ []
    )
    ( "activity model authority"
    ∷ "rate/equilibrium constant authority"
    ∷ "temperature calibration"
    ∷ []
    )
    "specified solvent, phase, ionic strength, and temperature regime"
    "reaction-network kinetics or equilibrium observable"
  ∷ mkSymbolicLawCarrier
    "Beer-Lambert law carrier"
    "Beer-Lambert law"
    "A = epsilon l c"
    ( "absorbance A"
    ∷ "molar absorptivity epsilon"
    ∷ "optical path length l"
    ∷ "concentration c"
    ∷ []
    )
    ( "N_A : exact SI Avogadro constant for concentration/count bridge"
    ∷ "c : exact SI speed of light for spectral unit conversion"
    ∷ []
    )
    ( "molar absorptivity authority"
    ∷ "instrument calibration"
    ∷ "sample matrix and wavelength authority"
    ∷ []
    )
    "linear absorbance regime with declared wavelength and sample matrix"
    "spectrophotometer absorbance observable"
  ∷ mkSymbolicLawCarrier
    "Nernst equation carrier"
    "Nernst equation"
    "E = E0 - (R T / z F) ln Q"
    ( "electrode potential E"
    ∷ "standard potential E0"
    ∷ "temperature T"
    ∷ "charge number z"
    ∷ "reaction quotient Q"
    ∷ []
    )
    ( "R : exact derived expression N_A k_B"
    ∷ "F : exact derived expression N_A e"
    ∷ "e : exact SI elementary charge"
    ∷ []
    )
    ( "standard-potential authority"
    ∷ "activity model authority"
    ∷ "electrode or membrane calibration"
    ∷ []
    )
    "declared electrochemical convention, activities, and temperature regime"
    "electrochemical or membrane-potential observable"
  ∷ []

canonicalSpectroscopyObservableAdapter :
  SpectroscopyObservableAdapter
canonicalSpectroscopyObservableAdapter = record
  { adapterLabel =
      "spectroscopy observable adapter"
  ; hSlotLabel =
      "Planck constant h"
  ; cSlotLabel =
      "speed of light in vacuum c"
  ; hbarSlotLabel =
      "reduced Planck constant hbar"
  ; spectralAuthoritySlot =
      "NIST spectral line or Chemistry WebBook measured spectrum authority"
  ; transitionEnergyCarrier =
      "transition energy Delta E"
  ; frequencyCarrier =
      "frequency nu"
  ; wavelengthCarrier =
      "wavelength lambda"
  ; hFrequencyExpression =
      "Delta E = h nu"
  ; hcOverLambdaExpression =
      "Delta E = h c / lambda"
  ; hbarAngularFrequencyExpression =
      "Delta E = hbar omega"
  ; instrumentResponseCarrier =
      "instrument response, line shape, resolution, and calibration carrier"
  ; measuredSpectrumChecksumRequired =
      true
  ; measuredSpectrumChecksumRequiredIsTrue =
      refl
  ; spectroscopyPromoted =
      false
  ; spectroscopyPromotedIsFalse =
      refl
  }

canonicalBondingInterpretationPreservationToken :
  BondingInterpretationPreservationToken
canonicalBondingInterpretationPreservationToken = record
  { tokenLabel =
      "bonding interpretation preservation token"
  ; sourceCarrier =
      "Hamiltonian/supervoxel/electron-density carrier"
  ; targetInterpretation =
      "bond graph, orbital, electron-density, or energy-partition semantics"
  ; preservedStructure =
      "atom incidence"
      ∷ "charge and multiplicity convention"
      ∷ "energy/order or density threshold convention"
      ∷ "basis/gauge/convention boundary"
      ∷ []
  ; conventionBoundary =
      "bonding decompositions are not unique without declared convention"
      ∷ "basis-dependent orbital statements require explicit basis boundary"
      ∷ "density or energy-partition claims require threshold policy"
      ∷ []
  ; requiredProofToken =
      "BondingInterpretationPreservation theorem or accepted authority token"
  ; tokenAccepted =
      false
  ; tokenAcceptedIsFalse =
      refl
  ; bondingInterpretationPromoted =
      false
  ; bondingInterpretationPromotedIsFalse =
      refl
  }

canonicalWetLabProtocolReplicationReceipt :
  WetLabProtocolReplicationReceipt
canonicalWetLabProtocolReplicationReceipt = record
  { protocolIdField =
      "protocolId"
  ; sampleProvenanceField =
      "sampleProvenance"
  ; reagentLotField =
      "reagentLot"
  ; instrumentCalibrationField =
      "instrumentCalibration"
  ; environmentMetadataField =
      "temperaturePressureHumidityAndMatrixMetadata"
  ; operatorOrAutomationField =
      "operatorOrAutomationRunId"
  ; rawDataChecksumField =
      "rawDataChecksum"
  ; analysisPipelineChecksumField =
      "analysisPipelineChecksum"
  ; replicateSetField =
      "replicateSet"
  ; acceptanceCriterionField =
      "acceptanceCriterion"
  ; independentReplicationField =
      "independentReplicationReceipt"
  ; protocolProvenanceComplete =
      false
  ; protocolProvenanceCompleteIsFalse =
      refl
  ; replicationAccepted =
      false
  ; replicationAcceptedIsFalse =
      refl
  ; wetLabValidationAccepted =
      false
  ; wetLabValidationAcceptedIsFalse =
      refl
  }

canonicalQuantitativeRequirements : List QuantitativeRequirement
canonicalQuantitativeRequirements =
  mkRequirement
    "Avogadro exact molecule-count bridge"
    stoichiometryLane
    exactReferenceSlotRequired
    "Registry exact SI slot: Avogadro constant / N_A"
    "StoichiometryMoleculeCountAdapter.exactMoleculeCountExpression"
    "DASHI.Promotion.ChemistryQuantitativeAdapter"
    "physicalChemistryPromoted"
  ∷ mkRequirement
    "balanced reaction conservation carrier"
    stoichiometryLane
    symbolicLawCarrierRequired
    "Registry chemistry law slot: stoichiometric conservation"
    "integer stoichiometric coefficient vector"
    "AtomicChemistryRecoveryTheorem or chemistry handoff diagnostic"
    "physicalChemistryPromoted"
  ∷ mkRequirement
    "ideal gas symbolic carrier"
    idealGasLane
    symbolicLawCarrierRequired
    "Registry chemistry law slot: ideal gas law"
    "SymbolicLawCarrier p V = n R T"
    "equation-of-state authority plus validity-regime adapter"
    "physicalChemistryPromoted"
  ∷ mkRequirement
    "mass action symbolic carrier"
    massActionLane
    symbolicLawCarrierRequired
    "Registry chemistry law slot: law of mass action"
    "SymbolicLawCarrier activity/concentration product target"
    "reaction-network calibration and activity-model adapter"
    "physicalChemistryPromoted"
  ∷ mkRequirement
    "Beer-Lambert symbolic carrier"
    beerLambertLane
    symbolicLawCarrierRequired
    "Registry chemistry law slot: Beer-Lambert law"
    "SymbolicLawCarrier A = epsilon l c"
    "instrument calibration and molar-absorptivity authority"
    "spectroscopyPromoted"
  ∷ mkRequirement
    "Nernst symbolic carrier"
    nernstLane
    symbolicLawCarrierRequired
    "Registry chemistry law slot: Nernst equation"
    "SymbolicLawCarrier E = E0 - (R T / z F) ln Q"
    "standard potential, activity, and electrode authority"
    "physicalChemistryPromoted"
  ∷ mkRequirement
    "spectroscopy exact h c hbar references"
    spectroscopyLane
    exactReferenceSlotRequired
    "Registry exact slots: h, c, hbar"
    "SpectroscopyObservableAdapter energy/frequency/wavelength formulas"
    "canonicalChemistryKnownInputsReferenceReceipt"
    "spectroscopyPromoted"
  ∷ mkRequirement
    "measured spectral authority"
    spectroscopyLane
    measuredAuthorityRequired
    "NIST spectral line or Chemistry WebBook spectrum authority"
    "SpectroscopyObservableAdapter.spectralAuthoritySlot"
    "source URI, version, checksum, access date, uncertainty, and units"
    "spectroscopyPromoted"
  ∷ mkRequirement
    "instrument response observable adapter"
    spectroscopyLane
    observableAdapterRequired
    "instrument calibration authority"
    "line shape, resolution, baseline, and response carrier"
    "comparison residual and tolerance law"
    "spectroscopyPromoted"
  ∷ mkRequirement
    "bonding preservation token"
    bondingLane
    preservationTokenRequired
    "BondingInterpretationPreservation theorem or authority token"
    "BondingInterpretationPreservationToken"
    "basis/gauge/convention-aware preservation proof"
    "bondingInterpretationPromoted"
  ∷ mkRequirement
    "wet-lab protocol provenance"
    wetLabLane
    protocolProvenanceRequired
    "protocol/sample/reagent/instrument/environment/raw-data fields"
    "WetLabProtocolReplicationReceipt"
    "complete protocol provenance and checksum receipt"
    "wetLabValidationAccepted"
  ∷ mkRequirement
    "wet-lab independent replication"
    wetLabLane
    replicationEvidenceRequired
    "replicate set and independent replication receipt"
    "WetLabProtocolReplicationReceipt"
    "accepted replication criterion and holdout/replicate evidence"
    "wetLabValidationAccepted"
  ∷ []

canonicalChemistryQuantitativeAdapter :
  ChemistryQuantitativeAdapter
canonicalChemistryQuantitativeAdapter = record
  { registryReceipt =
      Registry.canonicalChemistryKnownInputsReferenceReceipt
  ; chemistryBiologyObligationIndex =
      ChemBio.canonicalChemistryBiologyPromotionObligationIndex
  ; stoichiometryAdapter =
      canonicalStoichiometryMoleculeCountAdapter
  ; symbolicLawCarriers =
      canonicalSymbolicLawCarriers
  ; symbolicLawCarrierCount =
      lawCarrierCount canonicalSymbolicLawCarriers
  ; symbolicLawCarrierCountMatches =
      refl
  ; spectroscopyObservableAdapter =
      canonicalSpectroscopyObservableAdapter
  ; bondingPreservationToken =
      canonicalBondingInterpretationPreservationToken
  ; wetLabProtocolReplication =
      canonicalWetLabProtocolReplicationReceipt
  ; requirements =
      canonicalQuantitativeRequirements
  ; requirementCountField =
      requirementCount canonicalQuantitativeRequirements
  ; requirementCountMatches =
      refl
  ; status =
      adapterPopulatedNonPromoting
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
  ; validationCommand =
      "agda -i . DASHI/Promotion/ChemistryQuantitativeAdapter.agda"
  }

canonicalSymbolicLawCarrierCountIs4 :
  ChemistryQuantitativeAdapter.symbolicLawCarrierCount
    canonicalChemistryQuantitativeAdapter
  ≡
  suc (suc (suc (suc zero)))
canonicalSymbolicLawCarrierCountIs4 =
  refl

canonicalQuantitativeRequirementCountIs12 :
  ChemistryQuantitativeAdapter.requirementCountField
    canonicalChemistryQuantitativeAdapter
  ≡
  suc
    (suc
      (suc
        (suc
          (suc
            (suc
              (suc
                (suc
                  (suc
                    (suc
                      (suc
                        (suc zero)))))))))))
canonicalQuantitativeRequirementCountIs12 =
  refl

chemistryQuantitativeAdapterPhysicalChemistryStillFalse :
  ChemistryQuantitativeAdapter.physicalChemistryPromoted
    canonicalChemistryQuantitativeAdapter
  ≡ false
chemistryQuantitativeAdapterPhysicalChemistryStillFalse =
  refl

chemistryQuantitativeAdapterSpectroscopyStillFalse :
  ChemistryQuantitativeAdapter.spectroscopyPromoted
    canonicalChemistryQuantitativeAdapter
  ≡ false
chemistryQuantitativeAdapterSpectroscopyStillFalse =
  refl

chemistryQuantitativeAdapterBondingStillFalse :
  ChemistryQuantitativeAdapter.bondingInterpretationPromoted
    canonicalChemistryQuantitativeAdapter
  ≡ false
chemistryQuantitativeAdapterBondingStillFalse =
  refl

chemistryQuantitativeAdapterWetLabStillFalse :
  ChemistryQuantitativeAdapter.wetLabValidationAccepted
    canonicalChemistryQuantitativeAdapter
  ≡ false
chemistryQuantitativeAdapterWetLabStillFalse =
  refl
