module DASHI.Biology.NeurochemicalGenomicExpressionBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Biology.CellDifferentiationCommunicationBridge as Cell
import DASHI.Biology.GenomeSensorimotorConnectomeBridge as Sensorimotor
import DASHI.Biology.NeurochemicalTransmissionBridge as Neurochemical
import DASHI.Physics.Closure.DevelopmentalGenomicInverseBridge as Developmental

------------------------------------------------------------------------
-- Candidate-only bridge:
-- neurochemical transmission -> gene/regulatory/expression context.
--
-- This file records only bounded candidate carriers and inverse probes.
-- It does not close genome-to-behavior, genome-to-connectome,
-- psychiatric genetics, disease causation, or clinical/therapeutic
-- authority.
------------------------------------------------------------------------

data Never : Set where

data GenomicExpressionBridgeRoute : Set where
  boundedCandidateObservationRoute :
    GenomicExpressionBridgeRoute

  genomeToBehaviorClosureRoute :
    GenomicExpressionBridgeRoute

  genomeToConnectomeClosureRoute :
    GenomicExpressionBridgeRoute

  psychiatricGeneticsRoute :
    GenomicExpressionBridgeRoute

  diseaseCausationRoute :
    GenomicExpressionBridgeRoute

  clinicalAuthorityRoute :
    GenomicExpressionBridgeRoute

  therapeuticAuthorityRoute :
    GenomicExpressionBridgeRoute

AdmissibleGenomicExpressionBridgeRoute :
  GenomicExpressionBridgeRoute → Set
AdmissibleGenomicExpressionBridgeRoute boundedCandidateObservationRoute =
  ⊤
AdmissibleGenomicExpressionBridgeRoute genomeToBehaviorClosureRoute =
  Never
AdmissibleGenomicExpressionBridgeRoute genomeToConnectomeClosureRoute =
  Never
AdmissibleGenomicExpressionBridgeRoute psychiatricGeneticsRoute =
  Never
AdmissibleGenomicExpressionBridgeRoute diseaseCausationRoute =
  Never
AdmissibleGenomicExpressionBridgeRoute clinicalAuthorityRoute =
  Never
AdmissibleGenomicExpressionBridgeRoute therapeuticAuthorityRoute =
  Never

genomeToBehaviorClosureRejected :
  AdmissibleGenomicExpressionBridgeRoute genomeToBehaviorClosureRoute →
  Never
genomeToBehaviorClosureRejected impossible = impossible

genomeToConnectomeClosureRejected :
  AdmissibleGenomicExpressionBridgeRoute genomeToConnectomeClosureRoute →
  Never
genomeToConnectomeClosureRejected impossible = impossible

psychiatricGeneticsRejected :
  AdmissibleGenomicExpressionBridgeRoute psychiatricGeneticsRoute →
  Never
psychiatricGeneticsRejected impossible = impossible

diseaseCausationRejected :
  AdmissibleGenomicExpressionBridgeRoute diseaseCausationRoute →
  Never
diseaseCausationRejected impossible = impossible

clinicalAuthorityRejected :
  AdmissibleGenomicExpressionBridgeRoute clinicalAuthorityRoute →
  Never
clinicalAuthorityRejected impossible = impossible

therapeuticAuthorityRejected :
  AdmissibleGenomicExpressionBridgeRoute therapeuticAuthorityRoute →
  Never
therapeuticAuthorityRejected impossible = impossible

record NeurochemicalGenomicExpressionBridge : Set₁ where
  field
    developmentalGenomicInverseBoundary :
      Developmental.DevelopmentalGenomicInverseBridgeBoundary

    developmentalGenomicInverseBoundaryIsCanonical :
      developmentalGenomicInverseBoundary ≡
      Developmental.canonicalDevelopmentalGenomicInverseBridgeBoundary

    genomeSensorimotorConnectomeBridge :
      Sensorimotor.GenomeSensorimotorConnectomeBridge

    genomeSensorimotorConnectomeBridgeIsCanonical :
      genomeSensorimotorConnectomeBridge ≡
      Sensorimotor.canonicalGenomeSensorimotorConnectomeBridge

    cellDifferentiationCommunicationBridge :
      Cell.CellDifferentiationCommunicationBridge

    cellDifferentiationCommunicationBridgeIsCanonical :
      cellDifferentiationCommunicationBridge ≡
      Cell.canonicalCellDifferentiationCommunicationBridge

    neurochemicalTransmissionBridge :
      Neurochemical.NeurochemicalTransmissionBridge

    neurochemicalTransmissionBridgeIsCanonical :
      neurochemicalTransmissionBridge ≡
      Neurochemical.canonicalNeurochemicalTransmissionBridge

    geneRegulatoryCandidate :
      Set

    expressionCandidate :
      Set

    proteinTargetAvailability :
      Set

    receptorDistribution :
      Set

    transporterEnzymeAvailability :
      Set

    developmentalTime :
      Set

    lineageContext :
      Set

    plasticityResidual :
      Set

    geneRegulatoryCandidateChain :
      List String

    expressionCandidateChain :
      List String

    proteinTargetAvailabilityChain :
      List String

    receptorDistributionChain :
      List String

    transporterEnzymeAvailabilityChain :
      List String

    developmentalTimeChain :
      List String

    lineageContextChain :
      List String

    plasticityResidualChain :
      List String

    observation :
      Set

    receipt :
      Set

    route :
      GenomicExpressionBridgeRoute

    routeIsBounded :
      route ≡ boundedCandidateObservationRoute

    routeAdmissible :
      AdmissibleGenomicExpressionBridgeRoute route

    genomeToBehaviorClosureClaim :
      Bool

    genomeToBehaviorClosureClaimIsFalse :
      genomeToBehaviorClosureClaim ≡ false

    genomeToConnectomeClosureClaim :
      Bool

    genomeToConnectomeClosureClaimIsFalse :
      genomeToConnectomeClosureClaim ≡ false

    psychiatricGeneticsClaim :
      Bool

    psychiatricGeneticsClaimIsFalse :
      psychiatricGeneticsClaim ≡ false

    diseaseCausationClaim :
      Bool

    diseaseCausationClaimIsFalse :
      diseaseCausationClaim ≡ false

    clinicalAuthorityClaim :
      Bool

    clinicalAuthorityClaimIsFalse :
      clinicalAuthorityClaim ≡ false

    therapeuticAuthorityClaim :
      Bool

    therapeuticAuthorityClaimIsFalse :
      therapeuticAuthorityClaim ≡ false

    bridgeReading :
      String

open NeurochemicalGenomicExpressionBridge public

canonicalNeurochemicalGenomicExpressionBridge :
  NeurochemicalGenomicExpressionBridge
canonicalNeurochemicalGenomicExpressionBridge =
  record
    { developmentalGenomicInverseBoundary =
        Developmental.canonicalDevelopmentalGenomicInverseBridgeBoundary
    ; developmentalGenomicInverseBoundaryIsCanonical =
        refl
    ; genomeSensorimotorConnectomeBridge =
        Sensorimotor.canonicalGenomeSensorimotorConnectomeBridge
    ; genomeSensorimotorConnectomeBridgeIsCanonical =
        refl
    ; cellDifferentiationCommunicationBridge =
        Cell.canonicalCellDifferentiationCommunicationBridge
    ; cellDifferentiationCommunicationBridgeIsCanonical =
        refl
    ; neurochemicalTransmissionBridge =
        Neurochemical.canonicalNeurochemicalTransmissionBridge
    ; neurochemicalTransmissionBridgeIsCanonical =
        refl
    ; geneRegulatoryCandidate =
        ⊤
    ; expressionCandidate =
        ⊤
    ; proteinTargetAvailability =
        ⊤
    ; receptorDistribution =
        ⊤
    ; transporterEnzymeAvailability =
        ⊤
    ; developmentalTime =
        ⊤
    ; lineageContext =
        ⊤
    ; plasticityResidual =
        ⊤
    ; geneRegulatoryCandidateChain =
        "candidate gene / regulatory element"
        ∷ "candidate expression timing"
        ∷ "candidate receptor distribution"
        ∷ "candidate transporter / enzyme availability"
        ∷ "candidate developmental time"
        ∷ "candidate lineage context"
        ∷ "candidate plasticity residual"
        ∷ []
    ; expressionCandidateChain =
        "candidate transcriptional state"
        ∷ "candidate translational state"
        ∷ "candidate protein-expression state"
        ∷ "candidate post-synaptic response context"
        ∷ []
    ; proteinTargetAvailabilityChain =
        "protein target availability is recorded as candidate context only"
        ∷ []
    ; receptorDistributionChain =
        "receptor distribution is recorded as candidate context only"
        ∷ []
    ; transporterEnzymeAvailabilityChain =
        "transporter / enzyme availability is recorded as candidate context only"
        ∷ []
    ; developmentalTimeChain =
        "developmental time is indexed as candidate developmental context"
        ∷ []
    ; lineageContextChain =
        "lineage context is inherited from bounded developmental observation"
        ∷ []
    ; plasticityResidualChain =
        "plasticity residual is recorded as an inverse candidate residue"
        ∷ []
    ; observation =
        ⊤
    ; receipt =
        ⊤
    ; route =
        boundedCandidateObservationRoute
    ; routeIsBounded =
        refl
    ; routeAdmissible =
        tt
    ; genomeToBehaviorClosureClaim =
        false
    ; genomeToBehaviorClosureClaimIsFalse =
        refl
    ; genomeToConnectomeClosureClaim =
        false
    ; genomeToConnectomeClosureClaimIsFalse =
        refl
    ; psychiatricGeneticsClaim =
        false
    ; psychiatricGeneticsClaimIsFalse =
        refl
    ; diseaseCausationClaim =
        false
    ; diseaseCausationClaimIsFalse =
        refl
    ; clinicalAuthorityClaim =
        false
    ; clinicalAuthorityClaimIsFalse =
        refl
    ; therapeuticAuthorityClaim =
        false
    ; therapeuticAuthorityClaimIsFalse =
        refl
    ; bridgeReading =
        "Candidate-only neurochemical-to-genomic-expression bridge: gene/regulatory and expression candidates are carried as inverse probes alongside protein target availability, receptor distribution, transporter/enzyme availability, developmental time, lineage context, and plasticity residual; genome-to-behavior closure, genome-to-connectome closure, psychiatric genetics, disease causation, and clinical or therapeutic authority remain blocked."
    }

canonicalNeurochemicalGenomicExpressionBridgeRouteBounded :
  NeurochemicalGenomicExpressionBridge.route
    canonicalNeurochemicalGenomicExpressionBridge
  ≡
  boundedCandidateObservationRoute
canonicalNeurochemicalGenomicExpressionBridgeRouteBounded =
  refl

canonicalNeurochemicalGenomicExpressionBridgeGenomeToBehaviorClosureFalse :
  NeurochemicalGenomicExpressionBridge.genomeToBehaviorClosureClaim
    canonicalNeurochemicalGenomicExpressionBridge
  ≡
  false
canonicalNeurochemicalGenomicExpressionBridgeGenomeToBehaviorClosureFalse =
  refl

canonicalNeurochemicalGenomicExpressionBridgeGenomeToConnectomeClosureFalse :
  NeurochemicalGenomicExpressionBridge.genomeToConnectomeClosureClaim
    canonicalNeurochemicalGenomicExpressionBridge
  ≡
  false
canonicalNeurochemicalGenomicExpressionBridgeGenomeToConnectomeClosureFalse =
  refl

canonicalNeurochemicalGenomicExpressionBridgePsychiatricGeneticsFalse :
  NeurochemicalGenomicExpressionBridge.psychiatricGeneticsClaim
    canonicalNeurochemicalGenomicExpressionBridge
  ≡
  false
canonicalNeurochemicalGenomicExpressionBridgePsychiatricGeneticsFalse =
  refl

canonicalNeurochemicalGenomicExpressionBridgeDiseaseCausationFalse :
  NeurochemicalGenomicExpressionBridge.diseaseCausationClaim
    canonicalNeurochemicalGenomicExpressionBridge
  ≡
  false
canonicalNeurochemicalGenomicExpressionBridgeDiseaseCausationFalse =
  refl

canonicalNeurochemicalGenomicExpressionBridgeClinicalAuthorityFalse :
  NeurochemicalGenomicExpressionBridge.clinicalAuthorityClaim
    canonicalNeurochemicalGenomicExpressionBridge
  ≡
  false
canonicalNeurochemicalGenomicExpressionBridgeClinicalAuthorityFalse =
  refl

canonicalNeurochemicalGenomicExpressionBridgeTherapeuticAuthorityFalse :
  NeurochemicalGenomicExpressionBridge.therapeuticAuthorityClaim
    canonicalNeurochemicalGenomicExpressionBridge
  ≡
  false
canonicalNeurochemicalGenomicExpressionBridgeTherapeuticAuthorityFalse =
  refl
