module DASHI.Biology.Development.DevelopmentalGenomicInverseAdapter where

open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.DevelopmentalGenomicInverseBridge as Dev

-- The existing repository spine already formalises
-- genome -> regulation -> morphogenesis -> neural differentiation -> connectome
-- and a fail-closed inverse candidate fibre.  This adapter places that spine
-- after molecular/protein/cell recovery rather than treating DNA as a snapshot.
record DevelopmentalGenomicInverseAdapter : Setω where
  field
    forwardSpine : Dev.DevelopmentalForwardSpine
    bridgeStatus : Dev.DevelopmentalBridgeStatus

    MolecularLayerRecovered : Set
    ProteinLayerRecovered   : Set
    CellLayerRecovered      : Set
    MorphogenesisLayerCompatible : Set

    molecularWitness : MolecularLayerRecovered
    proteinWitness   : ProteinLayerRecovered
    cellWitness      : CellLayerRecovered
    morphogenesisCompatibility : MorphogenesisLayerCompatible

-- Inverse use remains candidate generation: phenotype residuals may narrow a
-- regulatory/genomic fibre, but do not identify a unique gene or clinical cause.
record DevelopmentalInverseAuthorityBoundary
  (A : DevelopmentalGenomicInverseAdapter) : Setω where
  field
    InverseCandidateFibre : Set
    CalibrationEvidence  : Set
    PerturbationEvidence : Set

    candidateFibreWitness : InverseCandidateFibre

    noUniqueGeneFromPhenotypeResidual : Set
    noGenomeAsFinalBlueprint          : Set
    noClinicalPromotionWithoutAuthority : Set

record DevelopmentalInverseCompletionTarget
  (A : DevelopmentalGenomicInverseAdapter) : Setω where
  field
    missingObligation : Dev.DevelopmentalInverseFirstMissing
    ObligationDischarged : Set
    dischargeWitness : ObligationDischarged
