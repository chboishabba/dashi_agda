module DASHI.Biology.ChegenWalshUndermethylationBidiResidualExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.OneCarbonHistamineMethylationNetworkExact as Network
import DASHI.Biology.ChegenWalshUndermethylationAssertionConeExact as Cone

------------------------------------------------------------------------
-- BIDI inverse-problem owner.
--
-- The reel informally maps a phenotype fingerprint back to one latent
-- "undermethylation" state.  This module retains the inverse as a set of
-- compatible candidate explanations plus unresolved residuals.
------------------------------------------------------------------------

data ObservationKind : Set where
  traitObservation : ObservationKind
  wholeBloodHistamineObservation : ObservationKind
  samSahObservation : ObservationKind
  genotypeObservation : ObservationKind
  methylationAssayObservation : ObservationKind
  enzymeActivityObservation : ObservationKind

record Observation : Set where
  constructor observation
  field
    kind : ObservationKind
    valueReference : String
    assayOrElicitationReference : String
    timingReference : String
    compartmentReference : String

open Observation public

data CandidateExplanation : Set where
  alteredOneCarbonFlux : CandidateExplanation
  alteredHNMTFlux : CandidateExplanation
  alteredCOMTFlux : CandidateExplanation
  alteredDNMTFlux : CandidateExplanation
  alteredHistamineProductionOrRelease : CandidateExplanation
  alteredPeripheralHistamineClearance : CandidateExplanation
  mixedMechanism : CandidateExplanation
  nonBiochemicalTraitCovariation : CandidateExplanation
  unresolvedCandidate : CandidateExplanation

data ResidualKind : Set where
  tissueCompartmentResidual : ResidualKind
  timingResidual : ResidualKind
  dietNutrientResidual : ResidualKind
  medicationResidual : ResidualKind
  inflammatoryMastCellResidual : ResidualKind
  geneticBackgroundResidual : ResidualKind
  assayCalibrationResidual : ResidualKind
  psychosocialCovariateResidual : ResidualKind
  unmeasuredMechanismResidual : ResidualKind

record InverseEnvelope : Set where
  constructor inverseEnvelope
  field
    observations : List Observation
    compatibleExplanations : List CandidateExplanation
    unresolvedResiduals : List ResidualKind
    uniqueMechanismIdentified : Bool
    uniqueMechanismIdentifiedIsFalse :
      uniqueMechanismIdentified ≡ false
    diagnosisImported : Bool
    diagnosisImportedIsFalse :
      diagnosisImported ≡ false
    treatmentImported : Bool
    treatmentImportedIsFalse :
      treatmentImported ≡ false
    reading : String

open InverseEnvelope public

reelFingerprintObservation : Observation
reelFingerprintObservation =
  observation
    traitObservation
    "Reel 19 phenotype cluster"
    "user-supplied transcript attributed to @danielchegenp"
    "cross-sectional / unspecified"
    "person-level reported traits; not a molecular compartment"

canonicalReelFingerprintInverseEnvelope : InverseEnvelope
canonicalReelFingerprintInverseEnvelope =
  inverseEnvelope
    (reelFingerprintObservation ∷ [])
    ( alteredOneCarbonFlux
    ∷ alteredHNMTFlux
    ∷ alteredHistamineProductionOrRelease
    ∷ alteredPeripheralHistamineClearance
    ∷ mixedMechanism
    ∷ nonBiochemicalTraitCovariation
    ∷ unresolvedCandidate
    ∷ [])
    ( tissueCompartmentResidual
    ∷ timingResidual
    ∷ dietNutrientResidual
    ∷ medicationResidual
    ∷ inflammatoryMastCellResidual
    ∷ geneticBackgroundResidual
    ∷ assayCalibrationResidual
    ∷ psychosocialCovariateResidual
    ∷ unmeasuredMechanismResidual
    ∷ [])
    false refl
    false refl
    false refl
    "A phenotype fingerprint can constrain candidate explanations only after calibrated observation models are supplied; it does not invert uniquely to a biochemical state."

------------------------------------------------------------------------
-- Non-identifiability theorems.
------------------------------------------------------------------------

data SameFingerprintImpliesSameMechanism : Set where
data SameMechanismImpliesSameFingerprint : Set where
data CompatibleCandidateMeansCausalTruth : Set where
data InverseEnvelopeMeansDiagnosis : Set where

sameFingerprintDoesNotForceSameMechanism :
  SameFingerprintImpliesSameMechanism → ⊥
sameFingerprintDoesNotForceSameMechanism ()

sameMechanismDoesNotForceSameFingerprint :
  SameMechanismImpliesSameFingerprint → ⊥
sameMechanismDoesNotForceSameFingerprint ()

compatibilityDoesNotPromoteCausalTruth :
  CompatibleCandidateMeansCausalTruth → ⊥
compatibilityDoesNotPromoteCausalTruth ()

inverseEnvelopeDoesNotPromoteDiagnosis :
  InverseEnvelopeMeansDiagnosis → ⊥
inverseEnvelopeDoesNotPromoteDiagnosis ()

------------------------------------------------------------------------
-- Experimental closure frontier.
------------------------------------------------------------------------

record ClosureFrontier : Set where
  constructor closureFrontier
  field
    phenotypeProtocol : String
    histamineProtocol : String
    oneCarbonProtocol : String
    methyltransferaseProtocol : String
    genotypeProtocol : String
    longitudinalProtocol : String
    interventionProtocol : String
    externalReplicationProtocol : String

canonicalClosureFrontier : ClosureFrontier
canonicalClosureFrontier =
  closureFrontier
    "pre-specified quantitative phenotype measures rather than post-hoc trait matching"
    "assay, compartment, timing and histamine-production/clearance context recorded"
    "direct methionine-cycle / SAM-SAH measurements with specimen and timing preserved"
    "enzyme- or pathway-specific activity/flux measurements for HNMT/COMT/DNMT-relevant lanes"
    "genotype retained as one causal input rather than a phenotype identity"
    "within-person repeated measurements to test whether biochemical and phenotype variation co-move"
    "pre-specified intervention with comparator, fidelity, safety and target engagement"
    "independent cohort replication of any proposed latent subtype and its predictive value"
