module Ontology.BrainDNA.BrainWholeChainIntegrationLaw where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; _+_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Vec using (Vec)

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
import Ontology.Brain.BrainRegionAutomatonSurface as Region
import Ontology.BrainDNA.BrainThemeConnectorSurface as Theme
import Ontology.BrainDNA.BrainDnaRepresentationMap as Map
import Ontology.BrainDNA.BrainRepresentationTransportLaws as Transport
import Ontology.BrainDNA.BrainRepresentationIntegratedLaws as RepLaw
import Ontology.BrainDNA.BrainThemeIntegratedLaws as ThemeLaw
import Ontology.BrainDNA.BrainCrossoverIntegrationLaws as Crossover
import Ontology.BrainDNA.BrainCodecPayloadRecoveryBridge as Payload
import Ontology.BrainDNA.BrainChemistryCodecConsumer as Consumer
import Ontology.BrainDNA.BrainAtomicChemistryHandoff as Handoff
import Ontology.DNA.StreamingEncoderSurface as SES
import Ontology.DNA.SynthesisSequencingRiskSurface as Risk
import Ontology.DNA.SynthesisSequencingIntegratedRealismLaws as Realism
open import Ontology.DNA.Supervoxel4Adic using (Base)
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)

------------------------------------------------------------------------
-- Whole-chain integration law for the bounded Brain-DNA lane.
--
-- This module deliberately remains non-physics-promoting and non-wet-lab
-- claiming. It packages the already-landed connector, representation,
-- crossover, checksum, and synthesis/sequencing realism owners into one
-- typed whole-chain profile and records only exact bounded coherence.

record theta_i (n : Nat) : Set where
  constructor mkTheta_i
  field
    state : BrainState n
    region : Region.BrainRegion

C_atom : Nat → Set
C_atom = Handoff.BrainAtomicChemistryHandoffProfile

I_chain : ∀ {n} → theta_i n → C_atom n
I_chain θ =
  Handoff.brainAtomicChemistryHandoffProfileOf (theta_i.state θ)

record SemanticChecksumPair : Set where
  constructor semanticChecksumPair
  field
    thermo : Nat
    hamiltonian : Nat

zeroChecksum : SemanticChecksumPair
zeroChecksum = semanticChecksumPair zero zero

_checksumCompose_ : SemanticChecksumPair → SemanticChecksumPair → SemanticChecksumPair
left checksumCompose right =
  semanticChecksumPair
    (SemanticChecksumPair.thermo left + SemanticChecksumPair.thermo right)
    (SemanticChecksumPair.hamiltonian left + SemanticChecksumPair.hamiltonian right)

infixl 6 _checksumCompose_

chainCarrierChecksum : ∀ {n} → theta_i n → SemanticChecksumPair
chainCarrierChecksum θ =
  semanticChecksumPair
    (Consumer.BrainChemistryCodecConsumerProfile.thermoChecksum
      (Consumer.brainChemistryCodecConsumerProfile (theta_i.state θ)))
    (Handoff.BrainAtomicChemistryHandoffProfile.hamiltonian (I_chain θ))

themeHopChecksum : ∀ {n} → theta_i n → SemanticChecksumPair
themeHopChecksum θ = zeroChecksum

representationHopChecksum : ∀ {n} → theta_i n → SemanticChecksumPair
representationHopChecksum θ = zeroChecksum

transportHopChecksum : ∀ {n} → theta_i n → SemanticChecksumPair
transportHopChecksum θ = zeroChecksum

crossoverHopChecksum : ∀ {n} → theta_i n → SemanticChecksumPair
crossoverHopChecksum θ = zeroChecksum

atomicHopChecksum : ∀ {n} → theta_i n → SemanticChecksumPair
atomicHopChecksum = chainCarrierChecksum

composeHopChecksums : ∀ {n} → theta_i n → SemanticChecksumPair
composeHopChecksums θ =
  (themeHopChecksum θ)
    checksumCompose (representationHopChecksum θ)
    checksumCompose (transportHopChecksum θ)
    checksumCompose (crossoverHopChecksum θ)
    checksumCompose (atomicHopChecksum θ)

wholeChainSemanticChecksumComposes :
  ∀ {n} (θ : theta_i n) →
  chainCarrierChecksum θ ≡ composeHopChecksums θ
wholeChainSemanticChecksumComposes θ = refl

wholeChainChecksumMatchesStreamingCarrier :
  ∀ {n} (θ : theta_i n) →
  chainCarrierChecksum θ
    ≡
  semanticChecksumPair
    (SES.EncoderState.thermoState
      (SES.stateOf
        (Payload.BrainCodecPayloadRecoveryProfile.sourcePayload
          (Payload.codecPayloadRecoveryProfileOf (theta_i.state θ)))))
    (Handoff.BrainAtomicChemistryHandoffProfile.hamiltonian (I_chain θ))
wholeChainChecksumMatchesStreamingCarrier θ = refl

rho_min : Nat
rho_min =
  Risk.SynthesisSequencingRiskProfile.recoveryBoundary
    (Risk.SynthesisSequencingRiskSurface.profile
      Risk.synthesisSequencingRiskSurface)

record O_phys (n : Nat) : Set₁ where
  constructor o_phys
  field
    atomCarrier : C_atom n
    riskSurface : Risk.SynthesisSequencingRiskSurface
    realismLawSurface : Realism.SynthesisSequencingIntegratedRealismLawSurface
    certifiedRhoMin : Nat

R_real : ∀ {n} → theta_i n → O_phys n
R_real θ =
  o_phys
    (I_chain θ)
    Risk.synthesisSequencingRiskSurface
    Realism.synthesisSequencingIntegratedRealismLawSurface
    rho_min

R_real_closes_I_chain :
  ∀ {n} (θ : theta_i n) →
  O_phys.atomCarrier (R_real θ) ≡ I_chain θ
R_real_closes_I_chain θ = refl

rhoMinCertifiedFromRiskSurface :
  rho_min
    ≡
  Risk.SynthesisSequencingRiskProfile.recoveryBoundary
    (Risk.SynthesisSequencingRiskSurface.profile
      Risk.synthesisSequencingRiskSurface)
rhoMinCertifiedFromRiskSurface = refl

R_real_rho_min_floor :
  ∀ {n} (θ : theta_i n) →
  O_phys.certifiedRhoMin (R_real θ) ≡ rho_min
R_real_rho_min_floor θ = refl

R_real_floorBoundedByRiskRecovery :
  ∀ {n} (θ : theta_i n) →
  O_phys.certifiedRhoMin (R_real θ)
    ≡
  Risk.SynthesisSequencingRiskProfile.recoveryBoundary
    (Risk.SynthesisSequencingRiskSurface.profile
      Risk.synthesisSequencingRiskSurface)
R_real_floorBoundedByRiskRecovery θ = refl

record BrainWholeChainIntegrationProfile (n : Nat) : Setω where
  constructor brainWholeChainIntegrationProfile
  field
    theta : theta_i n
    themeProfile : Theme.BrainThemeProfile n
    representation : Map.BrainDnaRepresentation n
    transportProfile : Transport.BrainRepresentationTransportProfile n
    representationIntegratedLaw : RepLaw.BrainRepresentationIntegratedLawProfile n
    themeIntegratedLaw : ThemeLaw.BrainThemeIntegratedLawProfile n
    crossoverIntegration : Crossover.BrainCrossoverIntegrationProfile
    atomCarrier : C_atom n
    physicalObservation : O_phys n
    encodedBases : Vec Base n
    order : ScanOrder
    emittedAdmissibility : Bool
    recoveryBoundary : Nat
    checksum : SemanticChecksumPair
    hopChecksumComposition : SemanticChecksumPair
    realismFloor : Nat

brainWholeChainIntegrationProfileOf :
  ∀ {n} → theta_i n → BrainWholeChainIntegrationProfile n
brainWholeChainIntegrationProfileOf θ =
  brainWholeChainIntegrationProfile
    θ
    (Theme.themeProfileOf (theta_i.state θ) (theta_i.region θ))
    (Map.representationOf (theta_i.state θ) (theta_i.region θ))
    (Transport.representationTransportProfileOf
      (theta_i.state θ)
      (theta_i.region θ))
    (RepLaw.brainRepresentationIntegratedLawProfile
      (theta_i.state θ)
      (theta_i.region θ))
    (ThemeLaw.brainThemeIntegratedLawProfile
      (theta_i.state θ)
      (theta_i.region θ))
    (Crossover.brainCrossoverIntegrationProfileOf (theta_i.state θ))
    (I_chain θ)
    (R_real θ)
    (Map.BrainDnaRepresentation.encodedBases
      (Map.representationOf (theta_i.state θ) (theta_i.region θ)))
    (RepLaw.BrainRepresentationIntegratedLawProfile.order
      (RepLaw.brainRepresentationIntegratedLawProfile
        (theta_i.state θ)
        (theta_i.region θ)))
    (RepLaw.BrainRepresentationIntegratedLawProfile.emittedAdmissibility
      (RepLaw.brainRepresentationIntegratedLawProfile
        (theta_i.state θ)
        (theta_i.region θ)))
    (RepLaw.BrainRepresentationIntegratedLawProfile.recoveryBoundary
      (RepLaw.brainRepresentationIntegratedLawProfile
        (theta_i.state θ)
        (theta_i.region θ)))
    (chainCarrierChecksum θ)
    (composeHopChecksums θ)
    rho_min

wholeChainIChainExact :
  ∀ {n} (θ : theta_i n) →
  BrainWholeChainIntegrationProfile.atomCarrier
    (brainWholeChainIntegrationProfileOf θ)
    ≡
  I_chain θ
wholeChainIChainExact θ = refl

wholeChainOrderLineMajor :
  ∀ {n} (θ : theta_i n) →
  BrainWholeChainIntegrationProfile.order
    (brainWholeChainIntegrationProfileOf θ)
    ≡
  lineMajor
wholeChainOrderLineMajor θ =
  RepLaw.integratedLawOrderLineMajor
    (theta_i.state θ)
    (theta_i.region θ)

wholeChainRecoveryBoundaryExact :
  ∀ {n} (θ : theta_i n) →
  BrainWholeChainIntegrationProfile.recoveryBoundary
    (brainWholeChainIntegrationProfileOf θ)
    ≡
  3
wholeChainRecoveryBoundaryExact θ =
  RepLaw.integratedLawRecoveryExact
    (theta_i.state θ)
    (theta_i.region θ)

wholeChainRealismFloorExact :
  ∀ {n} (θ : theta_i n) →
  BrainWholeChainIntegrationProfile.realismFloor
    (brainWholeChainIntegrationProfileOf θ)
    ≡
  rho_min
wholeChainRealismFloorExact θ = refl

wholeChainRealismFloorBoundedByRisk :
  ∀ {n} (θ : theta_i n) →
  BrainWholeChainIntegrationProfile.realismFloor
    (brainWholeChainIntegrationProfileOf θ)
    ≡
  Risk.SynthesisSequencingRiskProfile.recoveryBoundary
    (Risk.SynthesisSequencingRiskSurface.profile
      Risk.synthesisSequencingRiskSurface)
wholeChainRealismFloorBoundedByRisk θ = refl

record BrainWholeChainIntegrationLawSurface : Setω where
  field
    representationIntegratedLaws : RepLaw.BrainRepresentationIntegratedLawSurface
    themeIntegratedLaws : ThemeLaw.BrainThemeIntegratedLawsSurface
    crossoverIntegrationLaws : Crossover.BrainCrossoverIntegrationLawSurface
    atomicHandoff : Handoff.BrainAtomicChemistryHandoffSurface
    riskSurface : Risk.SynthesisSequencingRiskSurface
    realismLawSurface : Realism.SynthesisSequencingIntegratedRealismLawSurface
    profile : ∀ {n} → theta_i n → BrainWholeChainIntegrationProfile n
    integrationLaw : ∀ {n} → theta_i n → C_atom n
    realismLaw : ∀ {n} → theta_i n → O_phys n

brainWholeChainIntegrationLawSurface : BrainWholeChainIntegrationLawSurface
brainWholeChainIntegrationLawSurface = record
  { representationIntegratedLaws =
      RepLaw.brainRepresentationIntegratedLawSurface
  ; themeIntegratedLaws = ThemeLaw.brainThemeIntegratedLawsSurface
  ; crossoverIntegrationLaws = Crossover.brainCrossoverIntegrationLawSurface
  ; atomicHandoff = Handoff.brainAtomicChemistryHandoffSurface
  ; riskSurface = Risk.synthesisSequencingRiskSurface
  ; realismLawSurface = Realism.synthesisSequencingIntegratedRealismLawSurface
  ; profile = brainWholeChainIntegrationProfileOf
  ; integrationLaw = I_chain
  ; realismLaw = R_real
  }
