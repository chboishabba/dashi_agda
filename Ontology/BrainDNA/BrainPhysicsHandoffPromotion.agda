module Ontology.BrainDNA.BrainPhysicsHandoffPromotion where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import Ontology.BrainDNA.BrainWholeChainIntegrationLaw as Whole
open import DASHI.Physics.CliffordEvenLiftBridge as CE
open import DASHI.Physics.Closure.AtomicChemistryRecoveryTheorem as ACRT
open import DASHI.Physics.Closure.ChemistryRightLimitsQuotientCrossBandCouplingRequirement as CrossBand
open import DASHI.Physics.Closure.ChemistryRightLimitsQuotientCrossBandCandidate256Witness as Candidate256
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveObservablesTheorem as KLRWO
open import DASHI.Physics.Closure.PhysicsClosureFullCanonicalBridgePackage as PCFCBP
open import DASHI.Physics.Closure.SyntheticRealizationWitness as SRW
open import DASHI.Physics.Closure.Validation.ObservableCollapse as OC
open import DASHI.Physics.Closure.Validation.ObservableCollapseReport as OCR

------------------------------------------------------------------------
-- B4 bounded brain-to-chemistry physics handoff promotion.
--
-- This module does not derive chemistry from brain state, recover atoms,
-- spectra, scale-setting, bonding, or wet-lab realism. It only composes the
-- landed B2 whole-chain carrier with the landed B3 quotient/cross-band law
-- and the explicit theorem gates already exposed by
-- AtomicChemistryRecoveryTheorem.

C_atom : Nat → Set
C_atom = Whole.C_atom

record AtomicChemistryRecoveryGateWitness
  (atomic : ACRT.AtomicChemistryRecoveryTheorem) : Setω where
  constructor atomicChemistryRecoveryGateWitness
  field
    canonicalBridgePackagePresent :
      PCFCBP.PhysicsClosureFullCanonicalBridgePackage

    recoveredWaveObservablesPresent :
      KLRWO.KnownLimitsRecoveredWaveObservablesTheorem

    syntheticShellRealizationPresent :
      SRW.SyntheticRealizationWitness

    chemistryDictionarySupportGate : Set

    canonicalWaveLiftIntoEvenStateGate : Set

    shellObservableReportPresent :
      OCR.ObservableCollapseReport

    shellCollapseEstablishedGate :
      OCR.ObservableCollapseReport.verdict
        (ACRT.AtomicChemistryRecoveryTheorem.shellObservableReport atomic)
      ≡
      OC.collapseEstablished

    shellProfileCompatibilityGate : Set
    closedShellRecoveryGate : Set
    chemistryDictionaryCompatibilityGate : Set
    atomicChemistryRecoveryGate : Set

canonicalAtomicChemistryRecoveryGateWitness :
  AtomicChemistryRecoveryGateWitness
    ACRT.canonicalAtomicChemistryRecoveryTheorem
canonicalAtomicChemistryRecoveryGateWitness =
  let
    atomic = ACRT.canonicalAtomicChemistryRecoveryTheorem
  in
  atomicChemistryRecoveryGateWitness
    (ACRT.AtomicChemistryRecoveryTheorem.canonicalBridgePackage atomic)
    (ACRT.AtomicChemistryRecoveryTheorem.recoveredWaveObservables atomic)
    (ACRT.AtomicChemistryRecoveryTheorem.syntheticShellRealization atomic)
    (ACRT.AtomicChemistryRecoveryTheorem.chemistryDictionarySupport atomic)
    (CE.WaveLiftIntoEven.State
      (ACRT.AtomicChemistryRecoveryTheorem.canonicalWaveLiftIntoEven atomic))
    (ACRT.AtomicChemistryRecoveryTheorem.shellObservableReport atomic)
    (ACRT.AtomicChemistryRecoveryTheorem.shellCollapseEstablished atomic)
    (ACRT.AtomicChemistryRecoveryTheorem.shellProfileCompatibility atomic)
    (ACRT.AtomicChemistryRecoveryTheorem.closedShellRecovery atomic)
    (ACRT.AtomicChemistryRecoveryTheorem.chemistryDictionaryCompatibility atomic)
    (ACRT.AtomicChemistryRecoveryTheorem.atomicChemistryRecovery atomic)

record O_chem (n : Nat) : Setω where
  constructor o_chem
  field
    atomCarrier : C_atom n
    atomicRecovery : ACRT.AtomicChemistryRecoveryTheorem
    recoveryGateWitness : AtomicChemistryRecoveryGateWitness atomicRecovery

    quotientCrossBandLaw :
      CrossBand.ChemistryRightLimitsQuotientCrossBandLaw

    chemistryRightLimitsLaw :
      CrossBand.ChemistryRightLimitsLaw
        (CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.requirement
          quotientCrossBandLaw)

    LchemEntailsChemistryRightLimitsLaw :
      CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.LchemEntailsChemistryRightLimitsLaw
        quotientCrossBandLaw
        (CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.lawAtWitness
          quotientCrossBandLaw)
      ≡
      chemistryRightLimitsLaw

    nonClaimBoundary : List String

H_phys : ∀ {n} → C_atom n → O_chem n
H_phys atom =
  o_chem
    atom
    ACRT.canonicalAtomicChemistryRecoveryTheorem
    canonicalAtomicChemistryRecoveryGateWitness
    Candidate256.canonicalCandidate256QuotientCrossBandLaw
    (CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.LchemEntailsChemistryRightLimitsLaw
      Candidate256.canonicalCandidate256QuotientCrossBandLaw
      (CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.lawAtWitness
        Candidate256.canonicalCandidate256QuotientCrossBandLaw))
    refl
    ("H_phys is bounded to the existing C_atom carrier from I_chain; it does not reinterpret or mutate the brain-DNA carrier"
     ∷ "The chemistry side is the landed Candidate256 quotient/cross-band Lchem surface, not a bypass around B3"
     ∷ "AtomicChemistryRecoveryTheorem gates are carried as theorem-facing gates only; no empirical atom, spectra, scale-setting, bonding, or wet-lab recovery is claimed"
     ∷ [])

H_physCarriesAtom :
  ∀ {n} (atom : C_atom n) →
  O_chem.atomCarrier (H_phys atom) ≡ atom
H_physCarriesAtom atom = refl

H_physCarriesAtomicRecoveryGateWitness :
  ∀ {n} (atom : C_atom n) →
  AtomicChemistryRecoveryGateWitness (O_chem.atomicRecovery (H_phys atom))
H_physCarriesAtomicRecoveryGateWitness atom =
  O_chem.recoveryGateWitness (H_phys atom)

H_physCarriesLchemWitness :
  ∀ {n} (atom : C_atom n) →
  CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.Lchem
    (O_chem.quotientCrossBandLaw (H_phys atom))
    (CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.q
      (O_chem.quotientCrossBandLaw (H_phys atom))
      (CrossBand.ChemistryRightLimitsQuotientCrossBandCouplingRequirement.left
        (CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.requirement
          (O_chem.quotientCrossBandLaw (H_phys atom)))))
    (CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.q
      (O_chem.quotientCrossBandLaw (H_phys atom))
      (CrossBand.ChemistryRightLimitsQuotientCrossBandCouplingRequirement.right
        (CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.requirement
          (O_chem.quotientCrossBandLaw (H_phys atom)))))
H_physCarriesLchemWitness atom =
  CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.lawAtWitness
    (O_chem.quotientCrossBandLaw (H_phys atom))

H_physLchemEntailsRightLimitsLaw :
  ∀ {n} (atom : C_atom n) →
  O_chem.LchemEntailsChemistryRightLimitsLaw (H_phys atom)
    ≡
  refl
H_physLchemEntailsRightLimitsLaw atom = refl

record BrainPhysicsHandoffPromotion (n : Nat) : Setω where
  constructor brainPhysicsHandoffPromotion
  field
    theta : Whole.theta_i n
    wholeChainProfile : Whole.BrainWholeChainIntegrationProfile n

    iChainCarrier : C_atom n
    iChainCarrierExact : iChainCarrier ≡ Whole.I_chain theta

    physicsObservation : Whole.O_phys n
    physicsObservationClosesIChain :
      Whole.O_phys.atomCarrier physicsObservation
      ≡
      iChainCarrier

    chemOutput : O_chem n
    H_physCarriesI_chain :
      O_chem.atomCarrier chemOutput
      ≡
      iChainCarrier

    quotientCrossBandLaw :
      CrossBand.ChemistryRightLimitsQuotientCrossBandLaw

    LchemWitness :
      CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.Lchem
        quotientCrossBandLaw
        (CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.q quotientCrossBandLaw
          (CrossBand.ChemistryRightLimitsQuotientCrossBandCouplingRequirement.left
            (CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.requirement
              quotientCrossBandLaw)))
        (CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.q quotientCrossBandLaw
          (CrossBand.ChemistryRightLimitsQuotientCrossBandCouplingRequirement.right
            (CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.requirement
              quotientCrossBandLaw)))

    LchemEntailsRightLimitsGate :
      CrossBand.ChemistryRightLimitsLaw
        (CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.requirement
          quotientCrossBandLaw)

    atomicRecoveryGateWitness :
      AtomicChemistryRecoveryGateWitness
        (O_chem.atomicRecovery chemOutput)

    nonClaimBoundary : List String

physicsHandoffPromotionOf :
  ∀ {n} → Whole.theta_i n → BrainPhysicsHandoffPromotion n
physicsHandoffPromotionOf θ =
  let
    carrier = Whole.I_chain θ
    chem = H_phys carrier
    law = Candidate256.canonicalCandidate256QuotientCrossBandLaw
  in
  brainPhysicsHandoffPromotion
    θ
    (Whole.brainWholeChainIntegrationProfileOf θ)
    carrier
    refl
    (Whole.R_real θ)
    refl
    chem
    refl
    law
    (CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.lawAtWitness law)
    (CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.LchemEntailsChemistryRightLimitsLaw
      law
      (CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.lawAtWitness law))
    (O_chem.recoveryGateWitness chem)
    ("B4 promotion composes Whole.I_chain through H_phys; it does not construct an independent chemistry carrier"
     ∷ "The Lchem witness is exactly the landed Candidate256 quotient/cross-band law surface"
     ∷ "Atomic recovery gates are exposed only as gates already present on AtomicChemistryRecoveryTheorem"
     ∷ [])

H_phys∘I_chainCarriesCarrier :
  ∀ {n} (θ : Whole.theta_i n) →
  O_chem.atomCarrier (H_phys (Whole.I_chain θ))
    ≡
  Whole.I_chain θ
H_phys∘I_chainCarriesCarrier θ = refl

H_phys∘I_chainCarriesLchem :
  ∀ {n} (θ : Whole.theta_i n) →
  CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.Lchem
    (O_chem.quotientCrossBandLaw (H_phys (Whole.I_chain θ)))
    (CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.q
      (O_chem.quotientCrossBandLaw (H_phys (Whole.I_chain θ)))
      (CrossBand.ChemistryRightLimitsQuotientCrossBandCouplingRequirement.left
        (CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.requirement
          (O_chem.quotientCrossBandLaw (H_phys (Whole.I_chain θ))))))
    (CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.q
      (O_chem.quotientCrossBandLaw (H_phys (Whole.I_chain θ)))
      (CrossBand.ChemistryRightLimitsQuotientCrossBandCouplingRequirement.right
        (CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.requirement
          (O_chem.quotientCrossBandLaw (H_phys (Whole.I_chain θ))))))
H_phys∘I_chainCarriesLchem θ =
  H_physCarriesLchemWitness (Whole.I_chain θ)

H_phys∘I_chainCarriesAtomicRecoveryGates :
  ∀ {n} (θ : Whole.theta_i n) →
  AtomicChemistryRecoveryGateWitness
    (O_chem.atomicRecovery (H_phys (Whole.I_chain θ)))
H_phys∘I_chainCarriesAtomicRecoveryGates θ =
  O_chem.recoveryGateWitness (H_phys (Whole.I_chain θ))

promotionEntailsAtomicRecoveryGates :
  ∀ {n} (θ : Whole.theta_i n) →
  AtomicChemistryRecoveryGateWitness
    (O_chem.atomicRecovery
      (BrainPhysicsHandoffPromotion.chemOutput
        (physicsHandoffPromotionOf θ)))
promotionEntailsAtomicRecoveryGates θ =
  BrainPhysicsHandoffPromotion.atomicRecoveryGateWitness
    (physicsHandoffPromotionOf θ)

promotionEntailsLchemRightLimits :
  ∀ {n} (θ : Whole.theta_i n) →
  BrainPhysicsHandoffPromotion.LchemEntailsRightLimitsGate
    (physicsHandoffPromotionOf θ)
    ≡
  O_chem.chemistryRightLimitsLaw
    (BrainPhysicsHandoffPromotion.chemOutput
      (physicsHandoffPromotionOf θ))
promotionEntailsLchemRightLimits θ = refl
