module DASHI.Promotion.NumericMeasuredAuthorityTokenNormalization where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Level)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Constants.Registry as Registry
import DASHI.Promotion.NumericAndAuthorityObligations as Numeric
import DASHI.Promotion.NumericAuthorityTokenIntake as Intake
import DASHI.Promotion.NumericMeasuredAuthorityBinding as Binding

------------------------------------------------------------------------
-- Normalized measured-value authority-token surface.
--
-- This is a disjoint consumer module: it does not extend the canonical
-- binding or intake receipts, and it does not introduce numeric values.
-- It normalizes authority-token requirements for the measured registry
-- families that need explicit version/checksum/access-date/uncertainty/
-- rounding/unit/validity metadata before any numeric value can be used.

data NormalizedMeasuredAuthorityProvider : Set where
  normalizedCODATAProvider : NormalizedMeasuredAuthorityProvider
  normalizedPDGProvider : NormalizedMeasuredAuthorityProvider
  normalizedCODATAPDGProvider : NormalizedMeasuredAuthorityProvider

data NormalizedMeasuredAuthorityFamily : Set where
  normalizedGFamily : NormalizedMeasuredAuthorityFamily
  normalizedAlphaFamily : NormalizedMeasuredAuthorityFamily
  normalizedMassFamily : NormalizedMeasuredAuthorityFamily
  normalizedElectromagneticVacuumFamily :
    NormalizedMeasuredAuthorityFamily
  normalizedRydbergFamily : NormalizedMeasuredAuthorityFamily
  normalizedParticleStandardModelFamily :
    NormalizedMeasuredAuthorityFamily

record TokenVersion : Set where
  field
    tokenVersionName : String
    tokenVersionAuthority : String
    tokenVersionScope : String

open TokenVersion public

record TokenChecksum : Set where
  field
    tokenChecksumName : String
    tokenChecksumAlgorithm : String
    tokenChecksumCoverage : String

open TokenChecksum public

record TokenAccessDate : Set where
  field
    tokenAccessDateName : String
    tokenAccessDateValue : String
    tokenAccessDateScope : String

open TokenAccessDate public

record TokenUncertainty : Set where
  field
    tokenUncertaintyName : String
    tokenUncertaintyConvention : String
    tokenCovariancePolicy : String

open TokenUncertainty public

record TokenRounding : Set where
  field
    tokenRoundingName : String
    tokenRoundingMode : String
    tokenFiniteUsePolicy : String

open TokenRounding public

record TokenUnit : Set where
  field
    tokenUnitName : String
    tokenUnitSystem : String
    tokenUnitConversionPolicy : String

open TokenUnit public

record TokenValidity : Set where
  field
    tokenValidityName : String
    tokenValidityScope : String
    tokenValidityBoundary : String

open TokenValidity public

record NormalizedMeasuredAuthorityToken : Set₁ where
  field
    normalizedTokenLabel : String
    normalizedSymbol : String
    normalizedRegistrySlotName : String
    normalizedAuthoritySource : String
    normalizedProvider : NormalizedMeasuredAuthorityProvider
    normalizedFamily : NormalizedMeasuredAuthorityFamily
    normalizedTokenName : String
    normalizedValueIngestionReceiptName : String
    sourceRegistry : Registry.ConstantsRegistry
    sourceBindingReceipt :
      Binding.NumericMeasuredAuthorityBindingReceipt
    sourceTokenIntakeReceipt :
      Intake.NumericAuthorityTokenIntakeReceipt
    sourceObligationIndex :
      Numeric.NumericAndAuthorityObligationIndex
    version : TokenVersion
    checksum : TokenChecksum
    accessDate : TokenAccessDate
    uncertainty : TokenUncertainty
    rounding : TokenRounding
    unit : TokenUnit
    validity : TokenValidity
    versionPresent : Bool
    versionPresentIsTrue : versionPresent ≡ true
    checksumPresent : Bool
    checksumPresentIsTrue : checksumPresent ≡ true
    accessDatePresent : Bool
    accessDatePresentIsTrue : accessDatePresent ≡ true
    uncertaintyPresent : Bool
    uncertaintyPresentIsTrue : uncertaintyPresent ≡ true
    roundingPresent : Bool
    roundingPresentIsTrue : roundingPresent ≡ true
    unitPresent : Bool
    unitPresentIsTrue : unitPresent ≡ true
    validityPresent : Bool
    validityPresentIsTrue : validityPresent ≡ true
    acceptedAuthorityTokenPresent : Bool
    acceptedAuthorityTokenPresentIsFalse :
      acceptedAuthorityTokenPresent ≡ false
    numericValueLoaded : Bool
    numericValueLoadedIsFalse : numericValueLoaded ≡ false
    numericValuePromoted : Bool
    numericValuePromotedIsFalse :
      numericValuePromoted ≡ false
    falseNumericPromotion : Bool
    falseNumericPromotionIsTrue :
      falseNumericPromotion ≡ true

open NormalizedMeasuredAuthorityToken public

codataTokenVersion : TokenVersion
codataTokenVersion = record
  { tokenVersionName = "NIST CODATA 2022 recommended-values token"
  ; tokenVersionAuthority = "NIST CODATA"
  ; tokenVersionScope = "measured and adjusted fundamental constants"
  }

pdgTokenVersion : TokenVersion
pdgTokenVersion = record
  { tokenVersionName = "PDG current particle-data token"
  ; tokenVersionAuthority = "Particle Data Group"
  ; tokenVersionScope =
      "particle masses, couplings, mixing, and fitted SM inputs"
  }

codataPDGTokenVersion : TokenVersion
codataPDGTokenVersion = record
  { tokenVersionName = "CODATA/PDG cross-authority measured token"
  ; tokenVersionAuthority = "NIST CODATA and Particle Data Group"
  ; tokenVersionScope =
      "measured values available in both metrology and particle-data lanes"
  }

codataChecksum : TokenChecksum
codataChecksum = record
  { tokenChecksumName = "CODATA authority artifact checksum"
  ; tokenChecksumAlgorithm = "SHA-256"
  ; tokenChecksumCoverage =
      "authority version, value text, uncertainty, unit, and table row"
  }

pdgChecksum : TokenChecksum
pdgChecksum = record
  { tokenChecksumName = "PDG authority artifact checksum"
  ; tokenChecksumAlgorithm = "SHA-256"
  ; tokenChecksumCoverage =
      "PDG table version, fit convention, value text, uncertainty, and unit"
  }

canonicalAccessDate : TokenAccessDate
canonicalAccessDate = record
  { tokenAccessDateName = "normalized authority access date"
  ; tokenAccessDateValue = "2026-06-07"
  ; tokenAccessDateScope =
      "Worker 5 authority-token normalization construction date"
  }

codataUncertainty : TokenUncertainty
codataUncertainty = record
  { tokenUncertaintyName = "CODATA uncertainty token field"
  ; tokenUncertaintyConvention =
      "standard uncertainty from the authority row"
  ; tokenCovariancePolicy =
      "covariance is unavailable until imported by a value token"
  }

pdgUncertainty : TokenUncertainty
pdgUncertainty = record
  { tokenUncertaintyName = "PDG uncertainty token field"
  ; tokenUncertaintyConvention =
      "quoted fit uncertainty and convention from the PDG row"
  ; tokenCovariancePolicy =
      "fit covariance is unavailable until imported by a value token"
  }

canonicalRounding : TokenRounding
canonicalRounding = record
  { tokenRoundingName = "authority-preserving rounding token field"
  ; tokenRoundingMode =
      "preserve authority significant digits before finite representation"
  ; tokenFiniteUsePolicy =
      "finite numeric use requires a separate ingestion receipt"
  }

codataUnit : TokenUnit
codataUnit = record
  { tokenUnitName = "CODATA SI unit token field"
  ; tokenUnitSystem = "SI or dimensionless CODATA convention"
  ; tokenUnitConversionPolicy =
      "no natural-unit or derived-unit conversion without adapter receipt"
  }

pdgUnit : TokenUnit
pdgUnit = record
  { tokenUnitName = "PDG particle-unit token field"
  ; tokenUnitSystem =
      "GeV, MeV, c, scheme-dependent, or dimensionless PDG convention"
  ; tokenUnitConversionPolicy =
      "SI conversion requires explicit constant and scheme adapters"
  }

codataValidity : TokenValidity
codataValidity = record
  { tokenValidityName = "CODATA measured-value validity token field"
  ; tokenValidityScope =
      "metrology, atomic, electromagnetic, and gravity adapters"
  ; tokenValidityBoundary =
      "authority row only; not a dynamics theorem or adequacy proof"
  }

pdgValidity : TokenValidity
pdgValidity = record
  { tokenValidityName = "PDG measured-value validity token field"
  ; tokenValidityScope =
      "particle, Standard Model, collider, QCD, and electroweak adapters"
  ; tokenValidityBoundary =
      "authority row only; not a QFT or Standard Model promotion"
  }

mkNormalizedToken :
  String →
  String →
  String →
  String →
  NormalizedMeasuredAuthorityProvider →
  NormalizedMeasuredAuthorityFamily →
  String →
  String →
  TokenVersion →
  TokenChecksum →
  TokenUncertainty →
  TokenUnit →
  TokenValidity →
  NormalizedMeasuredAuthorityToken
mkNormalizedToken
  label symbol registrySlot authority provider family tokenName
  receiptName version checksum uncertainty unit validity =
  record
    { normalizedTokenLabel = label
    ; normalizedSymbol = symbol
    ; normalizedRegistrySlotName = registrySlot
    ; normalizedAuthoritySource = authority
    ; normalizedProvider = provider
    ; normalizedFamily = family
    ; normalizedTokenName = tokenName
    ; normalizedValueIngestionReceiptName = receiptName
    ; sourceRegistry = Registry.repoWideConstantsRegistry
    ; sourceBindingReceipt =
        Binding.canonicalNumericMeasuredAuthorityBindingReceipt
    ; sourceTokenIntakeReceipt =
        Intake.canonicalNumericAuthorityTokenIntakeReceipt
    ; sourceObligationIndex =
        Numeric.canonicalNumericAndAuthorityObligationIndex
    ; version = version
    ; checksum = checksum
    ; accessDate = canonicalAccessDate
    ; uncertainty = uncertainty
    ; rounding = canonicalRounding
    ; unit = unit
    ; validity = validity
    ; versionPresent = true
    ; versionPresentIsTrue = refl
    ; checksumPresent = true
    ; checksumPresentIsTrue = refl
    ; accessDatePresent = true
    ; accessDatePresentIsTrue = refl
    ; uncertaintyPresent = true
    ; uncertaintyPresentIsTrue = refl
    ; roundingPresent = true
    ; roundingPresentIsTrue = refl
    ; unitPresent = true
    ; unitPresentIsTrue = refl
    ; validityPresent = true
    ; validityPresentIsTrue = refl
    ; acceptedAuthorityTokenPresent = false
    ; acceptedAuthorityTokenPresentIsFalse = refl
    ; numericValueLoaded = false
    ; numericValueLoadedIsFalse = refl
    ; numericValuePromoted = false
    ; numericValuePromotedIsFalse = refl
    ; falseNumericPromotion = true
    ; falseNumericPromotionIsTrue = refl
    }

mkCODATAToken :
  String →
  String →
  String →
  NormalizedMeasuredAuthorityFamily →
  String →
  String →
  NormalizedMeasuredAuthorityToken
mkCODATAToken label symbol registrySlot family tokenName receiptName =
  mkNormalizedToken
    label
    symbol
    registrySlot
    "NIST CODATA fundamental physical constants"
    normalizedCODATAProvider
    family
    tokenName
    receiptName
    codataTokenVersion
    codataChecksum
    codataUncertainty
    codataUnit
    codataValidity

mkPDGToken :
  String →
  String →
  String →
  NormalizedMeasuredAuthorityFamily →
  String →
  String →
  NormalizedMeasuredAuthorityToken
mkPDGToken label symbol registrySlot family tokenName receiptName =
  mkNormalizedToken
    label
    symbol
    registrySlot
    "PDG particle data"
    normalizedPDGProvider
    family
    tokenName
    receiptName
    pdgTokenVersion
    pdgChecksum
    pdgUncertainty
    pdgUnit
    pdgValidity

mkCODATAPDGToken :
  String →
  String →
  String →
  NormalizedMeasuredAuthorityFamily →
  String →
  String →
  NormalizedMeasuredAuthorityToken
mkCODATAPDGToken label symbol registrySlot family tokenName receiptName =
  mkNormalizedToken
    label
    symbol
    registrySlot
    "NIST CODATA fundamental physical constants / PDG particle data"
    normalizedCODATAPDGProvider
    family
    tokenName
    receiptName
    codataPDGTokenVersion
    pdgChecksum
    pdgUncertainty
    pdgUnit
    pdgValidity

gNormalizedToken : NormalizedMeasuredAuthorityToken
gNormalizedToken =
  mkCODATAToken
    "normalized measured-value token for Newtonian gravitational constant"
    "G"
    "DASHI.Constants.Registry.measuredPhysicsConstantAuthoritySlots.G"
    normalizedGFamily
    "normalized-CODATA-G-authority-token"
    "normalized-G-value-ingestion-receipt"

alphaNormalizedToken : NormalizedMeasuredAuthorityToken
alphaNormalizedToken =
  mkCODATAToken
    "normalized measured-value token for fine-structure constant"
    "alpha"
    "DASHI.Constants.Registry.measuredPhysicsConstantAuthoritySlots.alpha"
    normalizedAlphaFamily
    "normalized-CODATA-alpha-authority-token"
    "normalized-alpha-value-ingestion-receipt"

electronMassNormalizedToken : NormalizedMeasuredAuthorityToken
electronMassNormalizedToken =
  mkCODATAToken
    "normalized measured-value token for electron rest mass"
    "m_e"
    "DASHI.Constants.Registry.measuredPhysicsConstantAuthoritySlots.m_e"
    normalizedMassFamily
    "normalized-CODATA-m_e-authority-token"
    "normalized-m_e-value-ingestion-receipt"

protonMassNormalizedToken : NormalizedMeasuredAuthorityToken
protonMassNormalizedToken =
  mkCODATAToken
    "normalized measured-value token for proton rest mass"
    "m_p"
    "DASHI.Constants.Registry.measuredPhysicsConstantAuthoritySlots.m_p"
    normalizedMassFamily
    "normalized-CODATA-m_p-authority-token"
    "normalized-m_p-value-ingestion-receipt"

neutronMassNormalizedToken : NormalizedMeasuredAuthorityToken
neutronMassNormalizedToken =
  mkCODATAToken
    "normalized measured-value token for neutron rest mass"
    "m_n"
    "DASHI.Constants.Registry.measuredPhysicsConstantAuthoritySlots.m_n"
    normalizedMassFamily
    "normalized-CODATA-m_n-authority-token"
    "normalized-m_n-value-ingestion-receipt"

muonMassNormalizedToken : NormalizedMeasuredAuthorityToken
muonMassNormalizedToken =
  mkCODATAPDGToken
    "normalized measured-value token for muon rest mass"
    "m_mu"
    "DASHI.Constants.Registry.measuredPhysicsConstantAuthoritySlots.m_mu"
    normalizedMassFamily
    "normalized-CODATA-PDG-m_mu-authority-token"
    "normalized-m_mu-value-ingestion-receipt"

tauMassNormalizedToken : NormalizedMeasuredAuthorityToken
tauMassNormalizedToken =
  mkCODATAPDGToken
    "normalized measured-value token for tau rest mass"
    "m_tau"
    "DASHI.Constants.Registry.measuredPhysicsConstantAuthoritySlots.m_tau"
    normalizedMassFamily
    "normalized-CODATA-PDG-m_tau-authority-token"
    "normalized-m_tau-value-ingestion-receipt"

protonMassEnergyNormalizedToken : NormalizedMeasuredAuthorityToken
protonMassEnergyNormalizedToken =
  mkCODATAToken
    "normalized measured-value token for proton mass energy equivalent"
    "m_p c^2"
    "DASHI.Constants.Registry.measuredPhysicsConstantAuthoritySlots.m_p_c2"
    normalizedMassFamily
    "normalized-CODATA-m_p_c2-authority-token"
    "normalized-m_p_c2-value-ingestion-receipt"

epsilonZeroNormalizedToken : NormalizedMeasuredAuthorityToken
epsilonZeroNormalizedToken =
  mkCODATAToken
    "normalized measured-value token for vacuum permittivity"
    "epsilon_0"
    "DASHI.Constants.Registry.measuredPhysicsConstantAuthoritySlots.epsilon_0"
    normalizedElectromagneticVacuumFamily
    "normalized-CODATA-epsilon_0-authority-token"
    "normalized-epsilon_0-value-ingestion-receipt"

muZeroNormalizedToken : NormalizedMeasuredAuthorityToken
muZeroNormalizedToken =
  mkCODATAToken
    "normalized measured-value token for vacuum permeability"
    "mu_0"
    "DASHI.Constants.Registry.measuredPhysicsConstantAuthoritySlots.mu_0"
    normalizedElectromagneticVacuumFamily
    "normalized-CODATA-mu_0-authority-token"
    "normalized-mu_0-value-ingestion-receipt"

zZeroNormalizedToken : NormalizedMeasuredAuthorityToken
zZeroNormalizedToken =
  mkCODATAToken
    "normalized measured-value token for characteristic impedance of vacuum"
    "Z_0"
    "DASHI.Constants.Registry.measuredPhysicsConstantAuthoritySlots.Z_0"
    normalizedElectromagneticVacuumFamily
    "normalized-CODATA-Z_0-authority-token"
    "normalized-Z_0-value-ingestion-receipt"

rydbergNormalizedToken : NormalizedMeasuredAuthorityToken
rydbergNormalizedToken =
  mkCODATAToken
    "normalized measured-value token for Rydberg constant"
    "R_infinity"
    "DASHI.Constants.Registry.measuredPhysicsConstantAuthoritySlots.R_infinity"
    normalizedRydbergFamily
    "normalized-CODATA-R_infinity-authority-token"
    "normalized-R_infinity-value-ingestion-receipt"

higgsMassNormalizedToken : NormalizedMeasuredAuthorityToken
higgsMassNormalizedToken =
  mkPDGToken
    "normalized measured-value token for Higgs boson mass"
    "m_H"
    "DASHI.Constants.Registry.measuredPhysicsConstantAuthoritySlots.m_H"
    normalizedParticleStandardModelFamily
    "normalized-PDG-m_H-authority-token"
    "normalized-m_H-value-ingestion-receipt"

wzMassesNormalizedToken : NormalizedMeasuredAuthorityToken
wzMassesNormalizedToken =
  mkPDGToken
    "normalized measured-value token for W and Z boson masses"
    "m_W, m_Z"
    "DASHI.Constants.Registry.measuredPhysicsConstantAuthoritySlots.m_W_m_Z"
    normalizedParticleStandardModelFamily
    "normalized-PDG-m_W_m_Z-authority-token"
    "normalized-m_W_m_Z-value-ingestion-receipt"

quarkMassesNormalizedToken : NormalizedMeasuredAuthorityToken
quarkMassesNormalizedToken =
  mkPDGToken
    "normalized measured-value token for quark masses"
    "m_q"
    "DASHI.Constants.Registry.measuredPhysicsConstantAuthoritySlots.m_q"
    normalizedParticleStandardModelFamily
    "normalized-PDG-m_q-authority-token"
    "normalized-m_q-value-ingestion-receipt"

ckmPmnsNormalizedToken : NormalizedMeasuredAuthorityToken
ckmPmnsNormalizedToken =
  mkPDGToken
    "normalized measured-value token for CKM and PMNS parameters"
    "CKM, PMNS"
    "DASHI.Constants.Registry.measuredPhysicsConstantAuthoritySlots.CKM_PMNS"
    normalizedParticleStandardModelFamily
    "normalized-PDG-CKM-PMNS-authority-token"
    "normalized-CKM-PMNS-value-ingestion-receipt"

alphaSNormalizedToken : NormalizedMeasuredAuthorityToken
alphaSNormalizedToken =
  mkPDGToken
    "normalized measured-value token for strong coupling constant"
    "alpha_s"
    "DASHI.Constants.Registry.measuredPhysicsConstantAuthoritySlots.alpha_s"
    normalizedParticleStandardModelFamily
    "normalized-PDG-alpha_s-authority-token"
    "normalized-alpha_s-value-ingestion-receipt"

fermiCouplingNormalizedToken : NormalizedMeasuredAuthorityToken
fermiCouplingNormalizedToken =
  mkCODATAPDGToken
    "normalized measured-value token for Fermi coupling constant"
    "G_F"
    "DASHI.Constants.Registry.measuredPhysicsConstantAuthoritySlots.G_F"
    normalizedParticleStandardModelFamily
    "normalized-CODATA-PDG-G_F-authority-token"
    "normalized-G_F-value-ingestion-receipt"

canonicalNormalizedMeasuredAuthorityTokens :
  List NormalizedMeasuredAuthorityToken
canonicalNormalizedMeasuredAuthorityTokens =
  gNormalizedToken
  ∷ alphaNormalizedToken
  ∷ electronMassNormalizedToken
  ∷ protonMassNormalizedToken
  ∷ neutronMassNormalizedToken
  ∷ muonMassNormalizedToken
  ∷ tauMassNormalizedToken
  ∷ protonMassEnergyNormalizedToken
  ∷ epsilonZeroNormalizedToken
  ∷ muZeroNormalizedToken
  ∷ zZeroNormalizedToken
  ∷ rydbergNormalizedToken
  ∷ higgsMassNormalizedToken
  ∷ wzMassesNormalizedToken
  ∷ quarkMassesNormalizedToken
  ∷ ckmPmnsNormalizedToken
  ∷ alphaSNormalizedToken
  ∷ fermiCouplingNormalizedToken
  ∷ []

canonicalNormalizedCODATATokens :
  List NormalizedMeasuredAuthorityToken
canonicalNormalizedCODATATokens =
  gNormalizedToken
  ∷ alphaNormalizedToken
  ∷ electronMassNormalizedToken
  ∷ protonMassNormalizedToken
  ∷ neutronMassNormalizedToken
  ∷ protonMassEnergyNormalizedToken
  ∷ epsilonZeroNormalizedToken
  ∷ muZeroNormalizedToken
  ∷ zZeroNormalizedToken
  ∷ rydbergNormalizedToken
  ∷ []

canonicalNormalizedPDGTokens :
  List NormalizedMeasuredAuthorityToken
canonicalNormalizedPDGTokens =
  higgsMassNormalizedToken
  ∷ wzMassesNormalizedToken
  ∷ quarkMassesNormalizedToken
  ∷ ckmPmnsNormalizedToken
  ∷ alphaSNormalizedToken
  ∷ []

canonicalNormalizedCODATAPDGTokens :
  List NormalizedMeasuredAuthorityToken
canonicalNormalizedCODATAPDGTokens =
  muonMassNormalizedToken
  ∷ tauMassNormalizedToken
  ∷ fermiCouplingNormalizedToken
  ∷ []

canonicalNormalizedMassTokens : List NormalizedMeasuredAuthorityToken
canonicalNormalizedMassTokens =
  electronMassNormalizedToken
  ∷ protonMassNormalizedToken
  ∷ neutronMassNormalizedToken
  ∷ muonMassNormalizedToken
  ∷ tauMassNormalizedToken
  ∷ protonMassEnergyNormalizedToken
  ∷ []

canonicalNormalizedElectromagneticVacuumTokens :
  List NormalizedMeasuredAuthorityToken
canonicalNormalizedElectromagneticVacuumTokens =
  epsilonZeroNormalizedToken
  ∷ muZeroNormalizedToken
  ∷ zZeroNormalizedToken
  ∷ []

canonicalNormalizedParticleSMTokens :
  List NormalizedMeasuredAuthorityToken
canonicalNormalizedParticleSMTokens =
  higgsMassNormalizedToken
  ∷ wzMassesNormalizedToken
  ∷ quarkMassesNormalizedToken
  ∷ ckmPmnsNormalizedToken
  ∷ alphaSNormalizedToken
  ∷ fermiCouplingNormalizedToken
  ∷ []

canonicalNormalizedTokenFieldNames : List String
canonicalNormalizedTokenFieldNames =
  "version"
  ∷ "checksum"
  ∷ "accessDate"
  ∷ "uncertainty"
  ∷ "rounding"
  ∷ "unit"
  ∷ "validity"
  ∷ []

listCount : ∀ {a : Level} {A : Set a} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

record NormalizedMeasuredAuthorityTokenReceipt : Set₁ where
  field
    receiptLabel : String
    sourceRegistry : Registry.ConstantsRegistry
    sourceBindingReceipt :
      Binding.NumericMeasuredAuthorityBindingReceipt
    sourceTokenIntakeReceipt :
      Intake.NumericAuthorityTokenIntakeReceipt
    sourceObligationIndex :
      Numeric.NumericAndAuthorityObligationIndex
    normalizedTokens : List NormalizedMeasuredAuthorityToken
    codataTokens : List NormalizedMeasuredAuthorityToken
    pdgTokens : List NormalizedMeasuredAuthorityToken
    codataPDGTokens : List NormalizedMeasuredAuthorityToken
    massTokens : List NormalizedMeasuredAuthorityToken
    electromagneticVacuumTokens :
      List NormalizedMeasuredAuthorityToken
    particleSMTokens : List NormalizedMeasuredAuthorityToken
    requiredFieldNames : List String
    normalizedTokenCount : Nat
    normalizedTokenCountIs18 : normalizedTokenCount ≡ 18
    codataTokenCount : Nat
    codataTokenCountIs10 : codataTokenCount ≡ 10
    pdgTokenCount : Nat
    pdgTokenCountIs5 : pdgTokenCount ≡ 5
    codataPDGTokenCount : Nat
    codataPDGTokenCountIs3 : codataPDGTokenCount ≡ 3
    massTokenCount : Nat
    massTokenCountIs6 : massTokenCount ≡ 6
    electromagneticVacuumTokenCount : Nat
    electromagneticVacuumTokenCountIs3 :
      electromagneticVacuumTokenCount ≡ 3
    particleSMTokenCount : Nat
    particleSMTokenCountIs6 : particleSMTokenCount ≡ 6
    requiredFieldCount : Nat
    requiredFieldCountIs7 : requiredFieldCount ≡ 7
    everyTokenHasVersion : Bool
    everyTokenHasVersionIsTrue : everyTokenHasVersion ≡ true
    everyTokenHasChecksum : Bool
    everyTokenHasChecksumIsTrue : everyTokenHasChecksum ≡ true
    everyTokenHasAccessDate : Bool
    everyTokenHasAccessDateIsTrue : everyTokenHasAccessDate ≡ true
    everyTokenHasUncertainty : Bool
    everyTokenHasUncertaintyIsTrue : everyTokenHasUncertainty ≡ true
    everyTokenHasRounding : Bool
    everyTokenHasRoundingIsTrue : everyTokenHasRounding ≡ true
    everyTokenHasUnit : Bool
    everyTokenHasUnitIsTrue : everyTokenHasUnit ≡ true
    everyTokenHasValidity : Bool
    everyTokenHasValidityIsTrue : everyTokenHasValidity ≡ true
    normalizedAcceptedAuthorityTokenPresent : Bool
    normalizedAcceptedAuthorityTokenPresentIsFalse :
      normalizedAcceptedAuthorityTokenPresent ≡ false
    intakeAcceptedAuthorityTokenPresent : Bool
    intakeAcceptedAuthorityTokenPresentIsFalse :
      intakeAcceptedAuthorityTokenPresent ≡ false
    normalizedNumericValueLoaded : Bool
    normalizedNumericValueLoadedIsFalse :
      normalizedNumericValueLoaded ≡ false
    normalizedNumericValuePromoted : Bool
    normalizedNumericValuePromotedIsFalse :
      normalizedNumericValuePromoted ≡ false
    bindingNumericValuePromoted : Bool
    bindingNumericValuePromotedIsFalse :
      bindingNumericValuePromoted ≡ false
    intakeNumericValuePromoted : Bool
    intakeNumericValuePromotedIsFalse :
      intakeNumericValuePromoted ≡ false
    obligationNumericValuePromoted : Bool
    obligationNumericValuePromotedIsFalse :
      obligationNumericValuePromoted ≡ false
    falseNumericPromotion : Bool
    falseNumericPromotionIsTrue :
      falseNumericPromotion ≡ true

open NormalizedMeasuredAuthorityTokenReceipt public

canonicalNormalizedMeasuredAuthorityTokenReceipt :
  NormalizedMeasuredAuthorityTokenReceipt
canonicalNormalizedMeasuredAuthorityTokenReceipt = record
  { receiptLabel =
      "normalized measured-value authority tokens remain unpromoted"
  ; sourceRegistry = Registry.repoWideConstantsRegistry
  ; sourceBindingReceipt =
      Binding.canonicalNumericMeasuredAuthorityBindingReceipt
  ; sourceTokenIntakeReceipt =
      Intake.canonicalNumericAuthorityTokenIntakeReceipt
  ; sourceObligationIndex =
      Numeric.canonicalNumericAndAuthorityObligationIndex
  ; normalizedTokens =
      canonicalNormalizedMeasuredAuthorityTokens
  ; codataTokens =
      canonicalNormalizedCODATATokens
  ; pdgTokens =
      canonicalNormalizedPDGTokens
  ; codataPDGTokens =
      canonicalNormalizedCODATAPDGTokens
  ; massTokens =
      canonicalNormalizedMassTokens
  ; electromagneticVacuumTokens =
      canonicalNormalizedElectromagneticVacuumTokens
  ; particleSMTokens =
      canonicalNormalizedParticleSMTokens
  ; requiredFieldNames =
      canonicalNormalizedTokenFieldNames
  ; normalizedTokenCount =
      listCount canonicalNormalizedMeasuredAuthorityTokens
  ; normalizedTokenCountIs18 = refl
  ; codataTokenCount =
      listCount canonicalNormalizedCODATATokens
  ; codataTokenCountIs10 = refl
  ; pdgTokenCount =
      listCount canonicalNormalizedPDGTokens
  ; pdgTokenCountIs5 = refl
  ; codataPDGTokenCount =
      listCount canonicalNormalizedCODATAPDGTokens
  ; codataPDGTokenCountIs3 = refl
  ; massTokenCount =
      listCount canonicalNormalizedMassTokens
  ; massTokenCountIs6 = refl
  ; electromagneticVacuumTokenCount =
      listCount canonicalNormalizedElectromagneticVacuumTokens
  ; electromagneticVacuumTokenCountIs3 = refl
  ; particleSMTokenCount =
      listCount canonicalNormalizedParticleSMTokens
  ; particleSMTokenCountIs6 = refl
  ; requiredFieldCount =
      listCount canonicalNormalizedTokenFieldNames
  ; requiredFieldCountIs7 = refl
  ; everyTokenHasVersion = true
  ; everyTokenHasVersionIsTrue = refl
  ; everyTokenHasChecksum = true
  ; everyTokenHasChecksumIsTrue = refl
  ; everyTokenHasAccessDate = true
  ; everyTokenHasAccessDateIsTrue = refl
  ; everyTokenHasUncertainty = true
  ; everyTokenHasUncertaintyIsTrue = refl
  ; everyTokenHasRounding = true
  ; everyTokenHasRoundingIsTrue = refl
  ; everyTokenHasUnit = true
  ; everyTokenHasUnitIsTrue = refl
  ; everyTokenHasValidity = true
  ; everyTokenHasValidityIsTrue = refl
  ; normalizedAcceptedAuthorityTokenPresent = false
  ; normalizedAcceptedAuthorityTokenPresentIsFalse = refl
  ; intakeAcceptedAuthorityTokenPresent =
      Intake.NumericAuthorityTokenIntakeReceipt.acceptedAuthorityTokenPresent
        Intake.canonicalNumericAuthorityTokenIntakeReceipt
  ; intakeAcceptedAuthorityTokenPresentIsFalse =
      Intake.NumericAuthorityTokenIntakeReceipt.acceptedAuthorityTokenPresentIsFalse
        Intake.canonicalNumericAuthorityTokenIntakeReceipt
  ; normalizedNumericValueLoaded = false
  ; normalizedNumericValueLoadedIsFalse = refl
  ; normalizedNumericValuePromoted = false
  ; normalizedNumericValuePromotedIsFalse = refl
  ; bindingNumericValuePromoted =
      Binding.NumericMeasuredAuthorityBindingReceipt.numericValuePromoted
        Binding.canonicalNumericMeasuredAuthorityBindingReceipt
  ; bindingNumericValuePromotedIsFalse =
      Binding.NumericMeasuredAuthorityBindingReceipt.numericValuePromotedIsFalse
        Binding.canonicalNumericMeasuredAuthorityBindingReceipt
  ; intakeNumericValuePromoted =
      Intake.NumericAuthorityTokenIntakeReceipt.numericValuePromoted
        Intake.canonicalNumericAuthorityTokenIntakeReceipt
  ; intakeNumericValuePromotedIsFalse =
      Intake.NumericAuthorityTokenIntakeReceipt.numericValuePromotedIsFalse
        Intake.canonicalNumericAuthorityTokenIntakeReceipt
  ; obligationNumericValuePromoted =
      Numeric.NumericAndAuthorityObligationIndex.numericValuePromoted
        Numeric.canonicalNumericAndAuthorityObligationIndex
  ; obligationNumericValuePromotedIsFalse =
      Numeric.NumericAndAuthorityObligationIndex.numericValuePromotedIsFalse
        Numeric.canonicalNumericAndAuthorityObligationIndex
  ; falseNumericPromotion = true
  ; falseNumericPromotionIsTrue = refl
  }

canonicalNormalizedMeasuredAuthorityTokenCountIs18 :
  NormalizedMeasuredAuthorityTokenReceipt.normalizedTokenCount
    canonicalNormalizedMeasuredAuthorityTokenReceipt
  ≡ 18
canonicalNormalizedMeasuredAuthorityTokenCountIs18 = refl

canonicalNormalizedCODATATokenCountIs10 :
  NormalizedMeasuredAuthorityTokenReceipt.codataTokenCount
    canonicalNormalizedMeasuredAuthorityTokenReceipt
  ≡ 10
canonicalNormalizedCODATATokenCountIs10 = refl

canonicalNormalizedPDGTokenCountIs5 :
  NormalizedMeasuredAuthorityTokenReceipt.pdgTokenCount
    canonicalNormalizedMeasuredAuthorityTokenReceipt
  ≡ 5
canonicalNormalizedPDGTokenCountIs5 = refl

canonicalNormalizedCODATAPDGTokenCountIs3 :
  NormalizedMeasuredAuthorityTokenReceipt.codataPDGTokenCount
    canonicalNormalizedMeasuredAuthorityTokenReceipt
  ≡ 3
canonicalNormalizedCODATAPDGTokenCountIs3 = refl

canonicalNormalizedMassTokenCountIs6 :
  NormalizedMeasuredAuthorityTokenReceipt.massTokenCount
    canonicalNormalizedMeasuredAuthorityTokenReceipt
  ≡ 6
canonicalNormalizedMassTokenCountIs6 = refl

canonicalNormalizedElectromagneticVacuumTokenCountIs3 :
  NormalizedMeasuredAuthorityTokenReceipt.electromagneticVacuumTokenCount
    canonicalNormalizedMeasuredAuthorityTokenReceipt
  ≡ 3
canonicalNormalizedElectromagneticVacuumTokenCountIs3 = refl

canonicalNormalizedParticleSMTokenCountIs6 :
  NormalizedMeasuredAuthorityTokenReceipt.particleSMTokenCount
    canonicalNormalizedMeasuredAuthorityTokenReceipt
  ≡ 6
canonicalNormalizedParticleSMTokenCountIs6 = refl

canonicalNormalizedRequiredFieldCountIs7 :
  NormalizedMeasuredAuthorityTokenReceipt.requiredFieldCount
    canonicalNormalizedMeasuredAuthorityTokenReceipt
  ≡ 7
canonicalNormalizedRequiredFieldCountIs7 = refl

canonicalNormalizedAcceptedAuthorityTokenPresentIsFalse :
  NormalizedMeasuredAuthorityTokenReceipt.normalizedAcceptedAuthorityTokenPresent
    canonicalNormalizedMeasuredAuthorityTokenReceipt
  ≡ false
canonicalNormalizedAcceptedAuthorityTokenPresentIsFalse = refl

canonicalNormalizedNumericValueLoadedIsFalse :
  NormalizedMeasuredAuthorityTokenReceipt.normalizedNumericValueLoaded
    canonicalNormalizedMeasuredAuthorityTokenReceipt
  ≡ false
canonicalNormalizedNumericValueLoadedIsFalse = refl

canonicalNormalizedNumericValuePromotedIsFalse :
  NormalizedMeasuredAuthorityTokenReceipt.normalizedNumericValuePromoted
    canonicalNormalizedMeasuredAuthorityTokenReceipt
  ≡ false
canonicalNormalizedNumericValuePromotedIsFalse = refl

canonicalNormalizedBindingNumericValuePromotedIsFalse :
  NormalizedMeasuredAuthorityTokenReceipt.bindingNumericValuePromoted
    canonicalNormalizedMeasuredAuthorityTokenReceipt
  ≡ false
canonicalNormalizedBindingNumericValuePromotedIsFalse = refl

canonicalNormalizedIntakeNumericValuePromotedIsFalse :
  NormalizedMeasuredAuthorityTokenReceipt.intakeNumericValuePromoted
    canonicalNormalizedMeasuredAuthorityTokenReceipt
  ≡ false
canonicalNormalizedIntakeNumericValuePromotedIsFalse = refl

canonicalNormalizedObligationNumericValuePromotedIsFalse :
  NormalizedMeasuredAuthorityTokenReceipt.obligationNumericValuePromoted
    canonicalNormalizedMeasuredAuthorityTokenReceipt
  ≡ false
canonicalNormalizedObligationNumericValuePromotedIsFalse = refl

canonicalNormalizedFalseNumericPromotion :
  NormalizedMeasuredAuthorityTokenReceipt.falseNumericPromotion
    canonicalNormalizedMeasuredAuthorityTokenReceipt
  ≡ true
canonicalNormalizedFalseNumericPromotion = refl
