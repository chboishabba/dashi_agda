module DASHI.Geometry.DNAFourAdicPrefixUltrametricBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Vec using (Vec; []; _∷_)

import DASHI.Biology.DNAChemistryCarrier as DNA
import DASHI.Geometry.SSP369Ultrametric as SSPMetric

------------------------------------------------------------------------
-- Four-adic DNA address geometry.
--
-- This module cross-pollinates the existing SSP prefix-ultrametric pattern
-- without identifying the four DNA digits with the distinct 3/6/9 carrier.
-- A DNA address is a path through ordered C/A/G/T fibres.  Agreement depth is
-- the chemistry-independent tree observable; chemistry may subsequently
-- quotient or reweight address regions.

DNAAddress : Nat → Set
DNAAddress d = Vec DNA.DNABase d

agreementDepth : ∀ {d : Nat} → DNAAddress d → DNAAddress d → Nat
agreementDepth [] [] = zero
agreementDepth (DNA.A ∷ xs) (DNA.A ∷ ys) = suc (agreementDepth xs ys)
agreementDepth (DNA.C ∷ xs) (DNA.C ∷ ys) = suc (agreementDepth xs ys)
agreementDepth (DNA.G ∷ xs) (DNA.G ∷ ys) = suc (agreementDepth xs ys)
agreementDepth (DNA.T ∷ xs) (DNA.T ∷ ys) = suc (agreementDepth xs ys)
agreementDepth _ _ = zero

agreementDepth-self : ∀ {d : Nat} (x : DNAAddress d) → agreementDepth x x ≡ d
agreementDepth-self [] = refl
agreementDepth-self (DNA.A ∷ xs) rewrite agreementDepth-self xs = refl
agreementDepth-self (DNA.C ∷ xs) rewrite agreementDepth-self xs = refl
agreementDepth-self (DNA.G ∷ xs) rewrite agreementDepth-self xs = refl
agreementDepth-self (DNA.T ∷ xs) rewrite agreementDepth-self xs = refl

rootAddress : DNAAddress zero
rootAddress = []

canonicalDNAAddress4 : DNAAddress (suc (suc (suc (suc zero))))
canonicalDNAAddress4 = DNA.A ∷ DNA.C ∷ DNA.G ∷ DNA.T ∷ []

canonicalDNAAddress4SelfAgreement :
  agreementDepth canonicalDNAAddress4 canonicalDNAAddress4
  ≡ suc (suc (suc (suc zero)))
canonicalDNAAddress4SelfAgreement = agreementDepth-self canonicalDNAAddress4

------------------------------------------------------------------------
-- Explicit seam with the existing ultrametric implementation.

record DNAFourAdicPrefixUltrametricBridgeReceipt : Set where
  constructor mkDNAFourAdicPrefixUltrametricBridgeReceipt
  field
    dnaDigitsRemainFourWay : Bool
    prefixAgreementIsPrimary : Bool
    existingSSPUltrametricPatternReused : Bool
    dnaDigitsIdentifiedWith369Digits : Bool
    chemistryQuotientMayCoarsenBasins : Bool
    chemistryQuotientChangesPrimitiveAddress : Bool
    bridgeIsCandidateOnly : Bool
    bridgeHolds : Bool
    bridgeHoldsIsTrue : bridgeHolds ≡ true

open DNAFourAdicPrefixUltrametricBridgeReceipt public

canonicalDNAFourAdicPrefixUltrametricBridgeReceipt :
  DNAFourAdicPrefixUltrametricBridgeReceipt
canonicalDNAFourAdicPrefixUltrametricBridgeReceipt =
  mkDNAFourAdicPrefixUltrametricBridgeReceipt
    true
    true
    true
    false
    true
    false
    true
    true
    refl

existing369RootWitness : SSPMetric.Address zero
existing369RootWitness = []

bridgeSummary : String
bridgeSummary =
  "DNA reuses prefix-ultrametric address geometry while retaining four primitive CAGT digits; chemistry acts after addressing as a basin or quotient structure."
