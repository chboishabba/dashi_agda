module DASHI.Physics.Closure.NSTriadKNTaxKindClassificationRound46Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: William Henry Young.
-- Title: "On the Multiplication of Successions of Fourier Constants".
-- Proceedings of the Royal Society of London. Series A 87 (1912).
-- DOI: 10.1098/rspa.1912.0086.
--
-- DASHI CONTRIBUTION
--
-- Round 45 showed that assigning a provisional eta before inspecting the
-- pre-absorption estimate can hide the real structure of an owner.  Round 46
-- therefore makes tax kind explicit:
--
--   Zero      : the physical owner admits an eta=0 estimate;
--   YoungSoft : the same physical producer yields an estimate at every
--               positive rational split, with eta exactly that split;
--   Hard      : a proved positive floor is part of the physical theorem.
--
-- The classification is intentionally proof-relevant.  In particular Com and
-- kernel are NOT assigned a kind here: their physical pre-absorption estimates
-- must first decide which constructor is justified.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_; _<_)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNHHGoodYoungSoftTaxRound45Exact as Soft

data TaxKind : Set where
  ZeroTax YoungSoftTax HardTax : TaxKind

record ZeroTaxCertificate
    (environment : Owner.TaxEnvironment)
    (selectedOwner : Tax.TaxOwner) : Set where
  field
    estimate : Owner.AdmissibleOwnerEstimate environment
    ownerExact : Owner.owner estimate ≡ selectedOwner
    etaZero : Owner.eta estimate ≡ 0ℚ

open ZeroTaxCertificate public

record HardTaxCertificate
    (environment : Owner.TaxEnvironment)
    (selectedOwner : Tax.TaxOwner) : Set where
  field
    estimate : Owner.AdmissibleOwnerEstimate environment
    ownerExact : Owner.owner estimate ≡ selectedOwner
    floor : ℚ
    floorPositive : 0ℚ < floor
    floorBelowEta : floor ≤ Owner.eta estimate

open HardTaxCertificate public

record TaxClassification
    (environment : Owner.TaxEnvironment)
    (selectedOwner : Tax.TaxOwner) : Set₁ where
  field
    kind : TaxKind
    zeroEvidence : kind ≡ ZeroTax → ZeroTaxCertificate environment selectedOwner
    softEvidence : kind ≡ YoungSoftTax → Soft.YoungSoftOwnerFamily environment selectedOwner
    hardEvidence : kind ≡ HardTax → HardTaxCertificate environment selectedOwner

open TaxClassification public

zeroClassification :
  ∀ {environment selectedOwner} →
  ZeroTaxCertificate environment selectedOwner →
  TaxClassification environment selectedOwner
zeroClassification certificate = record
  { kind = ZeroTax
  ; zeroEvidence = λ _ → certificate
  ; softEvidence = λ ()
  ; hardEvidence = λ ()
  }

youngSoftClassification :
  ∀ {environment selectedOwner} →
  Soft.YoungSoftOwnerFamily environment selectedOwner →
  TaxClassification environment selectedOwner
youngSoftClassification family = record
  { kind = YoungSoftTax
  ; zeroEvidence = λ ()
  ; softEvidence = λ _ → family
  ; hardEvidence = λ ()
  }

hardClassification :
  ∀ {environment selectedOwner} →
  HardTaxCertificate environment selectedOwner →
  TaxClassification environment selectedOwner
hardClassification certificate = record
  { kind = HardTax
  ; zeroEvidence = λ ()
  ; softEvidence = λ ()
  ; hardEvidence = λ _ → certificate
  }

hhGoodClassification :
  ∀ {environment} →
  Soft.YoungSoftOwnerFamily environment Tax.HH-good →
  TaxClassification environment Tax.HH-good
hhGoodClassification = youngSoftClassification

taxKindClassificationLanguageClosed : Bool
taxKindClassificationLanguageClosed = true

comTaxKindRequiresPhysicalPreAbsorptionTheorem : Bool
comTaxKindRequiresPhysicalPreAbsorptionTheorem = true

kernelTaxKindRequiresPhysicalPreAbsorptionTheorem : Bool
kernelTaxKindRequiresPhysicalPreAbsorptionTheorem = true

taxKindClassificationLanguageClosedIsTrue :
  taxKindClassificationLanguageClosed ≡ true
taxKindClassificationLanguageClosedIsTrue = refl
