module DASHI.Reasoning.TypedHyperfabricPantsSignatureCompletenessExact where

------------------------------------------------------------------------
-- H2.02: the five *original* typed pants interface coordinates
-- form a necessary AND sufficient matching signature.
--
-- This discharges a source-selection bottleneck: if independent
-- heterogeneous edge-stalk interpretations agree at the *whole*
-- signature, the original InterfaceMatch can be constructed,
-- rather than supplied as an independent opaque theorem.
--
-- Only the five original fields are compared. Boundary names,
-- scale tags, destination basin, receipts and provenance remain
-- independent and are NOT silently identified.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Reasoning.RelationalBranchCobordismGeometry as Pants
import DASHI.Reasoning.TypedHyperfabricPantsNonvacuousSeamQuotientExact as Source

signatureEqualityImpliesInterfaceMatch :
  {left right : Pants.BranchChannel} →
  Source.boundarySignature left ≡ Source.boundarySignature right →
  Pants.InterfaceMatch left right
signatureEqualityImpliesInterfaceMatch match =
  Pants.interfaceMatch
    (cong proj₁ match)
    (cong (λ signature → proj₁ (proj₂ signature)) match)
    (cong
      (λ signature → proj₁ (proj₂ (proj₂ signature))) match)
    (cong
      (λ signature →
        proj₁ (proj₂ (proj₂ (proj₂ signature)))) match)
    (cong
      (λ signature →
        proj₂ (proj₂ (proj₂ (proj₂ signature)))) match)

interfaceMatchImpliesSignatureEquality :
  {left right : Pants.BranchChannel} →
  Pants.InterfaceMatch left right →
  Source.boundarySignature left ≡ Source.boundarySignature right
interfaceMatchImpliesSignatureEquality =
  Source.interfaceMatchImpliesSignatureEquality

-- The original five-field interface and one packed heterogeneous
-- signature admit mutual conversions, without a new postulate.
signatureMatchSound :
  {left right : Pants.BranchChannel} →
  (matched : Pants.InterfaceMatch left right) →
  Source.boundarySignature left ≡ Source.boundarySignature right
signatureMatchSound = interfaceMatchImpliesSignatureEquality

signatureMatchComplete :
  {left right : Pants.BranchChannel} →
  Source.boundarySignature left ≡ Source.boundarySignature right →
  Pants.InterfaceMatch left right
signatureMatchComplete = signatureEqualityImpliesInterfaceMatch

-- A mismatch of the packed signature is enough to refute ANY
-- purported source interface-match certificate.
signatureMismatchBlocksInterfaceMatch :
  {left right : Pants.BranchChannel} →
  ¬ (Source.boundarySignature left ≡ Source.boundarySignature right) →
  ¬ (Pants.InterfaceMatch left right)
signatureMismatchBlocksInterfaceMatch mismatch matched =
  mismatch (signatureMatchSound matched)

-- Existing original donor specializes the equivalence; the
-- source did not need to invent matching field equalities.
selectedOriginalSignatureAgreement :
  Source.boundarySignature Pants.selectedChannel2
  ≡ Source.boundarySignature Pants.innerInputChannel2
selectedOriginalSignatureAgreement =
  signatureMatchSound Pants.outerInnerMatch

selectedOriginalInterfaceFromSignature :
  Pants.InterfaceMatch Pants.selectedChannel2 Pants.innerInputChannel2
selectedOriginalInterfaceFromSignature =
  signatureMatchComplete selectedOriginalSignatureAgreement
