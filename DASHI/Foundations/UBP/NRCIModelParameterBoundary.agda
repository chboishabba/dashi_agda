module DASHI.Foundations.UBP.NRCIModelParameterBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Integer.Base using (ℤ; +0; +[1+_]; -[1+_]; +_)
open import Data.Rational using (ℚ; _+_; _*_; _/_; _<_; 0ℚ)
open import Data.Rational.Base using (mkℚ)
open import Data.Nat.Coprimality as Coprime using ()

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.UBP.ExternalRepositoryProvenance as Provenance

10ℚ : ℚ
10ℚ = + 10 / 1

invℚ : ℚ → ℚ
invℚ (mkℚ +0 d prf) = 0ℚ
invℚ (mkℚ +[1+ n ] d prf) = mkℚ +[1+ d ] n (Coprime.sym prf)
invℚ (mkℚ -[1+ n ] d prf) = mkℚ -[1+ d ] n (Coprime.sym prf)

_÷_ : ℚ → ℚ → ℚ
p ÷ q = p * invℚ q

------------------------------------------------------------------------
-- NRCI normalization parameter boundary.
--
-- The value 10 in the source implementation is a selected model parameter.
-- The equality C_tau(tau) = 1/2 is a normalization law once cancellation for
-- the nonzero parameter is supplied; it is not an independently selected
-- physical phase transition.
------------------------------------------------------------------------

record PositiveModelParameter : Set where
  constructor positiveModelParameter
  field
    tau : ℚ
    tauPositive : 0ℚ < tau
    parameterLabel : String
    sourcePath : String

open PositiveModelParameter public

nrciWith : PositiveModelParameter → ℚ → ℚ
nrciWith parameter tax =
  tau parameter ÷ (tau parameter + tax)

record NRCIHalfThresholdCertificate
    (parameter : PositiveModelParameter) : Set where
  constructor nrciHalfThresholdCertificate
  field
    cancellationReceipt :
      nrciWith parameter (tau parameter) ≡ + 1 / 2
    normalizationReading : String

open NRCIHalfThresholdCertificate public

record NRCIParameterStatus : Set where
  constructor nrciParameterStatus
  field
    repositoryURL : String
    repositoryAuthor : String
    implementationPath : String
    sourceTau : ℚ
    sourceTauIsTen : sourceTau ≡ 10ℚ
    tauIsExplicitModelParameter : Bool
    tauIsExplicitModelParameterIsTrue : tauIsExplicitModelParameter ≡ true
    halfPointIsNormalizationIdentity : Bool
    halfPointIsNormalizationIdentityIsTrue :
      halfPointIsNormalizationIdentity ≡ true
    independentlyEmergentThresholdEstablished : Bool
    independentlyEmergentThresholdEstablishedIsFalse :
      independentlyEmergentThresholdEstablished ≡ false
    genericCancellationImportedHere : Bool
    genericCancellationImportedHereIsFalse :
      genericCancellationImportedHere ≡ false
    reading : String

open NRCIParameterStatus public

canonicalNRCIParameterStatus : NRCIParameterStatus
canonicalNRCIParameterStatus =
  nrciParameterStatus
    Provenance.ubpRepositoryURL
    Provenance.ubpAuthorName
    "core_studio_v4.0/core/ubp_unified_v5.py"
    10ℚ refl
    true refl
    true refl
    false refl
    false refl
    "tau=10 is retained as the attributed UBP model parameter; a generic nonzero-rational cancellation proof remains an explicit certificate"

nrciParameterReceipt : GenericReceipt.GenericReceipt
nrciParameterReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "NRCI model-parameter boundary"
    "DASHI.Foundations.UBP.NRCIModelParameterBoundary"
    "canonicalNRCIParameterStatus"
    "the source value tau=10 is tagged as a model parameter and the half-threshold is exposed as a parameterised normalization certificate"
    "no empirical phase transition, coherence horizon, or physical emergence theorem follows from the algebraic normalization"
    "agda -i . DASHI/Foundations/UBP/NRCIModelParameterBoundary.agda"

nrciParameterReceiptNonPromoting :
  GenericReceipt.promotesClaim nrciParameterReceipt ≡ false
nrciParameterReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse nrciParameterReceipt
