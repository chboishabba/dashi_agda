module DASHI.Foundations.UBP.NRCIModelParameterBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Rational using (ℚ; _+_; _/_; _<_; 0ℚ)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.UBP.ExternalRepositoryProvenance as Provenance

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
  tau parameter / (tau parameter + tax)

record NRCIHalfThresholdCertificate
    (parameter : PositiveModelParameter) : Set where
  constructor nrciHalfThresholdCertificate
  field
    cancellationReceipt :
      nrciWith parameter (tau parameter) ≡ 1 / 2
    normalizationReading : String

open NRCIHalfThresholdCertificate public

record NRCIParameterStatus : Set where
  constructor nrciParameterStatus
  field
    repositoryURL : String
    repositoryAuthor : String
    implementationPath : String
    sourceTau : ℚ
    sourceTauIsTen : sourceTau ≡ 10
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
    10 refl
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
