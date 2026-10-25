module DASHI.Cognition.ClinicToStreetsSourceReviewReuseRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Cognition.ClinicToStreetsSourceReviewReuseExact as X

bookCitationDoesNotImportProof :
  Source.citationImportsProof X.clinicBookSource ≡ false
bookCitationDoesNotImportProof =
  Source.citationImportsProofIsFalse X.clinicBookSource

bookCitationDoesNotCreateAuthority :
  Source.citationCreatesAuthority X.clinicBookSource ≡ false
bookCitationDoesNotCreateAuthority =
  Source.citationCreatesAuthorityIsFalse X.clinicBookSource

sourceAtlasDoesNotCreateAuthority :
  Source.atlasCreatesAuthority X.clinicSourceAtlas ≡ false
sourceAtlasDoesNotCreateAuthority =
  Source.atlasCreatesAuthorityIsFalse X.clinicSourceAtlas

familyActivationReviewStillUnpaid :
  X.reviewPaid X.familyActivationReviewDemand ≡ false
familyActivationReviewStillUnpaid = refl

therapyCounterinsurgencyReviewStillUnpaid :
  X.reviewPaid X.therapyCounterinsurgencyReviewDemand ≡ false
therapyCounterinsurgencyReviewStillUnpaid = refl

familyActivationCurrentStateCannotSupplyReviewedClaim :
  X.ReviewedClinicClaim
    X.familyActivationClaimId
    X.familyActivationReviewDemand →
  ⊥
familyActivationCurrentStateCannotSupplyReviewedClaim =
  X.familyActivationCurrentCannotSupplyReviewedClaim

therapyCounterinsurgencyCurrentStateCannotSupplyReviewedClaim :
  X.ReviewedClinicClaim
    X.therapyCounterinsurgencyClaimId
    X.therapyCounterinsurgencyReviewDemand →
  ⊥
therapyCounterinsurgencyCurrentStateCannotSupplyReviewedClaim =
  X.therapyCounterinsurgencyCurrentCannotSupplyReviewedClaim

reviewDoesNotPayCausalIdentification :
  X.ReviewPaymentImpliesCausalIdentification → ⊥
reviewDoesNotPayCausalIdentification =
  X.reviewPaymentDoesNotEstablishCausalIdentification

reviewDoesNotPayClaimTruth :
  X.ReviewPaymentImpliesClaimTruth → ⊥
reviewDoesNotPayClaimTruth =
  X.reviewPaymentDoesNotEstablishClaimTruth
