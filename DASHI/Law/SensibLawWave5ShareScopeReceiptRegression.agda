module DASHI.Law.SensibLawWave5ShareScopeReceiptRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawWave5ShareScopeReceiptExact as S

reviewAndShareRemainDistinct :
  S.reviewAndShareAreDistinct
    S.canonicalWave5ShareScopeBoundary
  ≡ true
reviewAndShareRemainDistinct = refl

unreviewedRowsRemainBlocked :
  S.unreviewedRowsCannotBeAllowed
    S.canonicalWave5ShareScopeBoundary
  ≡ true
unreviewedRowsRemainBlocked = refl

therapistStillNeedsSeparateScope :
  S.reviewedTherapistRequiresSeparateScope
    S.canonicalWave5ShareScopeBoundary
  ≡ true
therapistStillNeedsSeparateScope = refl

testOnlyDistinctFibresRemainAvailable :
  S.testOnlyDistinctFibresExist
    S.canonicalWave5ShareScopeBoundary
  ≡ true
testOnlyDistinctFibresRemainAvailable = refl

scopeStillDoesNotCreateAuthority :
  S.scopeCreatesSemanticAuthority
    S.canonicalWave5ShareScopeBoundary
  ≡ false
scopeStillDoesNotCreateAuthority = refl

scopeStillDoesNotCreateTruth :
  S.scopeCreatesClaimTruth
    S.canonicalWave5ShareScopeBoundary
  ≡ false
scopeStillDoesNotCreateTruth = refl

clinicStillCannotBecomeProfessionalPayment :
  S.Included S.clinicLetter S.lawyer → ⊥
clinicStillCannotBecomeProfessionalPayment =
  S.clinicCannotBeIncluded

journalStillCannotBecomeProfessionalPayment :
  S.Included S.userJournalAccount S.lawyer → ⊥
journalStillCannotBecomeProfessionalPayment =
  S.journalCannotBeIncluded
