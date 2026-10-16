module DASHI.Physics.CondensedMatter.MATBG2026SourceDataAvailabilityValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.CondensedMatter.MATBG2026SourceDataAvailabilityExact as D

entropy-workbook-count : D.publisherVisibleWorkbookCount D.zhang2026EntropySourceDataAvailability ≡ 4
entropy-workbook-count = refl

qtm-availability-paid : D.qtmDataAvailabilitySourcePaid D.canonicalMATBGSourceDataAvailabilityBoundary ≡ true
qtm-availability-paid = refl

bytes-still-unacquired : D.entropyBytesAcquired D.canonicalMATBGSourceDataAvailabilityBoundary ≡ false
bytes-still-unacquired = refl

same-sample-still-unpaid : D.crossStudySameSamplePaid D.canonicalMATBGSourceDataAvailabilityBoundary ≡ false
same-sample-still-unpaid = refl
