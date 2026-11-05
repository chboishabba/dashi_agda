module DASHI.Moonshine.Monster3BSuzukiProofRelevantOccurrenceHardeningValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.Monster3BSuzukiProofRelevantOccurrenceHardeningExact as H

_ : H.legacyPairRestrictionObligationProofRelevant H.canonicalBoundary ≡ false
_ = refl

_ : H.legacyMainSplitObligationProofRelevant H.canonicalBoundary ≡ false
_ = refl

_ : H.legacyQuotientDescentObligationProofRelevant H.canonicalBoundary ≡ false
_ = refl

_ : H.legacyMonsterOccurrenceObligationProofRelevant H.canonicalBoundary ≡ false
_ = refl

_ : H.legacyOrientationObligationProofRelevant H.canonicalBoundary ≡ false
_ = refl

_ : H.paidPairFamilyWrapperAvailable H.canonicalBoundary ≡ true
_ = refl

_ : H.paidMainSplitWrapperAvailable H.canonicalBoundary ≡ true
_ = refl

_ : H.paidQuotientDescentWrapperAvailable H.canonicalBoundary ≡ true
_ = refl

_ : H.paidMonsterOccurrenceWrapperAvailable H.canonicalBoundary ≡ true
_ = refl

_ : H.paidWholeSameObjectWrapperAvailable H.canonicalBoundary ≡ true
_ = refl

_ : H.paidIndividualOrientationWrapperAvailable H.canonicalBoundary ≡ true
_ = refl

_ : H.externalGapResultCreatesAgdaProof H.canonicalBoundary ≡ false
_ = refl

_ : H.pairFamilyOccurrenceCreatesIndividualOrientation H.canonicalBoundary ≡ false
_ = refl
