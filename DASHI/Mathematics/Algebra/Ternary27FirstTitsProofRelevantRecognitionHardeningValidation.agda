module DASHI.Mathematics.Algebra.Ternary27FirstTitsProofRelevantRecognitionHardeningValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Mathematics.Algebra.Ternary27FirstTitsProofRelevantRecognitionHardeningExact as H

legacyFirstTitsStructureStoresObligationTypesOnly :
  H.legacyFirstTitsStructureIsProofRelevant H.canonicalBoundary ≡ false
legacyFirstTitsStructureStoresObligationTypesOnly = refl

legacyKernelApplicationStoresObligationTypesOnly :
  H.legacyKernelApplicationIsProofRelevant H.canonicalBoundary ≡ false
legacyKernelApplicationStoresObligationTypesOnly = refl

paidFirstTitsWrapperAvailable :
  H.paidFirstTitsStructureWrapperAvailable H.canonicalBoundary ≡ true
paidFirstTitsWrapperAvailable = refl

paidKernelApplicationWrapperAvailable :
  H.paidKernelApplicationWrapperAvailable H.canonicalBoundary ≡ true
paidKernelApplicationWrapperAvailable = refl

sourceReceiptAloneDoesNotPayApplication :
  H.classicalSourceReceiptAlonePaysKernelApplication H.canonicalBoundary ≡ false
sourceReceiptAloneDoesNotPayApplication = refl

localPythonAloneDoesNotPayApplication :
  H.localExecutableReceiptAlonePaysKernelApplication H.canonicalBoundary ≡ false
localPythonAloneDoesNotPayApplication = refl
