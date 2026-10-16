module DASHI.Biology.KitzerowBH4StrictEvidenceBindingValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import DASHI.Biology.KitzerowBH4StrictEvidenceBindingExact as B

cacoRateCannotPayTargetNeuralFlux :
  B.cacoRatePaysOnlyCacoEstimand B.canonicalBH4StrictBindingBoundary ≡ true
  × B.cacoRatePaysTargetNeuralDonorRecipientFlux B.canonicalBH4StrictBindingBoundary ≡ false
cacoRateCannotPayTargetNeuralFlux = refl , refl

separateTHAndTPHStudiesDoNotPaySimultaneousAllocation :
  B.thResponsePaidInItsEstimand B.canonicalBH4StrictBindingBoundary ≡ true
  × B.tphResponsePaidInItsEstimand B.canonicalBH4StrictBindingBoundary ≡ true
  × B.separateBranchStudiesPaySameObjectSimultaneousAllocation B.canonicalBH4StrictBindingBoundary ≡ false
separateTHAndTPHStudiesDoNotPaySimultaneousAllocation = refl , (refl , refl)

sameClaimLabelDoesNotEraseEstimandScope :
  B.sameClaimLabelErasesEstimandScope B.canonicalBH4StrictBindingBoundary ≡ false
sameClaimLabelDoesNotEraseEstimandScope = refl

strictBindingsDoNotCloseWholeAllocator :
  B.strictBindingsCloseWholeAllocator B.canonicalBH4StrictBindingBoundary ≡ false
strictBindingsDoNotCloseWholeAllocator = refl
