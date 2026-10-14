module DASHI.Moonshine.Monster3BProofRelevantRecognitionHardeningValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.Monster3BProofRelevantRecognitionHardeningExact as Hardening

legacyHZetaStoresObligationTypesOnly :
  Hardening.legacyHZetaRecognitionIsProofRelevant Hardening.canonicalBoundary ≡ false
legacyHZetaStoresObligationTypesOnly = refl

legacyMultiplicityDimensionStoresTypeOnly :
  Hardening.legacyMultiplicityDimensionIsProofRelevant Hardening.canonicalBoundary ≡ false
legacyMultiplicityDimensionStoresTypeOnly = refl

legacyHomIntertwinerStoresTypeOnly :
  Hardening.legacyHomIntertwinerIsProofRelevant Hardening.canonicalBoundary ≡ false
legacyHomIntertwinerStoresTypeOnly = refl

legacyConstituentAttachmentStoresTypeOnly :
  Hardening.legacyConstituentAttachmentIsProofRelevant Hardening.canonicalBoundary ≡ false
legacyConstituentAttachmentStoresTypeOnly = refl

paidHZetaWrapperRequiresWitnesses :
  Hardening.paidHZetaRecognitionWrapperAvailable Hardening.canonicalBoundary ≡ true
paidHZetaWrapperRequiresWitnesses = refl

paidMultiplicityWrapperRequiresWitnesses :
  Hardening.paidMultiplicityRouteWrapperAvailable Hardening.canonicalBoundary ≡ true
paidMultiplicityWrapperRequiresWitnesses = refl

paidConstituentWrapperRequiresWitnesses :
  Hardening.paidConstituentAttachmentWrapperAvailable Hardening.canonicalBoundary ≡ true
paidConstituentWrapperRequiresWitnesses = refl

paidHomWrapperRequiresWitnesses :
  Hardening.paidHomIntertwinerWrapperAvailable Hardening.canonicalBoundary ≡ true
paidHomWrapperRequiresWitnesses = refl

noPromotionFromTypedObligationAlone :
  Hardening.typedObligationAlonePaysRecognition Hardening.canonicalBoundary ≡ false
noPromotionFromTypedObligationAlone = refl
