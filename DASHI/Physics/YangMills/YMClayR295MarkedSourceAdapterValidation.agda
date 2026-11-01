module DASHI.Physics.YangMills.YMClayR295MarkedSourceAdapterValidation where

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Physics.YangMills.CompactLieProofLevel using (conditional)

import DASHI.Physics.YangMills.YMClayR295MarkedSourceAdapterExact as Adapter

r295AlreadyBuildsMarkedResponse :
  Adapter.r295BuildsGenericMarkedResponse ≡ true
r295AlreadyBuildsMarkedResponse =
  Adapter.r295BuildsGenericMarkedResponseIsTrue

r295AlreadyBuildsSeparationDecayProducer :
  Adapter.r295BuildsGenericSeparationDecayProducer ≡ true
r295AlreadyBuildsSeparationDecayProducer =
  Adapter.r295BuildsGenericSeparationDecayProducerIsTrue

selectedMarkedDecayIsNotNewF1Leaf :
  Adapter.selectedMarkedDecayRequiresIndependentF1Payment ≡ false
selectedMarkedDecayIsNotNewF1Leaf =
  Adapter.selectedMarkedDecayRequiresIndependentF1PaymentIsFalse

noKernelReceiptMeansAdapterMetadataStaysConditional :
  Adapter.r295MarkedSourceAdapterLevel ≡ conditional
noKernelReceiptMeansAdapterMetadataStaysConditional = refl
