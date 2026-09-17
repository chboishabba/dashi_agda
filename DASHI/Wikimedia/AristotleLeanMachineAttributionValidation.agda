module DASHI.Wikimedia.AristotleLeanMachineAttributionValidation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.AttributedSourceCore as Source
open import DASHI.Wikimedia.AristotleLeanMachineAttributionExact

_ : Source.doiState jmdLeanArchiveSource ≡ Source.noDOIRecordedByAtlas
_ = refl

_ : Source.citationImportsProof jmdLeanArchiveSource ≡ false
_ = refl

_ : Source.citationCreatesAuthority jmdLeanArchiveSource ≡ false
_ = refl

_ : archiveIdentityPreserved jmdLeanArchiveAttributionReceipt ≡ true
_ = refl

_ : archiveDigestPreserved jmdLeanArchiveAttributionReceipt ≡ true
_ = refl

_ : archiveActsAsLiveWikidataAuthority jmdLeanArchiveAttributionReceipt ≡ false
_ = refl

_ : archiveLeanProofBecomesAgdaProof jmdLeanArchiveAttributionReceipt ≡ false
_ = refl
