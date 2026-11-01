module DASHI.Core.MultipartSameObjectReconstructionRegression where

open import DASHI.Core.Prelude

import DASHI.Core.MultipartSameObjectReconstructionExact as Multipart

------------------------------------------------------------------------
-- RED regression: a complete two-part package can pay a whole-object relation
-- only when both declared parts are present/admissible and the family carries
-- its compatibility receipt.
------------------------------------------------------------------------

data PartIndex : Set where manifest payload : PartIndex

data Part : Set where manifestPart payloadPart : Part

canonicalParts : PartIndex → Part
canonicalParts manifest = manifestPart
canonicalParts payload = payloadPart

data PartAdmissible : (index : PartIndex) → Part → Set where
  manifestAdmitted : PartAdmissible manifest manifestPart
  payloadAdmitted : PartAdmissible payload payloadPart

data Compatible : (PartIndex → Part) → Set where
  canonicalCompatible : Compatible canonicalParts

data Whole : Set where canonicalArchive : Whole

reconstruct : (PartIndex → Part) → Whole
reconstruct parts = canonicalArchive

SameWhole : Whole → Whole → Set
SameWhole left right = left ≡ right

completeReceipt :
  Multipart.CompleteMultipartReconstruction
    PartAdmissible Compatible reconstruct SameWhole canonicalArchive
completeReceipt = Multipart.complete-multipart-reconstruction
  canonicalParts
  (λ { manifest → manifestAdmitted ; payload → payloadAdmitted })
  canonicalCompatible
  refl

wholeIdentityPaid :
  SameWhole
    (reconstruct (Multipart.parts completeReceipt))
    canonicalArchive
wholeIdentityPaid = Multipart.sameObjectWhole completeReceipt
