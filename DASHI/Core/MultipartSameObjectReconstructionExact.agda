module DASHI.Core.MultipartSameObjectReconstructionExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- COMPLETE MULTIPART SAME-OBJECT RECONSTRUCTION
--
-- A conclusion-paying whole reconstruction requires a complete declared part
-- family, a proof that every declared part is admissible for its index/role,
-- a compatibility receipt for the whole family, and an explicit same-object
-- relation between the reconstructed whole and the expected whole.
--
-- The same-object relation is parameterized deliberately: some domains pay it
-- by literal equality, others by a governed digest/identity relation.  Merely
-- acquiring some pieces, matching local names, or possessing a reconstruction
-- algorithm does not inhabit this record.
------------------------------------------------------------------------

record CompleteMultipartReconstruction
    {Index Part Whole : Set}
    (PartAdmissible : Index → Part → Set)
    (Compatible : (Index → Part) → Set)
    (reconstruct : (Index → Part) → Whole)
    (SameObject : Whole → Whole → Set)
    (expectedWhole : Whole) : Set₁ where
  constructor complete-multipart-reconstruction
  field
    parts : Index → Part
    everyPartAdmissible :
      (index : Index) → PartAdmissible index (parts index)
    compatibleFamily : Compatible parts
    sameObjectWhole : SameObject (reconstruct parts) expectedWhole

open CompleteMultipartReconstruction public

------------------------------------------------------------------------
-- Boundary: completeness/compatibility/identity/custody remain different
-- obligations. Acquisition chronology belongs to append-only provenance and is
-- intentionally not encoded as part of the mathematical reconstruction record.
------------------------------------------------------------------------

record MultipartReconstructionBoundary : Set where
  constructor multipart-reconstruction-boundary
  field
    everyDeclaredPartRequired : Bool
    everyDeclaredPartRequiredIsTrue : everyDeclaredPartRequired ≡ true

    compatibilityRequiredSeparately : Bool
    compatibilityRequiredSeparatelyIsTrue :
      compatibilityRequiredSeparately ≡ true

    wholeSameObjectReceiptRequiredSeparately : Bool
    wholeSameObjectReceiptRequiredSeparatelyIsTrue :
      wholeSameObjectReceiptRequiredSeparately ≡ true

    localPartIdentityAloneCreatesWholeIdentity : Bool
    localPartIdentityAloneCreatesWholeIdentityIsFalse :
      localPartIdentityAloneCreatesWholeIdentity ≡ false

    reconstructionCreatesHistoricalCustody : Bool
    reconstructionCreatesHistoricalCustodyIsFalse :
      reconstructionCreatesHistoricalCustody ≡ false

    acquisitionOrderDeterminesWholeIdentity : Bool
    acquisitionOrderDeterminesWholeIdentityIsFalse :
      acquisitionOrderDeterminesWholeIdentity ≡ false

canonicalMultipartReconstructionBoundary : MultipartReconstructionBoundary
canonicalMultipartReconstructionBoundary =
  multipart-reconstruction-boundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
