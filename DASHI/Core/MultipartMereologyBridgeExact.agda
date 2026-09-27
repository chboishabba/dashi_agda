{-# OPTIONS --safe #-}
module DASHI.Core.MultipartMereologyBridgeExact where

open import Agda.Primitive using (Set₁)
import DASHI.Core.MultipartSameObjectReconstructionExact as Multipart

------------------------------------------------------------------------
-- COMPLETE MULTIPART RECONSTRUCTION AS A MEREOLOGICAL FUSION RECEIPT
------------------------------------------------------------------------

record CompleteFusionReceipt
    {Index Part Whole : Set}
    (PartAdmissible : Index → Part → Set)
    (Compatible : (Index → Part) → Set)
    (reconstruct : (Index → Part) → Whole)
    (SameObject : Whole → Whole → Set)
    (expectedWhole : Whole) : Set₁ where
  constructor complete-fusion-receipt
  field
    parts :
      Index → Part

    everyPartAdmissible :
      (i : Index) → PartAdmissible i (parts i)

    compatibleFamily :
      Compatible parts

    fusedWhole :
      Whole

    fusedWholeIsReconstruction :
      SameObject fusedWhole (reconstruct parts)

    fusedWholeIsExpectedWhole :
      SameObject fusedWhole expectedWhole

open CompleteFusionReceipt public

fromCompleteMultipartReconstruction :
  ∀ {Index Part Whole}
    {PartAdmissible : Index → Part → Set}
    {Compatible : (Index → Part) → Set}
    {reconstruct : (Index → Part) → Whole}
    {SameObject : Whole → Whole → Set}
    {expectedWhole : Whole} →
  ((w : Whole) → SameObject w w) →
  ((a b c : Whole) → SameObject a b → SameObject a c → SameObject b c) →
  Multipart.CompleteMultipartReconstruction
    PartAdmissible Compatible reconstruct SameObject expectedWhole →
  CompleteFusionReceipt
    PartAdmissible Compatible reconstruct SameObject expectedWhole
fromCompleteMultipartReconstruction
    sameRefl
    sameCancel
    reconstruction =
  complete-fusion-receipt
    (Multipart.parts reconstruction)
    (Multipart.everyPartAdmissible reconstruction)
    (Multipart.compatibleFamily reconstruction)
    (reconstruct (Multipart.parts reconstruction))
    (sameRefl (reconstruct (Multipart.parts reconstruction)))
    (sameCancel
      (reconstruct (Multipart.parts reconstruction))
      (reconstruct (Multipart.parts reconstruction))
      expectedWhole
      (sameRefl (reconstruct (Multipart.parts reconstruction)))
      (Multipart.sameObjectWhole reconstruction))
