module DASHI.Biology.IteratedPointedAttachmentSpiralExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Saunders Mac Lane,
-- "Categories for the Working Mathematician", second edition,
-- Springer, 1998.
-- DOI: 10.1007/978-1-4757-4721-8.
--
-- DASHI CONTRIBUTION
--
-- Formalize the mathematical content of the "spiral out of the page"
-- picture: repeated pointed attachment can return to the same projected seam
-- while retaining a strictly different lift/depth coordinate.  The module
-- does not attribute categorical pushouts or this exact construction to any
-- philosophical author; it isolates the reusable finite geometry.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.IndexedJExternalGluingExact as Gluing

data LiftedSeam : Set where
  seamDepth0 seamDepth1 seamDepth2 : LiftedSeam

projectSeam : LiftedSeam → Gluing.NineRing0
projectSeam seamDepth0 = Gluing.r0
projectSeam seamDepth1 = Gluing.r0
projectSeam seamDepth2 = Gluing.r0

seamDepth : LiftedSeam → Nat
seamDepth seamDepth0 = 0
seamDepth seamDepth1 = 1
seamDepth seamDepth2 = 2

allSeamsProjectTogether01 :
  projectSeam seamDepth0 ≡ projectSeam seamDepth1
allSeamsProjectTogether01 = refl

allSeamsProjectTogether12 :
  projectSeam seamDepth1 ≡ projectSeam seamDepth2
allSeamsProjectTogether12 = refl

depthZeroAndOneDistinct : seamDepth0 ≡ seamDepth1 → ⊥
depthZeroAndOneDistinct ()

depthOneAndTwoDistinct : seamDepth1 ≡ seamDepth2 → ⊥
depthOneAndTwoDistinct ()

data SpiralAddress : Set where
  address0 address1 address10 address11 : SpiralAddress

projectAddress : SpiralAddress → Gluing.NineRing0
projectAddress address0 = Gluing.r0
projectAddress address1 = Gluing.r0
projectAddress address10 = Gluing.r0
projectAddress address11 = Gluing.r1

addressDepth : SpiralAddress → Nat
addressDepth address0 = 0
addressDepth address1 = 1
addressDepth address10 = 1
addressDepth address11 = 2

addressIndex : SpiralAddress → Nat
addressIndex address0 = 0
addressIndex address1 = 1
addressIndex address10 = 10
addressIndex address11 = 11

zeroOneProjectedSeam : projectAddress address0 ≡ projectAddress address1
zeroOneProjectedSeam = refl

oneTenProjectedSeam : projectAddress address1 ≡ projectAddress address10
oneTenProjectedSeam = refl

oneTenRetainSameLiftDepth : addressDepth address1 ≡ addressDepth address10
oneTenRetainSameLiftDepth = refl

tenElevenAdvanceDepth : addressDepth address11 ≡ addressDepth address10 + 1
tenElevenAdvanceDepth = refl

tenIsOneAfterHostWidth :
  addressIndex address10 ≡ addressIndex address1 + Gluing.hostTransportWidth
tenIsOneAfterHostWidth = refl

elevenIsNextLocalAddress :
  addressIndex address11 ≡ addressIndex address10 + 1
elevenIsNextLocalAddress = refl

record AttachmentStage : Set where
  constructor attachmentStage
  field
    previousDepth : Nat
    importedBundleDepth : Nat
    resultingDepth : Nat
    depthAccumulation :
      resultingDepth ≡ previousDepth + importedBundleDepth

open AttachmentStage public

firstAttachment : AttachmentStage
firstAttachment = attachmentStage 0 1 1 refl

secondAttachment : AttachmentStage
secondAttachment = attachmentStage 1 1 2 refl

record SpiralAttachmentBoundary : Set where
  constructor spiralAttachmentBoundary
  field
    sameProjectionImpliesSameLift : Bool
    sameProjectionImpliesSameLiftIsFalse :
      sameProjectionImpliesSameLift ≡ false
    attachmentRetainsDepthHistory : Bool
    attachmentRetainsDepthHistoryIsTrue :
      attachmentRetainsDepthHistory ≡ true
    finiteModelProvesUniversalPushout : Bool
    finiteModelProvesUniversalPushoutIsFalse :
      finiteModelProvesUniversalPushout ≡ false
    formalismIsAttributedToMarx : Bool
    formalismIsAttributedToMarxIsFalse :
      formalismIsAttributedToMarx ≡ false

canonicalSpiralAttachmentBoundary : SpiralAttachmentBoundary
canonicalSpiralAttachmentBoundary =
  spiralAttachmentBoundary false refl true refl false refl false refl
