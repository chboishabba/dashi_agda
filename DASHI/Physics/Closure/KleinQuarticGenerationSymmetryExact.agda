module DASHI.Physics.Closure.KleinQuarticGenerationSymmetryExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Closure.KleinQuarticQMReceipt as Klein

------------------------------------------------------------------------
-- Exact finite symmetry theorem behind the open Klein-quartic generation
-- assignment.  Three factors supply three slots, but the full permutation
-- symmetry has no globally fixed selected slot.  A physical generation label
-- therefore needs symmetry-breaking or additional equivariant data; factor
-- count alone cannot provide a canonical selector.
------------------------------------------------------------------------

data Factor3 : Set where
  factorA factorB factorC : Factor3

swapAB : Factor3 → Factor3
swapAB factorA = factorB
swapAB factorB = factorA
swapAB factorC = factorC

swapBC : Factor3 → Factor3
swapBC factorA = factorA
swapBC factorB = factorC
swapBC factorC = factorB

swapABInvolutive :
  (factor : Factor3) →
  swapAB (swapAB factor) ≡ factor
swapABInvolutive factorA = refl
swapABInvolutive factorB = refl
swapABInvolutive factorC = refl

swapBCInvolutive :
  (factor : Factor3) →
  swapBC (swapBC factor) ≡ factor
swapBCInvolutive factorA = refl
swapBCInvolutive factorB = refl
swapBCInvolutive factorC = refl

FullySymmetricSelectedFactor : Set
FullySymmetricSelectedFactor =
  Σ Factor3
    (λ factor →
      swapAB factor ≡ factor
      × swapBC factor ≡ factor)

noFullySymmetricSelectedFactor :
  FullySymmetricSelectedFactor → ⊥
noFullySymmetricSelectedFactor (factorA , (swapABFixed , swapBCFixed))
  with swapABFixed
... | ()
noFullySymmetricSelectedFactor (factorB , (swapABFixed , swapBCFixed))
  with swapABFixed
... | ()
noFullySymmetricSelectedFactor (factorC , (swapABFixed , swapBCFixed))
  with swapBCFixed
... | ()

factorCountDoesNotSupplyCanonicalSelector :
  FullySymmetricSelectedFactor → ⊥
factorCountDoesNotSupplyCanonicalSelector =
  noFullySymmetricSelectedFactor

receiptStillMarksSymmetryBreakingOpen :
  Klein.symmetryBreakingMechanismOpen
    Klein.canonicalKleinQuarticQMReceipt
  ≡ true
receiptStillMarksSymmetryBreakingOpen = refl

receiptStillBlocksPhysicalCKMPromotion :
  Klein.physicalCKMPromoted
    Klein.canonicalKleinQuarticQMReceipt
  ≡ false
receiptStillBlocksPhysicalCKMPromotion = refl

record ThreeFactorGenerationBoundary : Set where
  constructor threeFactorGenerationBoundary
  field
    factorCarrier : Set
    firstTransposition : factorCarrier → factorCarrier
    secondTransposition : factorCarrier → factorCarrier
    noCommonFixedSelector :
      Σ factorCarrier
        (λ factor →
          firstTransposition factor ≡ factor
          × secondTransposition factor ≡ factor)
      → ⊥
    threeFactorsExist : Bool
    threeFactorsExistIsTrue : threeFactorsExist ≡ true
    canonicalGenerationSelectorExists : Bool
    canonicalGenerationSelectorExistsIsFalse :
      canonicalGenerationSelectorExists ≡ false

canonicalThreeFactorGenerationBoundary :
  ThreeFactorGenerationBoundary
canonicalThreeFactorGenerationBoundary =
  threeFactorGenerationBoundary
    Factor3
    swapAB
    swapBC
    noFullySymmetricSelectedFactor
    true refl
    false refl
