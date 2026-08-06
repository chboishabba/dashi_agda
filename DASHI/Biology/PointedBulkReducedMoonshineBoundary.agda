module DASHI.Biology.PointedBulkReducedMoonshineBoundary where

open import DASHI.Core.Prelude

import DASHI.Biology.PointedTernaryBulkExact as Bulk
import DASHI.Biology.ReducedFiftyThreeFibreExact as Reduced
import DASHI.Biology.ReducedFiftyThreeOrbitCandidateExact as Orbit
import DASHI.Biology.SporadicTarotDependencyExact as Tarot

------------------------------------------------------------------------
-- Corrected nested arithmetic:
--
--   196884 = (1 + 9) * 3^9 + 54,
--   196883 = (1 + 9) * 3^9 + 53.
--
-- The bulk now has a concrete marked/unmarked-sheet interpretation.  The 53
-- remains the repository's reduced 6 x 9 fibre.  The equality 53 = 1 + 26 * 2
-- is retained only as a separately typed candidate orbit anatomy.
------------------------------------------------------------------------

fullCoefficientDimension : Nat
fullCoefficientDimension =
  Bulk.pointedBulkDimension + Reduced.fullSixByNineDimension

nontrivialCoefficientDimension : Nat
nontrivialCoefficientDimension =
  Bulk.pointedBulkDimension + Reduced.reducedDimension

fullCoefficientDimensionIs196884 :
  fullCoefficientDimension ≡ 196884
fullCoefficientDimensionIs196884 = refl

nontrivialCoefficientDimensionIs196883 :
  nontrivialCoefficientDimension ≡ 196883
nontrivialCoefficientDimensionIs196883 = refl

fullCoefficientAsPointedBulkPlusInvariantAndReduced :
  fullCoefficientDimension
  ≡ Bulk.pointedBulkDimension
    + Reduced.trivialInvariantDimension
    + Reduced.reducedDimension
fullCoefficientAsPointedBulkPlusInvariantAndReduced = refl

candidateResidualArithmetic : Nat
candidateResidualArithmetic =
  Orbit.fixedPointCount
  + Orbit.orbitIndexCount * Orbit.binaryFibreCount

candidateResidualArithmeticIsFiftyThree :
  candidateResidualArithmetic ≡ 53
candidateResidualArithmeticIsFiftyThree = refl

candidateResidualArithmeticMatchesReducedDimension :
  candidateResidualArithmetic ≡ Reduced.reducedDimension
candidateResidualArithmeticMatchesReducedDimension = refl

record ResidualOrbitCandidateShape : Set where
  constructor residualOrbitCandidateShape
  field
    fixedPoints : Nat
    binaryOrbits : Nat
    binaryOrbitSize : Nat
    total : Nat
    countCertificate :
      fixedPoints + binaryOrbits * binaryOrbitSize ≡ total

open ResidualOrbitCandidateShape public

canonicalResidualOrbitCandidateShape : ResidualOrbitCandidateShape
canonicalResidualOrbitCandidateShape =
  residualOrbitCandidateShape 1 26 2 53 refl

------------------------------------------------------------------------
-- Promotion order.  Later structures cannot be read backwards from a decimal
-- identity.  In particular S26 and its sign character only enter after an
-- independently constructed 26-orbit quotient and a canonical sporadic label.
------------------------------------------------------------------------

data PromotionStage : Set where
  arithmeticCardinalityStage : PromotionStage
  pointedBulkD4ActionStage : PromotionStage
  reducedCarrierEquivalenceStage : PromotionStage
  oneFixedPointInvolutionStage : PromotionStage
  canonicalTwentySixOrbitQuotientStage : PromotionStage
  sporadicOrbitLabellingStage : PromotionStage
  symmetricPermutationActionStage : PromotionStage
  signTwistedModuleStage : PromotionStage
  monsterIntertwinerStage : PromotionStage

nextPromotionStage : PromotionStage → PromotionStage
nextPromotionStage arithmeticCardinalityStage = pointedBulkD4ActionStage
nextPromotionStage pointedBulkD4ActionStage = reducedCarrierEquivalenceStage
nextPromotionStage reducedCarrierEquivalenceStage = oneFixedPointInvolutionStage
nextPromotionStage oneFixedPointInvolutionStage = canonicalTwentySixOrbitQuotientStage
nextPromotionStage canonicalTwentySixOrbitQuotientStage = sporadicOrbitLabellingStage
nextPromotionStage sporadicOrbitLabellingStage = symmetricPermutationActionStage
nextPromotionStage symmetricPermutationActionStage = signTwistedModuleStage
nextPromotionStage signTwistedModuleStage = monsterIntertwinerStage
nextPromotionStage monsterIntertwinerStage = monsterIntertwinerStage

advanceSeven : PromotionStage → PromotionStage
advanceSeven stage =
  nextPromotionStage
    (nextPromotionStage
      (nextPromotionStage
        (nextPromotionStage
          (nextPromotionStage
            (nextPromotionStage
              (nextPromotionStage stage))))))

signTwistOccursSevenPromotionsAfterArithmetic :
  advanceSeven arithmeticCardinalityStage ≡ signTwistedModuleStage
signTwistOccursSevenPromotionsAfterArithmetic = refl

sporadicLabellingPrecedesSymmetricAction :
  nextPromotionStage sporadicOrbitLabellingStage
  ≡ symmetricPermutationActionStage
sporadicLabellingPrecedesSymmetricAction = refl

symmetricActionPrecedesSignTwist :
  nextPromotionStage symmetricPermutationActionStage
  ≡ signTwistedModuleStage
symmetricActionPrecedesSignTwist = refl

------------------------------------------------------------------------
-- Concrete witness types for the missing promotions.  No inhabitant is
-- fabricated by the cardinal identities.
------------------------------------------------------------------------

record SporadicOrbitIdentification : Set where
  constructor sporadicOrbitIdentification
  field
    reducedInvolution : Orbit.ReducedInvolutionWitness
    orbitLabels : Orbit.OrbitLabellingWitness Tarot.SporadicGroup

record SymmetricActionWitness : Set where
  constructor symmetricActionWitness
  field
    sporadicIdentification : SporadicOrbitIdentification
    actionPreservesOrbitLabels : Bool
    actionPreservesOrbitLabelsIsTrue :
      actionPreservesOrbitLabels ≡ true

record SignTwistedModuleWitness : Set where
  constructor signTwistedModuleWitness
  field
    symmetricAction : SymmetricActionWitness
    parityCharacterConstructed : Bool
    parityCharacterConstructedIsTrue :
      parityCharacterConstructed ≡ true
    linearIntertwiningConstructed : Bool
    linearIntertwiningConstructedIsTrue :
      linearIntertwiningConstructed ≡ true

record PointedBulkReducedMoonshineBoundary : Set where
  constructor pointedBulkReducedMoonshineBoundary
  field
    pointedBulkInterpretationIsExact : Bool
    pointedBulkInterpretationIsExactIsTrue :
      pointedBulkInterpretationIsExact ≡ true

    residualFiftyThreeIsExactReducedCarrier : Bool
    residualFiftyThreeIsExactReducedCarrierIsTrue :
      residualFiftyThreeIsExactReducedCarrier ≡ true

    arithmeticTwentySixPairingConstructsInvolution : Bool
    arithmeticTwentySixPairingConstructsInvolutionIsFalse :
      arithmeticTwentySixPairingConstructsInvolution ≡ false

    twentySixOrbitsAreAutomaticallySporadicGroups : Bool
    twentySixOrbitsAreAutomaticallySporadicGroupsIsFalse :
      twentySixOrbitsAreAutomaticallySporadicGroups ≡ false

    S26ActionMayBeReusedWithoutConstruction : Bool
    S26ActionMayBeReusedWithoutConstructionIsFalse :
      S26ActionMayBeReusedWithoutConstruction ≡ false

    signCharacterExistsBeforeSymmetricAction : Bool
    signCharacterExistsBeforeSymmetricActionIsFalse :
      signCharacterExistsBeforeSymmetricAction ≡ false

    coefficientIdentityIsMoonshineRepresentationTheorem : Bool
    coefficientIdentityIsMoonshineRepresentationTheoremIsFalse :
      coefficientIdentityIsMoonshineRepresentationTheorem ≡ false

open PointedBulkReducedMoonshineBoundary public

canonicalPointedBulkReducedMoonshineBoundary :
  PointedBulkReducedMoonshineBoundary
canonicalPointedBulkReducedMoonshineBoundary =
  pointedBulkReducedMoonshineBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
