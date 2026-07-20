module DASHI.Moonshine.ThompsonFourAvatarBridge where

-- The Thompson case carries four related moonshine avatars: two in weight
-- one-half and two in weight zero.  Singular-theta/Borcherds constructions run
-- from half-integral weight to weight zero; traces of singular moduli provide
-- a distinct reverse arithmetic correspondence.  Neither direction is treated
-- as an automatic equivalence.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Unit using (⊤; tt)
open import DASHI.Moonshine.SingularThetaBorcherdsBridge

data ThompsonAvatar : Set where
  generalizedMonsterWeightZero : ThompsonAvatar
  classicalThompsonWeightHalf : ThompsonAvatar
  penumbralThompsonWeightZero : ThompsonAvatar
  penumbralThompsonWeightHalf : ThompsonAvatar

record ThompsonAvatarObject : Set₁ where
  field
    Object : ThompsonAvatar → Set

record ThompsonBorcherdsArrows
  (objects : ThompsonAvatarObject) : Set₁ where
  field
    classicalHalfToGeneralizedZero :
      ThompsonAvatarObject.Object objects classicalThompsonWeightHalf →
      ThompsonAvatarObject.Object objects generalizedMonsterWeightZero

    penumbralHalfToPenumbralZero :
      ThompsonAvatarObject.Object objects penumbralThompsonWeightHalf →
      ThompsonAvatarObject.Object objects penumbralThompsonWeightZero

    ClassicalBorcherdsCorrect : Set
    PenumbralBorcherdsCorrect : Set
    classicalBorcherdsCorrect : ClassicalBorcherdsCorrect
    penumbralBorcherdsCorrect : PenumbralBorcherdsCorrect

record ThompsonSingularModuliArrows
  (objects : ThompsonAvatarObject) : Set₁ where
  field
    generalizedZeroToPenumbralHalf :
      ThompsonAvatarObject.Object objects generalizedMonsterWeightZero →
      ThompsonAvatarObject.Object objects penumbralThompsonWeightHalf

    penumbralZeroToClassicalHalf :
      ThompsonAvatarObject.Object objects penumbralThompsonWeightZero →
      ThompsonAvatarObject.Object objects classicalThompsonWeightHalf

    TraceOfSingularModuliCorrect : ThompsonAvatar → Set
    generalizedTraceCorrect :
      TraceOfSingularModuliCorrect generalizedMonsterWeightZero
    penumbralTraceCorrect :
      TraceOfSingularModuliCorrect penumbralThompsonWeightZero

record ThompsonRegularityRestriction : Set₁ where
  field
    ThompsonElement : Set
    ThreeRegular : ThompsonElement → Set
    CorrespondenceVerifiedOn : ThompsonElement → Set

    threeRegularIncluded :
      (g : ThompsonElement) →
      ThreeRegular g →
      CorrespondenceVerifiedOn g

record ThompsonFourAvatarClosure : Setω where
  field
    objects : ThompsonAvatarObject
    borcherdsArrows : ThompsonBorcherdsArrows objects
    singularModuliArrows : ThompsonSingularModuliArrows objects
    regularity : ThompsonRegularityRestriction

    SameFiniteGroupAction : ThompsonAvatar → Set
    sameThompsonAction :
      (avatar : ThompsonAvatar) →
      SameFiniteGroupAction avatar

record ThompsonFourAvatarBoundary : Set where
  field
    fourAvatarsAreDistinctObjects : ⊤
    borcherdsAndTraceArrowsAreDifferentConstructions : ⊤
    arrowsDoNotSupplyMutualInverseProofs : ⊤
    regularityRestrictionsMustBeTracked : ⊤
    noUniversalPenumbralGeneralizedCorrespondenceClaim : ⊤

thompsonFourAvatarBoundary : ThompsonFourAvatarBoundary
thompsonFourAvatarBoundary = record
  { fourAvatarsAreDistinctObjects = tt
  ; borcherdsAndTraceArrowsAreDifferentConstructions = tt
  ; arrowsDoNotSupplyMutualInverseProofs = tt
  ; regularityRestrictionsMustBeTracked = tt
  ; noUniversalPenumbralGeneralizedCorrespondenceClaim = tt
  }
