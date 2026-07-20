module DASHI.Moonshine.ThompsonPenumbralSpecialization where

-- Thompson moonshine is the λ = (-3 , 1) specialization of the penumbral
-- family.  The group identification and the proven existence of the virtual
-- graded module are explicit witnesses; the four-avatar closure adds the
-- product/trace correspondences without identifying the avatars.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Unit using (⊤; tt)
open import DASHI.Moonshine.PenumbralLambency
open import DASHI.Moonshine.PenumbralVectorValuedForm
open import DASHI.Moonshine.PenumbralMoonshineModule
open import DASHI.Moonshine.ThompsonFourAvatarBridge

record ThompsonPenumbralDatum
  (arithmetic : LambencyArithmetic)
  (Discriminant : Set) : Set₁ where
  field
    lambda : PenumbralLambdency arithmetic Discriminant

    IsMinusThree : Discriminant → Set
    IsLevelOne : Lambency arithmetic → Set

    discriminantIsMinusThree :
      IsMinusThree
        (PenumbralLambdency.fundamentalDiscriminant lambda)
    lambencyIsLevelOne :
      IsLevelOne (PenumbralLambdency.lambency lambda)

    ThompsonGroup : Set
    PenumbralGroup : Set
    groupIdentification : PenumbralGroup ≡ ThompsonGroup

record ThompsonPenumbralClosure
  (arithmetic : LambencyArithmetic)
  (Discriminant : Set) : Setω where
  field
    datum : ThompsonPenumbralDatum arithmetic Discriminant

    formCarrier : VectorValuedModularCarrier
    support :
      PenumbralSupport formCarrier arithmetic
        (ThompsonPenumbralDatum.lambda datum)
    identityForm :
      PenumbralForm formCarrier arithmetic
        (ThompsonPenumbralDatum.lambda datum) support

    moduleRealization :
      PenumbralMoonshineRealization formCarrier arithmetic
        (ThompsonPenumbralDatum.lambda datum) support identityForm

    fourAvatars : ThompsonFourAvatarClosure

    realizationUsesThompsonGroup : Set
    identitySeriesIsThompsonSeries : Set

record ThompsonPenumbralBoundary : Set where
  field
    thompsonIsMinusThreeLevelOneCase : ⊤
    halfIntegralModuleExistenceIsProven : ⊤
    fourAvatarRelationsNeedSeparateLiftWitnesses : ⊤
    noClaimEveryPenumbralGroupIsSporadic : ⊤

thompsonPenumbralBoundary : ThompsonPenumbralBoundary
thompsonPenumbralBoundary = record
  { thompsonIsMinusThreeLevelOneCase = tt
  ; halfIntegralModuleExistenceIsProven = tt
  ; fourAvatarRelationsNeedSeparateLiftWitnesses = tt
  ; noClaimEveryPenumbralGroupIsSporadic = tt
  }
