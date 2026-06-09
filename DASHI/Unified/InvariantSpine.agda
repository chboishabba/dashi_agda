module DASHI.Unified.InvariantSpine where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.PNFRoleVectorAlgebra as Role
import DASHI.Interop.SensibLawResidualLattice as Residual
import DASHI.Interop.UnifiedMathLanguageAssertedProofs as Asserted
import DASHI.Interop.UnifiedMathLanguageSpine as Unified

------------------------------------------------------------------------
-- Unified object invariant interface.
--
-- Every facade object exposes the same spine:
--
--   observation -> projection -> carrier/role vector -> residual
--   -> proof posture -> invariant posture -> formal projection bundle
--
-- The j-projection axis was the first example.  The invariant spine now
-- records the broader rule: every DASHI-encoded facade object gets the parent
-- family of formal projections, while each projection carries its own
-- authority status and non-promotion proof.

data InvariantStrength : Set where
  stronglyInvariant : InvariantStrength
  softInvariant : InvariantStrength
  blockedInvariant : InvariantStrength

data JProjectionStatus : Set where
  literalModularJ : JProjectionStatus
  softJInvariant : JProjectionStatus
  blockedJInvariant : JProjectionStatus

data UniversalProjectionKind : Set where
  modularJProjectionKind : UniversalProjectionKind
  heckeProjectionKind : UniversalProjectionKind
  bottProjectionKind : UniversalProjectionKind
  kolmogorovProjectionKind : UniversalProjectionKind
  categoryProjectionKind : UniversalProjectionKind
  quotientProjectionKind : UniversalProjectionKind
  latticeProjectionKind : UniversalProjectionKind
  operatorProjectionKind : UniversalProjectionKind

data UniversalProjectionStatus : Set where
  literalProjection : UniversalProjectionStatus
  softProjection : UniversalProjectionStatus
  blockedProjection : UniversalProjectionStatus

projectionCarrier : UniversalProjectionKind → Unified.LanguageCarrier
projectionCarrier modularJProjectionKind =
  Unified.jInvariantCarrier
projectionCarrier heckeProjectionKind =
  Unified.heckeCarrier
projectionCarrier bottProjectionKind =
  Unified.bottCarrier
projectionCarrier kolmogorovProjectionKind =
  Unified.kolmogorovCarrier
projectionCarrier categoryProjectionKind =
  Unified.categoryCarrier
projectionCarrier quotientProjectionKind =
  Unified.quotientCarrier
projectionCarrier latticeProjectionKind =
  Unified.latticeCarrier
projectionCarrier operatorProjectionKind =
  Unified.operatorCarrier

record UniversalProjection (kind : UniversalProjectionKind) : Set where
  constructor universalProjection
  field
    status :
      UniversalProjectionStatus

    carrier :
      Unified.LanguageCarrier

    carrierIsCanonical :
      carrier ≡ projectionCarrier kind

    label :
      String

    externalPromotion :
      Bool

    externalPromotionIsFalse :
      externalPromotion ≡ false

open UniversalProjection public

softUniversalProjection :
  (kind : UniversalProjectionKind) →
  String →
  UniversalProjection kind
softUniversalProjection kind label =
  universalProjection
    softProjection
    (projectionCarrier kind)
    refl
    label
    false
    refl

literalUniversalProjection :
  (kind : UniversalProjectionKind) →
  String →
  UniversalProjection kind
literalUniversalProjection kind label =
  universalProjection
    literalProjection
    (projectionCarrier kind)
    refl
    label
    false
    refl

blockedUniversalProjection :
  (kind : UniversalProjectionKind) →
  String →
  UniversalProjection kind
blockedUniversalProjection kind label =
  universalProjection
    blockedProjection
    (projectionCarrier kind)
    refl
    label
    false
    refl

record FormalProjectionBundle : Set where
  constructor formalProjectionBundle
  field
    modularJ :
      UniversalProjection modularJProjectionKind

    hecke :
      UniversalProjection heckeProjectionKind

    bott :
      UniversalProjection bottProjectionKind

    kolmogorov :
      UniversalProjection kolmogorovProjectionKind

    category :
      UniversalProjection categoryProjectionKind

    quotient :
      UniversalProjection quotientProjectionKind

    lattice :
      UniversalProjection latticeProjectionKind

    operator :
      UniversalProjection operatorProjectionKind

open FormalProjectionBundle public

softFormalProjectionBundle : String → FormalProjectionBundle
softFormalProjectionBundle label =
  formalProjectionBundle
    (softUniversalProjection modularJProjectionKind label)
    (softUniversalProjection heckeProjectionKind label)
    (softUniversalProjection bottProjectionKind label)
    (softUniversalProjection kolmogorovProjectionKind label)
    (softUniversalProjection categoryProjectionKind label)
    (softUniversalProjection quotientProjectionKind label)
    (softUniversalProjection latticeProjectionKind label)
    (softUniversalProjection operatorProjectionKind label)

blockedFormalProjectionBundle : String → FormalProjectionBundle
blockedFormalProjectionBundle label =
  formalProjectionBundle
    (blockedUniversalProjection modularJProjectionKind label)
    (blockedUniversalProjection heckeProjectionKind label)
    (blockedUniversalProjection bottProjectionKind label)
    (blockedUniversalProjection kolmogorovProjectionKind label)
    (blockedUniversalProjection categoryProjectionKind label)
    (blockedUniversalProjection quotientProjectionKind label)
    (blockedUniversalProjection latticeProjectionKind label)
    (blockedUniversalProjection operatorProjectionKind label)

arithmeticMoonshineProjectionBundle : String → FormalProjectionBundle
arithmeticMoonshineProjectionBundle label =
  formalProjectionBundle
    (literalUniversalProjection modularJProjectionKind label)
    (literalUniversalProjection heckeProjectionKind label)
    (softUniversalProjection bottProjectionKind label)
    (softUniversalProjection kolmogorovProjectionKind label)
    (softUniversalProjection categoryProjectionKind label)
    (softUniversalProjection quotientProjectionKind label)
    (softUniversalProjection latticeProjectionKind label)
    (softUniversalProjection operatorProjectionKind label)

projectionExternalPromotion :
  ∀ {kind} → UniversalProjection kind → Bool
projectionExternalPromotion projection =
  UniversalProjection.externalPromotion projection

projectionExternalPromotionIsFalse :
  ∀ {kind} →
  (projection : UniversalProjection kind) →
  projectionExternalPromotion projection ≡ false
projectionExternalPromotionIsFalse projection =
  UniversalProjection.externalPromotionIsFalse projection

bundleExternalPromotionIsFalse :
  FormalProjectionBundle → UniversalProjectionKind → Bool
bundleExternalPromotionIsFalse bundle modularJProjectionKind =
  projectionExternalPromotion (modularJ bundle)
bundleExternalPromotionIsFalse bundle heckeProjectionKind =
  projectionExternalPromotion (hecke bundle)
bundleExternalPromotionIsFalse bundle bottProjectionKind =
  projectionExternalPromotion (bott bundle)
bundleExternalPromotionIsFalse bundle kolmogorovProjectionKind =
  projectionExternalPromotion (kolmogorov bundle)
bundleExternalPromotionIsFalse bundle categoryProjectionKind =
  projectionExternalPromotion (category bundle)
bundleExternalPromotionIsFalse bundle quotientProjectionKind =
  projectionExternalPromotion (quotient bundle)
bundleExternalPromotionIsFalse bundle latticeProjectionKind =
  projectionExternalPromotion (lattice bundle)
bundleExternalPromotionIsFalse bundle operatorProjectionKind =
  projectionExternalPromotion (operator bundle)

record JProjection : Set where
  constructor mkJProjection
  field
    status :
      JProjectionStatus

    label :
      String

    externalPromotion :
      Bool

    externalPromotionIsFalse :
      externalPromotion ≡ false

open JProjection public

jProjectionCarrier : JProjection → Unified.LanguageCarrier
jProjectionCarrier _ =
  Unified.jInvariantCarrier

literalModularJProjection : String → JProjection
literalModularJProjection label =
  mkJProjection
    literalModularJ
    label
    false
    refl

softJProjection : String → JProjection
softJProjection label =
  mkJProjection
    softJInvariant
    label
    false
    refl

blockedJProjection : String → JProjection
blockedJProjection label =
  mkJProjection
    blockedJInvariant
    label
    false
    refl

record UnifiedObjectInvariant : Set where
  constructor unifiedObjectInvariant
  field
    objectName :
      String

    lane :
      Unified.DomainLane

    observation :
      String

    projection :
      String

    carrier :
      Unified.LanguageCarrier

    roleVector :
      Role.RoleVector

    residual :
      Residual.ResidualLevel

    proofPosture :
      Asserted.ProofPosture

    invariantStrength :
      InvariantStrength

    jProjection :
      JProjection

    formalProjections :
      FormalProjectionBundle

open UnifiedObjectInvariant public

objectExternalJPromotion : UnifiedObjectInvariant → Bool
objectExternalJPromotion object =
  JProjection.externalPromotion (jProjection object)

objectProjectionPromotion :
  UnifiedObjectInvariant → UniversalProjectionKind → Bool
objectProjectionPromotion object =
  bundleExternalPromotionIsFalse (formalProjections object)

objectExternalJPromotionIsFalse :
  ∀ object →
  objectExternalJPromotion object ≡ false
objectExternalJPromotionIsFalse object =
  JProjection.externalPromotionIsFalse (jProjection object)

defaultRoleVector : String → Role.RoleVector
defaultRoleVector label =
  Role.roleVector
    (Role.observedRole label)
    (Role.observedRole "project")
    (Role.observedRole "carrier")
    (Role.observedRole "residual")
    (Role.observedRole "non-promotion")
    (Role.observedRole "facade")

canonicalInvariantObjectsHaveJProjection :
  ∀ object →
  jProjectionCarrier (jProjection object) ≡ Unified.jInvariantCarrier
canonicalInvariantObjectsHaveJProjection object =
  refl

canonicalInvariantObjectsHaveProjectionBundle :
  ∀ object →
  UniversalProjection.carrier
    (FormalProjectionBundle.hecke (formalProjections object))
  ≡
  Unified.heckeCarrier
canonicalInvariantObjectsHaveProjectionBundle object =
  UniversalProjection.carrierIsCanonical
    (FormalProjectionBundle.hecke (formalProjections object))

canonicalInvariantObjectsDoNotPromoteJ :
  ∀ object →
  objectExternalJPromotion object ≡ false
canonicalInvariantObjectsDoNotPromoteJ =
  objectExternalJPromotionIsFalse

canonicalInvariantObjectsDoNotPromoteFormalProjections :
  ∀ object kind →
  objectProjectionPromotion object kind ≡ false
canonicalInvariantObjectsDoNotPromoteFormalProjections object modularJProjectionKind =
  projectionExternalPromotionIsFalse
    (modularJ (formalProjections object))
canonicalInvariantObjectsDoNotPromoteFormalProjections object heckeProjectionKind =
  projectionExternalPromotionIsFalse
    (hecke (formalProjections object))
canonicalInvariantObjectsDoNotPromoteFormalProjections object bottProjectionKind =
  projectionExternalPromotionIsFalse
    (bott (formalProjections object))
canonicalInvariantObjectsDoNotPromoteFormalProjections object kolmogorovProjectionKind =
  projectionExternalPromotionIsFalse
    (kolmogorov (formalProjections object))
canonicalInvariantObjectsDoNotPromoteFormalProjections object categoryProjectionKind =
  projectionExternalPromotionIsFalse
    (category (formalProjections object))
canonicalInvariantObjectsDoNotPromoteFormalProjections object quotientProjectionKind =
  projectionExternalPromotionIsFalse
    (quotient (formalProjections object))
canonicalInvariantObjectsDoNotPromoteFormalProjections object latticeProjectionKind =
  projectionExternalPromotionIsFalse
    (lattice (formalProjections object))
canonicalInvariantObjectsDoNotPromoteFormalProjections object operatorProjectionKind =
  projectionExternalPromotionIsFalse
    (operator (formalProjections object))

canonicalObjectListHasRequiredJProjection :
  List UnifiedObjectInvariant → Set
canonicalObjectListHasRequiredJProjection [] =
  Bool
canonicalObjectListHasRequiredJProjection (object ∷ objects) =
  objectExternalJPromotion object ≡ false
