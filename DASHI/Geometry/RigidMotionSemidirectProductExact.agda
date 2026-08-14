module DASHI.Geometry.RigidMotionSemidirectProductExact where

------------------------------------------------------------------------
-- RIGID-MOTION SEMIDIRECT PRODUCT
--
-- SE(3) is algebraically SO(3) acting on translations R^3.  This module proves
-- the group laws for the semidirect product from explicit rotation-group,
-- translation-group and action laws.  It is independent of any floating-point
-- matrix representation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

record RigidMotionModel : Set₁ where
  field
    Rotation Translation : Set

    rId : Rotation
    rMul : Rotation → Rotation → Rotation
    rInv : Rotation → Rotation

    tZero : Translation
    tAdd : Translation → Translation → Translation
    tNeg : Translation → Translation

    act : Rotation → Translation → Translation

    rAssoc : (a b c : Rotation) →
      rMul (rMul a b) c ≡ rMul a (rMul b c)
    rIdLeft : (a : Rotation) → rMul rId a ≡ a
    rIdRight : (a : Rotation) → rMul a rId ≡ a
    rInvLeft : (a : Rotation) → rMul (rInv a) a ≡ rId
    rInvRight : (a : Rotation) → rMul a (rInv a) ≡ rId

    tAssoc : (a b c : Translation) →
      tAdd (tAdd a b) c ≡ tAdd a (tAdd b c)
    tZeroLeft : (a : Translation) → tAdd tZero a ≡ a
    tZeroRight : (a : Translation) → tAdd a tZero ≡ a
    tNegLeft : (a : Translation) → tAdd (tNeg a) a ≡ tZero
    tNegRight : (a : Translation) → tAdd a (tNeg a) ≡ tZero

    actIdentity : (v : Translation) → act rId v ≡ v
    actCompose : (a b : Rotation) (v : Translation) →
      act (rMul a b) v ≡ act a (act b v)
    actAdd : (a : Rotation) (u v : Translation) →
      act a (tAdd u v) ≡ tAdd (act a u) (act a v)
    actZero : (a : Rotation) → act a tZero ≡ tZero

open RigidMotionModel public

record RigidMotion (model : RigidMotionModel) : Set where
  constructor rigidMotion
  field
    rotation : Rotation model
    translation : Translation model

open RigidMotion public

rigid-ext :
  ∀ {model} {r₁ r₂ : Rotation model} {t₁ t₂ : Translation model} →
  r₁ ≡ r₂ → t₁ ≡ t₂ →
  rigidMotion {model} r₁ t₁ ≡ rigidMotion r₂ t₂
rigid-ext refl refl = refl

identity : (model : RigidMotionModel) → RigidMotion model
identity model = rigidMotion (rId model) (tZero model)

compose : (model : RigidMotionModel) →
  RigidMotion model → RigidMotion model → RigidMotion model
compose model (rigidMotion r₁ t₁) (rigidMotion r₂ t₂) =
  rigidMotion
    (rMul model r₁ r₂)
    (tAdd model t₁ (act model r₁ t₂))

inverse : (model : RigidMotionModel) → RigidMotion model → RigidMotion model
inverse model (rigidMotion r t) =
  rigidMotion
    (rInv model r)
    (act model (rInv model r) (tNeg model t))

leftIdentity :
  (model : RigidMotionModel) (g : RigidMotion model) →
  compose model (identity model) g ≡ g
leftIdentity model (rigidMotion r t)
  rewrite rIdLeft model r
        | actIdentity model t
        | tZeroLeft model t = refl

rightIdentity :
  (model : RigidMotionModel) (g : RigidMotion model) →
  compose model g (identity model) ≡ g
rightIdentity model (rigidMotion r t)
  rewrite rIdRight model r
        | actZero model r
        | tZeroRight model t = refl

inverseLeft :
  (model : RigidMotionModel) (g : RigidMotion model) →
  compose model (inverse model g) g ≡ identity model
inverseLeft model (rigidMotion r t) =
  rigid-ext
    (rInvLeft model r)
    translationProof
  where
    translationProof :
      tAdd model
        (act model (rInv model r) (tNeg model t))
        (act model (rInv model r) t)
      ≡ tZero model
    translationProof =
      trans
        (sym (actAdd model (rInv model r) (tNeg model t) t))
        (trans
          (cong (act model (rInv model r)) (tNegLeft model t))
          (actZero model (rInv model r)))

inverseRight :
  (model : RigidMotionModel) (g : RigidMotion model) →
  compose model g (inverse model g) ≡ identity model
inverseRight model (rigidMotion r t) =
  rigid-ext
    (rInvRight model r)
    translationProof
  where
    translationProof :
      tAdd model t
        (act model r
          (act model (rInv model r) (tNeg model t)))
      ≡ tZero model
    translationProof =
      trans
        (cong (tAdd model t)
          (sym (actCompose model r (rInv model r) (tNeg model t))))
        (trans
          (cong (λ q → tAdd model t (act model q (tNeg model t)))
            (rInvRight model r))
          (trans
            (cong (tAdd model t) (actIdentity model (tNeg model t)))
            (tNegRight model t)))

associative :
  (model : RigidMotionModel) (a b c : RigidMotion model) →
  compose model (compose model a b) c
  ≡ compose model a (compose model b c)
associative model
  (rigidMotion r₁ t₁)
  (rigidMotion r₂ t₂)
  (rigidMotion r₃ t₃) =
  rigid-ext
    (rAssoc model r₁ r₂ r₃)
    translationProof
  where
    translationProof :
      tAdd model
        (tAdd model t₁ (act model r₁ t₂))
        (act model (rMul model r₁ r₂) t₃)
      ≡
      tAdd model t₁
        (act model r₁ (tAdd model t₂ (act model r₂ t₃)))
    translationProof =
      trans
        (tAssoc model t₁ (act model r₁ t₂)
          (act model (rMul model r₁ r₂) t₃))
        (trans
          (cong (tAdd model t₁)
            (cong (tAdd model (act model r₁ t₂))
              (actCompose model r₁ r₂ t₃)))
          (cong (tAdd model t₁)
            (sym (actAdd model r₁ t₂ (act model r₂ t₃)))))

record RigidMotionGroupLaws (model : RigidMotionModel) : Set₁ where
  field
    assoc : (a b c : RigidMotion model) →
      compose model (compose model a b) c
      ≡ compose model a (compose model b c)
    idLeft : (g : RigidMotion model) → compose model (identity model) g ≡ g
    idRight : (g : RigidMotion model) → compose model g (identity model) ≡ g
    invLeft : (g : RigidMotion model) → compose model (inverse model g) g ≡ identity model
    invRight : (g : RigidMotion model) → compose model g (inverse model g) ≡ identity model

canonicalRigidMotionGroupLaws :
  (model : RigidMotionModel) → RigidMotionGroupLaws model
canonicalRigidMotionGroupLaws model = record
  { assoc = associative model
  ; idLeft = leftIdentity model
  ; idRight = rightIdentity model
  ; invLeft = inverseLeft model
  ; invRight = inverseRight model
  }
