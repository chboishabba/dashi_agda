module DASHI.Biology.TargetRecognitionBundleFibreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.ProjectionCategory as Category
import DASHI.Core.ProjectionFibre as Fibre
import DASHI.Biology.TargetRecognitionFibrationExact as Indexed
import DASHI.Biology.TargetIndexedRecognitionGeometryExact as Geometry

------------------------------------------------------------------------
-- TOTAL RECOGNITION BUNDLE AND PROJECTION FIBRES
--
-- Total space:
--
--   Sigma (context : RecognitionBaseObject), RecognitionMismatch
--
-- Base projection forgets the mismatch coordinate.
--
-- This module instantiates the repo-native ProjectionCategory and
-- ProjectionFibre owners exactly; no external category-theory theorem is
-- promoted beyond those owners.
------------------------------------------------------------------------

RecognitionTotal : Set
RecognitionTotal =
  Σ Indexed.RecognitionBaseObject
    (λ _ → Geometry.RecognitionMismatch)

baseProjection :
  RecognitionTotal →
  Indexed.RecognitionBaseObject
baseProjection =
  proj₁

------------------------------------------------------------------------
-- Small projection category with exactly the arrows required by the bundle.
------------------------------------------------------------------------

data BundleObject : Set where
  totalObject : BundleObject
  baseObject : BundleObject

data BundleHom : BundleObject → BundleObject → Set where
  idTotal : BundleHom totalObject totalObject
  idBase : BundleHom baseObject baseObject
  projectToBase : BundleHom totalObject baseObject

bundleCompose :
  ∀ {A B C} →
  BundleHom B C →
  BundleHom A B →
  BundleHom A C
bundleCompose idTotal idTotal = idTotal
bundleCompose idBase idBase = idBase
bundleCompose idBase projectToBase = projectToBase
bundleCompose projectToBase idTotal = projectToBase

bundleId :
  ∀ {A} →
  BundleHom A A
bundleId {totalObject} = idTotal
bundleId {baseObject} = idBase

bundleIdLeft :
  ∀ {A B} (f : BundleHom A B) →
  bundleCompose bundleId f ≡ f
bundleIdLeft idTotal = refl
bundleIdLeft idBase = refl
bundleIdLeft projectToBase = refl

bundleIdRight :
  ∀ {A B} (f : BundleHom A B) →
  bundleCompose f bundleId ≡ f
bundleIdRight idTotal = refl
bundleIdRight idBase = refl
bundleIdRight projectToBase = refl

bundleAssoc :
  ∀ {A B C D}
    (f : BundleHom C D)
    (g : BundleHom B C)
    (h : BundleHom A B) →
  bundleCompose (bundleCompose f g) h
  ≡
  bundleCompose f (bundleCompose g h)
bundleAssoc idTotal idTotal idTotal = refl
bundleAssoc idBase idBase idBase = refl
bundleAssoc idBase projectToBase idTotal = refl
bundleAssoc projectToBase idTotal idTotal = refl

recognitionBundleCategory : Category.ProjectionCategory
recognitionBundleCategory =
  record
    { Obj = BundleObject
    ; Hom = BundleHom
    ; id = bundleId
    ; _∘_ = bundleCompose
    ; id-left = bundleIdLeft
    ; id-right = bundleIdRight
    ; assoc = bundleAssoc
    ; categoryReading =
        "Two-object recognition bundle category: total recognition states project to target/context base objects."
    }

------------------------------------------------------------------------
-- Underlying-set interpretation and exact projection.
------------------------------------------------------------------------

BundleUnderlying : BundleObject → Set
BundleUnderlying totalObject = RecognitionTotal
BundleUnderlying baseObject = Indexed.RecognitionBaseObject

applyBundleHom :
  ∀ {A B} →
  BundleHom A B →
  BundleUnderlying A →
  BundleUnderlying B
applyBundleHom idTotal x = x
applyBundleHom idBase x = x
applyBundleHom projectToBase x = baseProjection x

recognitionProjectionFibre :
  Fibre.ProjectionFibre recognitionBundleCategory
recognitionProjectionFibre =
  record
    { Underlying = BundleUnderlying
    ; Carrier = totalObject
    ; Observable = baseObject
    ; π = projectToBase
    ; apply = applyBundleHom
    ; fibreReading =
        "Fibre over one target/context contains the recognition mismatch states compatible with that base coordinate."
    }

------------------------------------------------------------------------
-- Canonical fibre inhabitants.
------------------------------------------------------------------------

permissiveTotalPoint : RecognitionTotal
permissiveTotalPoint =
  Indexed.permissiveContextObject ,
  Geometry.canonicalPairMismatch

strictTotalPoint : RecognitionTotal
strictTotalPoint =
  Indexed.strictContextObject ,
  Geometry.canonicalPairMismatch

permissiveFibrePoint :
  Fibre.Fibre
    recognitionProjectionFibre
    Indexed.permissiveContextObject
permissiveFibrePoint =
  permissiveTotalPoint , refl

strictFibrePoint :
  Fibre.Fibre
    recognitionProjectionFibre
    Indexed.strictContextObject
strictFibrePoint =
  strictTotalPoint , refl

------------------------------------------------------------------------
-- Section and transport.
------------------------------------------------------------------------

canonicalMismatchSection :
  Indexed.RecognitionBaseObject →
  RecognitionTotal
canonicalMismatchSection context =
  context , Geometry.canonicalPairMismatch

sectionProjectsToBase :
  (context : Indexed.RecognitionBaseObject) →
  baseProjection (canonicalMismatchSection context)
  ≡
  context
sectionProjectsToBase context = refl

transportedSectionKeepsMismatch :
  proj₂
    (canonicalMismatchSection Indexed.permissiveContextObject)
  ≡
  proj₂
    (canonicalMismatchSection Indexed.strictContextObject)
transportedSectionKeepsMismatch = refl

------------------------------------------------------------------------
-- Same fine coordinate, distinct bundle points.
------------------------------------------------------------------------

bundlePointsDistinct :
  permissiveTotalPoint ≡ strictTotalPoint → ⊥
bundlePointsDistinct ()

sameMismatchDoesNotIdentifyBundlePoint :
  proj₂ permissiveTotalPoint ≡ proj₂ strictTotalPoint
sameMismatchDoesNotIdentifyBundlePoint = refl

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record TargetRecognitionBundleBoundary : Set where
  constructor targetRecognitionBundleBoundary
  field
    totalSpaceIsDependentContextMismatchPair : Bool
    totalSpaceIsDependentContextMismatchPairIsTrue :
      totalSpaceIsDependentContextMismatchPair ≡ true

    projectionFibreIsRepoNative : Bool
    projectionFibreIsRepoNativeIsTrue :
      projectionFibreIsRepoNative ≡ true

    sameMismatchIdentifiesBaseContext : Bool
    sameMismatchIdentifiesBaseContextIsFalse :
      sameMismatchIdentifiesBaseContext ≡ false

    canonicalSectionIsEmpiricalBiologicalSection : Bool
    canonicalSectionIsEmpiricalBiologicalSectionIsFalse :
      canonicalSectionIsEmpiricalBiologicalSection ≡ false

open TargetRecognitionBundleBoundary public

canonicalTargetRecognitionBundleBoundary :
  TargetRecognitionBundleBoundary
canonicalTargetRecognitionBundleBoundary =
  targetRecognitionBundleBoundary
    true refl
    true refl
    false refl
    false refl
