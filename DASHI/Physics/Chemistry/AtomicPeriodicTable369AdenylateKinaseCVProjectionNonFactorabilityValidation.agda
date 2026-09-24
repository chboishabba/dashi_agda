module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCVProjectionNonFactorabilityValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCVProjectionNonFactorabilityExact as Collision

boundary = Collision.canonicalAdKCVProjectionNonFactorabilityBoundary

_ : Collision.selectionExtensionalCOMRequired boundary ≡ true
_ = refl

_ : Collision.threeCVSelectionEquivalenceExplicit boundary ≡ true
_ = refl

_ : Collision.sameSelectedGeometryCreatesSameThreeCV boundary ≡ true
_ = refl

_ : Collision.distinctSameCVPairCreatesProjectionCollision boundary ≡ true
_ = refl

_ : Collision.projectionCollisionReusesCanonicalFactorisationSpine boundary ≡ true
_ = refl

_ : Collision.sourceAttributionCreatesDASHITheorem boundary ≡ false
_ = refl

_ : Collision.threeCVRecoversFullConfiguration boundary ≡ false
_ = refl
