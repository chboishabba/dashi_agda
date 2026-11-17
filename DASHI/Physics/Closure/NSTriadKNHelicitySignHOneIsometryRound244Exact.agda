module DASHI.Physics.Closure.NSTriadKNHelicitySignHOneIsometryRound244Exact where

------------------------------------------------------------------------
-- ROUND244 / HELICITY-SIGN H^1 ISOMETRY REDUCTION
--
-- Backward need from Round243/W1:
--
--   || H u ||_{H^1} = || u ||_{H^1},
--
-- where H = |D|^-1 curl is the helicity-sign action.
--
-- Round142 already identifies the literal physical normalized curl with
--
--   H u = u^+ - u^-.
--
-- The periodic helical infrastructure already owns orthogonal +/- projectors
-- and H^s Pythagoras.  What it does NOT expose is a generic quadratic law for
-- its abstract `hsSquaredNorm`, so we must not silently rewrite the norm of
-- u^+ - u^- from Pythagoras alone.
--
-- This file isolates the exact remaining norm fact: each helical component's
-- H^1 energy is invariant under sign/phase.  Once that standard quadratic-law
-- receipt is supplied, flipping the minus component changes no component
-- energy and therefore the helicity-sign action is an H^1 isometry.
--
-- This is a strict reduction of W1: the repo-specific helicity geometry is
-- already closed; only sign-invariance of the actual H^1 quadratic norm and
-- the standard torus Sobolev embeddings remain analytic.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl; cong)

record HelicalComponentEnergy {a} (Component Scalar : Set a) : Set a where
  constructor helical-component-energy
  field
    energy : Component → Scalar
    negateComponent : Component → Component
    addScalar : Scalar → Scalar → Scalar
    negateEnergyInvariant :
      (v : Component) → energy (negateComponent v) ≡ energy v

open HelicalComponentEnergy public

componentPairEnergy :
  ∀ {a} {Component Scalar : Set a} →
  HelicalComponentEnergy Component Scalar →
  Component → Component → Scalar
componentPairEnergy E plus minus =
  addScalar E (energy E plus) (energy E minus)

helicitySignFlippedPairEnergy :
  ∀ {a} {Component Scalar : Set a} →
  HelicalComponentEnergy Component Scalar →
  Component → Component → Scalar
helicitySignFlippedPairEnergy E plus minus =
  addScalar E (energy E plus) (energy E (negateComponent E minus))

helicitySignFlipPreservesComponentHOneEnergy :
  ∀ {a} {Component Scalar : Set a}
    (E : HelicalComponentEnergy Component Scalar)
    (plus minus : Component) →
  helicitySignFlippedPairEnergy E plus minus
  ≡ componentPairEnergy E plus minus
helicitySignFlipPreservesComponentHOneEnergy E plus minus =
  cong (addScalar E (energy E plus))
    (negateEnergyInvariant E minus)

------------------------------------------------------------------------
-- Physical binding boundary.
--
-- Round142 supplies the vector equality
--
--   normalizedCurl u = u^+ - u^-.
--
-- Round244 proves the component-energy sign-flip invariant.  To conclude the
-- literal physical H^1 norm equality, an analytic realization must identify
-- the physical H^1 norm with the orthogonal sum of the two helical component
-- H^1 energies.  That is exactly the standard quadratic-norm weld and is kept
-- distinct from the already-proved helical algebra.
------------------------------------------------------------------------

record PhysicalHOneHelicalWeld {a}
    (Component Scalar : Set a)
    (E : HelicalComponentEnergy Component Scalar) : Set a where
  constructor physical-hone-helical-weld
  field
    physicalHOneEnergy : Component → Component → Scalar
    normalizedCurlHOneEnergy : Component → Component → Scalar

    physicalEnergyIsComponentSum :
      (plus minus : Component) →
      physicalHOneEnergy plus minus
      ≡ componentPairEnergy E plus minus

    normalizedCurlEnergyIsSignFlippedSum :
      (plus minus : Component) →
      normalizedCurlHOneEnergy plus minus
      ≡ helicitySignFlippedPairEnergy E plus minus

open PhysicalHOneHelicalWeld public

physicalNormalizedCurlHOneIsometry :
  ∀ {a} {Component Scalar : Set a}
    {E : HelicalComponentEnergy Component Scalar}
    (W : PhysicalHOneHelicalWeld Component Scalar E)
    (plus minus : Component) →
  normalizedCurlHOneEnergy W plus minus
  ≡ physicalHOneEnergy W plus minus
physicalNormalizedCurlHOneIsometry {E = E} W plus minus =
  let
    signFlip = helicitySignFlipPreservesComponentHOneEnergy E plus minus
  in
  transEq
    (normalizedCurlEnergyIsSignFlippedSum W plus minus)
    signFlip
    (symEq (physicalEnergyIsComponentSum W plus minus))
  where
  transEq : ∀ {A : Set a} {x y z w : A} → x ≡ y → y ≡ z → z ≡ w → x ≡ w
  transEq refl refl refl = refl

  symEq : ∀ {A : Set a} {x y : A} → x ≡ y → y ≡ x
  symEq refl = refl

round244Round142NormalizedCurlIdentificationReused : Bool
round244Round142NormalizedCurlIdentificationReused = true

round244HelicalComponentSignFlipIsometryClosed : Bool
round244HelicalComponentSignFlipIsometryClosed = true

round244PhysicalQuadraticHOneWeldInstalled : Bool
round244PhysicalQuadraticHOneWeldInstalled = false

round244StandardTorusSobolevEmbeddingsInstalled : Bool
round244StandardTorusSobolevEmbeddingsInstalled = false

round244W1PhysicalInterpolationInstalled : Bool
round244W1PhysicalInterpolationInstalled = false

round244PackageAClosed : Bool
round244PackageAClosed = false

round244ClayPromotion : Bool
round244ClayPromotion = false

round244HelicalComponentSignFlipIsometryClosedIsTrue :
  round244HelicalComponentSignFlipIsometryClosed ≡ true
round244HelicalComponentSignFlipIsometryClosedIsTrue = refl

round244PhysicalQuadraticHOneWeldInstalledIsFalse :
  round244PhysicalQuadraticHOneWeldInstalled ≡ false
round244PhysicalQuadraticHOneWeldInstalledIsFalse = refl

round244W1PhysicalInterpolationInstalledIsFalse :
  round244W1PhysicalInterpolationInstalled ≡ false
round244W1PhysicalInterpolationInstalledIsFalse = refl

round244ClayPromotionIsFalse : round244ClayPromotion ≡ false
round244ClayPromotionIsFalse = refl
