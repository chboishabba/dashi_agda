module DASHI.Moonshine.JInvariant369JointFibreBifiltrationExact where

------------------------------------------------------------------------
-- JOINT MODULAR FIBRE x EXISTING J/SSP RESOLUTION BIFILTRATION
--
-- The repository already owns a finite J369 bifiltration whose axes are:
--
--   relational horizon 3/6/9
--   decimal resolution depth r.
--
-- The canonical modular work owns a DIFFERENT axis:
--
--   phase/reflection + principal-level + signed-SSP joint fibre.
--
-- This module composes them as an explicit product rather than identifying
-- either 3/6/9 semantics.  Resolution coarsening acts only on the pre-existing
-- bifiltration coordinate; modular translation/reflection act only on the
-- joint fibre.  Therefore the actions commute definitionally.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.SSP369JResolutionBifiltrationExact as Bif
import DASHI.Moonshine.JInvariant369JointFibredObserverExact as Joint

record JointResolutionState (r : Nat) : Set where
  constructor joint-resolution-state
  field
    modularFibre :
      Joint.Joint369FiniteFibre
    resolutionH9 :
      Bif.H9 r

open JointResolutionState public

coarsenJointResolution :
  ∀ {r} →
  JointResolutionState (suc r) →
  JointResolutionState r
coarsenJointResolution state =
  joint-resolution-state
    (modularFibre state)
    (Bif.coarsen9 (resolutionH9 state))

translateJointResolution :
  ∀ {r} →
  JointResolutionState r →
  JointResolutionState r
translateJointResolution state =
  joint-resolution-state
    (Joint.translateJoint (modularFibre state))
    (resolutionH9 state)

reflectJointResolution :
  ∀ {r} →
  JointResolutionState r →
  JointResolutionState r
reflectJointResolution state =
  joint-resolution-state
    (Joint.reflectJoint (modularFibre state))
    (resolutionH9 state)

coarseningCommutesWithTranslation :
  ∀ {r}
    (state : JointResolutionState (suc r)) →
  coarsenJointResolution (translateJointResolution state)
  ≡
  translateJointResolution (coarsenJointResolution state)
coarseningCommutesWithTranslation state = refl

coarseningCommutesWithReflection :
  ∀ {r}
    (state : JointResolutionState (suc r)) →
  coarsenJointResolution (reflectJointResolution state)
  ≡
  reflectJointResolution (coarsenJointResolution state)
coarseningCommutesWithReflection state = refl

------------------------------------------------------------------------
-- Existing relational-horizon projection also remains orthogonal to the
-- modular fibre.
------------------------------------------------------------------------

record JointResolutionH6State (r : Nat) : Set where
  constructor joint-resolution-h6-state
  field
    modularFibre6 :
      Joint.Joint369FiniteFibre
    resolutionH6 :
      Bif.H6 r

open JointResolutionH6State public

projectJoint9to6 :
  ∀ {r} →
  JointResolutionState r →
  JointResolutionH6State r
projectJoint9to6 state =
  joint-resolution-h6-state
    (modularFibre state)
    (Bif.project9to6 (resolutionH9 state))

translateJointResolutionH6 :
  ∀ {r} →
  JointResolutionH6State r →
  JointResolutionH6State r
translateJointResolutionH6 state =
  joint-resolution-h6-state
    (Joint.translateJoint (modularFibre6 state))
    (resolutionH6 state)

projectHorizonCommutesWithTranslation :
  ∀ {r}
    (state : JointResolutionState r) →
  projectJoint9to6 (translateJointResolution state)
  ≡
  translateJointResolutionH6 (projectJoint9to6 state)
projectHorizonCommutesWithTranslation state = refl

------------------------------------------------------------------------
-- Claim boundary.
------------------------------------------------------------------------

record JointFibreBifiltrationBoundary : Set where
  constructor joint-fibre-bifiltration-boundary
  field
    productAxisConstructed : Bool
    resolutionCoarseningCommutesWithLevelTranslation : Bool
    resolutionCoarseningCommutesWithReflection : Bool
    horizonProjectionCommutesWithLevelTranslation : Bool

    oldRelational369HorizonEqualsPrincipalLevelTower : Bool
    decimalResolutionEqualsModularLevelDepth : Bool
    finiteCommutingSquaresProveInfiniteLimitInterchange : Bool

open JointFibreBifiltrationBoundary public

canonicalJointFibreBifiltrationBoundary :
  JointFibreBifiltrationBoundary
canonicalJointFibreBifiltrationBoundary =
  joint-fibre-bifiltration-boundary
    true true true true
    false false false
