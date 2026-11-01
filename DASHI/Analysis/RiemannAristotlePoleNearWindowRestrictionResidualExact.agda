module DASHI.Analysis.RiemannAristotlePoleNearWindowRestrictionResidualExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleNearTranslationModulationIntertwinerExact as HT

------------------------------------------------------------------------
-- RH H_W LEAF: WINDOW/RESTRICTION COMPATIBILITY + RESIDUAL
--
-- Monster/Base369 contributes the structural warning that a translation can
-- be lawful on a full periodic carrier while restriction to a smaller observed
-- region creates/cuts edges.  RH imports only this proof shape:
--
--   lawful global modulation
--   !=
--   lawful modulation after near-window restriction.
--
-- The actual RH theorem must track the exact cluster + near + far residual.
------------------------------------------------------------------------

record PoleNearWindowRestriction
    (H_T : HT.TargetTranslationModulationIntertwiner) : Set₁ where
  constructor pole-near-window-restriction
  field
    FullCarrier RestrictedCarrier Scalar : Set

    fullTranslatedResponse : FullCarrier → Scalar
    restrictNearWindow : FullCarrier → RestrictedCarrier
    restrictedNearResponse : RestrictedCarrier → Scalar

    sameOrdinateCluster : FullCarrier → Scalar
    farResidual : FullCarrier → Scalar

    add : Scalar → Scalar → Scalar

    -- The key decomposition.  The exact application supplies the algebraic
    -- carrier and proves this identity for the actual target/cutoff data.
    restrictionResidualDecomposition :
      (x : FullCarrier) →
      fullTranslatedResponse x
      ≡ add (sameOrdinateCluster x)
          (add (restrictedNearResponse (restrictNearWindow x))
               (farResidual x))

    usesSharedTranslationModulation : Set
    preservesLiteralPoleTaper : Set
    preservesTargetRelativeGap : Set
    preservesMultiplicity : Set
    preservesNearOffFinset : Set
    residualIsActualFarZeroChannel : Set

    restrictionReference : String

open PoleNearWindowRestriction public

------------------------------------------------------------------------
-- H_W is logically downstream of H_T.  Similar-looking windows without the
-- shared target-translation law cannot be promoted.
------------------------------------------------------------------------

record WindowRestrictionAuthority
    (H_T : HT.TargetTranslationModulationIntertwiner)
    (H_W : PoleNearWindowRestriction H_T) : Set₁ where
  constructor window-restriction-authority
  field
    globalModulationLawUsed : Set
    restrictionCompatibilityProved : Set
    residualTrackedRatherThanErased : Set
    authorityReference : String

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record WindowRestrictionBoundary : Set where
  constructor window-restriction-boundary
  field
    globalModulationImpliesRestrictedCompatibilityAutomatically : Bool
    globalModulationImpliesRestrictedCompatibilityAutomaticallyIsFalse :
      globalModulationImpliesRestrictedCompatibilityAutomatically ≡ false

    explicitRestrictionResidualRequired : Bool
    explicitRestrictionResidualRequiredIsTrue :
      explicitRestrictionResidualRequired ≡ true

    clusterNearFarDecompositionRequired : Bool
    clusterNearFarDecompositionRequiredIsTrue :
      clusterNearFarDecompositionRequired ≡ true

    monsterPeriodicRestrictionIsOnlyStructuralDonor : Bool
    monsterPeriodicRestrictionIsOnlyStructuralDonorIsTrue :
      monsterPeriodicRestrictionIsOnlyStructuralDonor ≡ true

    windowRestrictionClosed : Bool
    windowRestrictionClosedIsFalse : windowRestrictionClosed ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    nextTheorem : String

canonicalWindowRestrictionBoundary : WindowRestrictionBoundary
canonicalWindowRestrictionBoundary =
  window-restriction-boundary
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl
    "Assuming the shared target translation-modulation intertwiner H_T on the actual RH carrier, prove that the finite near-window restriction is compatible with that modulation and derive the literal full translated spectral response = same-ordinate cluster + finite pole-near response + far-zero residual decomposition."
