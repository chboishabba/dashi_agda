module DASHI.Core.SnowballPluralLensInvariantExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- SNOWBALL PLURAL-LENS INVARIANT
--
-- The invariant is abstract over the contingent axis vocabulary. A consumer
-- chooses the local Axis type; the invariant requires every locally-relevant
-- axis to survive the projection. New axes may be added later without changing
-- the invariant or pretending the present list is complete.
------------------------------------------------------------------------

record PluralLens (Axis : Set) : Set where
  constructor plural-lens
  field
    relevant : Axis → Bool
    retained : Axis → Bool
    relevantIsRetained :
      (axis : Axis) → relevant axis ≡ true → retained axis ≡ true
open PluralLens public

record LensProjectionReceipt (Axis : Set) (lens : PluralLens Axis) : Set where
  constructor lens-projection-receipt
  field
    projectionNamedLocally : Bool
    noGlobalAxisClosureClaim : Bool
    authorityRoleRetained : Bool
    sourceProvenanceRetained : Bool
    observerPositionRetained : Bool
    disagreementMaySurvive : Bool
open LensProjectionReceipt public

record LensExtension
    (Old New Extended : Set)
    (oldLens : PluralLens Old)
    (extendedLens : PluralLens Extended) : Set where
  constructor lens-extension
  field
    injectOld : Old → Extended
    injectNew : New → Extended
    oldRelevancePreserved :
      (axis : Old) → relevant oldLens axis ≡ relevant extendedLens (injectOld axis)
    oldRetentionPreserved :
      (axis : Old) → retained oldLens axis ≡ retained extendedLens (injectOld axis)
    newAxesNeedNotHaveBeenPreEnumerated : Bool
open LensExtension public

------------------------------------------------------------------------
-- Non-collapse rules. The abstraction removes the need to globally enumerate
-- axes; it does not permit consumers to discard a relevant local distinction.
------------------------------------------------------------------------

data AbstractInvariantErasesRelevantAxis : Set where
data AxisExtensionInvalidatesPriorLens : Set where
data UnnamedAxisMeansIrrelevant : Set where
data PluralLensRequiresEpistemicSynthesis : Set where

abstractInvariantDoesNotEraseRelevantAxis : AbstractInvariantErasesRelevantAxis → ⊥
abstractInvariantDoesNotEraseRelevantAxis ()

axisExtensionNeedNotInvalidatePriorLens : AxisExtensionInvalidatesPriorLens → ⊥
axisExtensionNeedNotInvalidatePriorLens ()

unnamedDoesNotMeanIrrelevant : UnnamedAxisMeansIrrelevant → ⊥
unnamedDoesNotMeanIrrelevant ()

pluralLensNeedNotSynthesize : PluralLensRequiresEpistemicSynthesis → ⊥
pluralLensNeedNotSynthesize ()

record SnowballPluralLensBoundary : Set where
  constructor snowball-plural-lens-boundary
  field
    invariantIndependentOfAxisNames : Bool
    consumersMayAddAxes : Bool
    oldRelevantAxesMustRemainRetained : Bool
    sourceAuthorityObserverCoordinatesFirstClass : Bool
    disagreementMayRemain : Bool
    finitePresentAxisListClaimedComplete : Bool
open SnowballPluralLensBoundary public

canonicalSnowballPluralLensBoundary : SnowballPluralLensBoundary
canonicalSnowballPluralLensBoundary =
  snowball-plural-lens-boundary true true true true true false
