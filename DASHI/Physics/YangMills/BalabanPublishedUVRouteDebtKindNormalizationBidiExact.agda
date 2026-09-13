{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPublishedUVRouteDebtKindNormalizationBidiExact where

------------------------------------------------------------------------
-- PUBLISHED UV ROUTE / DEBT-KIND NORMALIZATION
--
-- Older closure ledgers treated a new nonperturbative Balaban block-spin
-- scale-transfer theorem as mandatory.  The source-native CMP119/CMP122 route
-- supersedes that requirement:
--
-- * CMP122 Theorem 1 is imported at its published strength as four-dimensional
--   UV stability on the active effective-density flow;
-- * finite beta-history smallness is compiler-owned;
-- * the raw CMP119 state can be constructed with its running coupling equal to
--   the finite beta history definitionally;
-- * active Section-2 preservation is then compiler output from the published
--   theorem witness.
--
-- The remaining pre-continuum task is source/same-object instantiation of the
-- literal CMP119/CMP122 complete-density objects and predicates.  The genuinely
-- new post-source mathematics begins after UV stability: continuum Schwinger
-- construction/uniqueness, OS-compatible passage, nontriviality and physical
-- clustering/application.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP122PublishedFourDimensionalUVStabilityExact as UV
import DASHI.Physics.YangMills.BalabanCMP122Theorem1ToRawCMP119ActiveExact as T1
import DASHI.Physics.YangMills.BalabanCMP119RawStateFromFiniteBetaHistoryExact as RawHistory

data PublishedUVRouteDebtKind : Set where
  sourceSameObjectInstantiationDebt : PublishedUVRouteDebtKind
  freshNonperturbativeScaleTransferDebt : PublishedUVRouteDebtKind
  postUVContinuumAnalyticDebt : PublishedUVRouteDebtKind

record PublishedUVRouteBoundary : Set where
  constructor published-uv-route-boundary
  field
    cmp122FourDimensionalUVStabilitySourceOwned : Bool
    cmp122FourDimensionalUVStabilitySourceOwnedIsTrue :
      cmp122FourDimensionalUVStabilitySourceOwned ≡ true

    finiteHistoryCouplingIdentityCompilerOwned : Bool
    finiteHistoryCouplingIdentityCompilerOwnedIsTrue :
      finiteHistoryCouplingIdentityCompilerOwned ≡ true

    activeSection2PreservationCompilerOwnedAfterTheoremWitness : Bool
    activeSection2PreservationCompilerOwnedAfterTheoremWitnessIsTrue :
      activeSection2PreservationCompilerOwnedAfterTheoremWitness ≡ true

    newNonperturbativeBlockSpinScaleTransferMandatory : Bool
    newNonperturbativeBlockSpinScaleTransferMandatoryIsFalse :
      newNonperturbativeBlockSpinScaleTransferMandatory ≡ false

    literalRawObjectsPredicateInstantiationStillRealDebt : Bool
    literalRawObjectsPredicateInstantiationStillRealDebtIsTrue :
      literalRawObjectsPredicateInstantiationStillRealDebt ≡ true

    continuumSchwingerConstructionStillPostUVDebt : Bool
    continuumSchwingerConstructionStillPostUVDebtIsTrue :
      continuumSchwingerConstructionStillPostUVDebt ≡ true

canonicalPublishedUVRouteBoundary : PublishedUVRouteBoundary
canonicalPublishedUVRouteBoundary =
  published-uv-route-boundary
    true refl
    true refl
    true refl
    false refl
    true refl
    true refl

publishedUVStabilityLevel : ProofLevel
publishedUVStabilityLevel = UV.cmp122PublishedFourDimensionalUVStabilitySourceLevel

activeSection2CompilerLevel : ProofLevel
activeSection2CompilerLevel = T1.cmp122Theorem1ProducesActiveSection2Level

finiteHistoryRawStateCompilerLevel : ProofLevel
finiteHistoryRawStateCompilerLevel = RawHistory.cmp119RawStateActiveTheorem1AssemblyLevel

literalRawObjectsPredicateInstantiationLevel : ProofLevel
literalRawObjectsPredicateInstantiationLevel =
  RawHistory.cmp119LiteralRawObjectsAndPredicateInstantiationLevel

continuumSchwingerConstructionLevel : ProofLevel
continuumSchwingerConstructionLevel = UV.continuumSchwingerFamilyConstructionLevel

continuumOSLevel : ProofLevel
continuumOSLevel = UV.continuumOsterwalderSchraderAxiomsLevel

continuumNonGaussianLevel : ProofLevel
continuumNonGaussianLevel = UV.continuumNonGaussianSurvivalLevel

physicalClusteringLevel : ProofLevel
physicalClusteringLevel = UV.cutoffUniformPhysicalExponentialClusteringLevel

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
