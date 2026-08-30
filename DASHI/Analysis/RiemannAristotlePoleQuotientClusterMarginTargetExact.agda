module DASHI.Analysis.RiemannAristotlePoleQuotientClusterMarginTargetExact where

------------------------------------------------------------------------
-- POLE-QUOTIENT QUANTITATIVE TARGET-CLUSTER MARGIN
--
-- Existing Lean provenance already records strict positivity of the complete
-- same-ordinate cluster in the universal even-cone / pole-quotient observer.
-- The split complement consumer needs a stronger *quantitative receipt*:
-- an explicit margin M_cluster^pole with
--
--   M_cluster^pole <= ClusterResponse(g_pole).
--
-- This file prevents strict positivity from being silently promoted into an
-- unspecified numerical allowance.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

record PoleQuotientClusterMarginTarget : Set₁ where
  constructor pole-quotient-cluster-margin-target
  field
    Scalar : Set
    Taper : Set

    ClusterResponse : Taper → Scalar
    ClusterMargin : Taper → Scalar
    _≤_ : Scalar → Scalar → Set

    universalPoleQuotientTaper : Taper

    quantitativeClusterMarginLower :
      ClusterMargin universalPoleQuotientTaper
      ≤ ClusterResponse universalPoleQuotientTaper

open PoleQuotientClusterMarginTarget public

record PoleQuotientClusterMarginBoundary : Set where
  constructor pole-quotient-cluster-margin-boundary
  field
    strictClusterPositivityOwnedInLean : Bool
    strictClusterPositivityOwnedInLeanIsTrue :
      strictClusterPositivityOwnedInLean ≡ true

    targetLeadingCoefficientAndRemainderLaneOwnedInLean : Bool
    targetLeadingCoefficientAndRemainderLaneOwnedInLeanIsTrue :
      targetLeadingCoefficientAndRemainderLaneOwnedInLean ≡ true

    strictPositivityAutomaticallyInstantiatesConsumerMargin : Bool
    strictPositivityAutomaticallyInstantiatesConsumerMarginIsFalse :
      strictPositivityAutomaticallyInstantiatesConsumerMargin ≡ false

    literalQuantitativePoleQuotientClusterMarginClosed : Bool
    literalQuantitativePoleQuotientClusterMarginClosedIsFalse :
      literalQuantitativePoleQuotientClusterMarginClosed ≡ false

    requiredTheorem : String

canonicalPoleQuotientClusterMarginBoundary :
  PoleQuotientClusterMarginBoundary
canonicalPoleQuotientClusterMarginBoundary =
  pole-quotient-cluster-margin-boundary
    true refl
    true refl
    false refl
    false refl
    "On the exact universal pole-quotient taper g_pole, instantiate an explicit positive M_cluster^pole and prove M_cluster^pole <= ClusterResponse(g_pole), with enough quantitative room that B_off^pole + B_Gamma < M_cluster^pole can be proved."
