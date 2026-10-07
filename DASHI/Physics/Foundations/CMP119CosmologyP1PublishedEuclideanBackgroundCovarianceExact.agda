{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP1PublishedEuclideanBackgroundCovarianceExact where

------------------------------------------------------------------------
-- S1 PUBLISHED SOURCE LAW: CMP119 EUCLIDEAN COVARIANCE IN B-COORDINATES.
--
-- T. Bałaban, "Convergent Renormalization Expansions for Lattice Gauge
-- Theories", Commun. Math. Phys. 119 (1988), 243--285,
-- DOI 10.1007/BF01217741.
--
-- Eq. (2.29):
--   E^(j)(r U_j, r z) = E^(j)(U_j, z).
--
-- Eq. (3.58) rewrites the same covariance in the Lie-background coordinate B:
--   E^(j)( U_j(Q_1 exp(i rB)), r z )
--     = E^(j)( U_j(exp(i B)), z ).
--
-- The source therefore already supplies the scalar-potential covariance needed
-- by the derivative compiler. The cosmology proof must not repay that as a new
-- theorem. The surviving work is same-object identification of the repository
-- CMP109/116 Background/tangent with this literal B-coordinate and its B4
-- action, including the ten canonical metric/source directions.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

record PublishedCMP119EuclideanBackgroundCovariance
    (Background EuclideanAction : Set)
    (potential : Background → ℝ)
    : Set₁ where
  field
    actBackground : EuclideanAction → Background → Background
    potentialCovariant : ∀ action background →
      potential (actBackground action background) ≡ potential background

open PublishedCMP119EuclideanBackgroundCovariance public

cmp119Equation229And358EuclideanCovarianceLevel : ProofLevel
cmp119Equation229And358EuclideanCovarianceLevel = standardImported

publishedPotentialCovarianceNeedsFreshProof : Bool
publishedPotentialCovarianceNeedsFreshProof = false

remainingS1WorkIsSameObjectBackgroundAndTangentIdentification : Bool
remainingS1WorkIsSameObjectBackgroundAndTangentIdentification = true

remainingS1WorkIncludesTenMetricDirectionsInPublishedBAction : Bool
remainingS1WorkIncludesTenMetricDirectionsInPublishedBAction = true
