module DASHI.Biology.MonsterStructuredBulkCarrierExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Robert L. Griess,
-- "The Friendly Giant", Inventiones Mathematicae 69 (1982), 1--102.
-- DOI: 10.1007/BF01389186.
--
-- Richard E. Borcherds,
-- "Monstrous Moonshine and Monstrous Lie Superalgebras",
-- Inventiones Mathematicae 109 (1992), 405--444.
-- DOI: 10.1007/BF01232032.
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications",
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- DASHI CONTRIBUTION
--
-- Refine the arithmetic carrier
--
--   196883 = 10 * 3^9 + 53
--
-- into the structured elementary-harmonic identity
--
--   196883 = 3^11 + 3^9 + 53.
--
-- The 3^11 term is T^2 x T^9, the 3^9 term is the distinguished j-channel
-- evaluated on the same fine-frequency fibre, and 53 is the independently
-- typed reduced quotient V54 / 1.  This remains an associated-graded/channel
-- candidate, not a Monster branching rule.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_+_)

import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Biology.MonsterFilteredCarrierExact as Filtered

ordinaryChannelPiece : Nat
ordinaryChannelPiece = Harmonic.ordinaryHarmonicDimension

completionChannelPiece : Nat
completionChannelPiece = Harmonic.completionHarmonicDimension

reducedChannelPiece : Nat
reducedChannelPiece = Filtered.reducedDimension

structuredBulkDimension : Nat
structuredBulkDimension = ordinaryChannelPiece + completionChannelPiece

structuredTotalDimension : Nat
structuredTotalDimension = structuredBulkDimension + reducedChannelPiece

structuredBulkDimensionExact : structuredBulkDimension ≡ 196830
structuredBulkDimensionExact = refl

structuredTotalDimensionExact : structuredTotalDimension ≡ 196883
structuredTotalDimensionExact = refl

threePowerElevenPlusThreePowerNinePlusFiftyThree :
  177147 + 19683 + 53 ≡ 196883
threePowerElevenPlusThreePowerNinePlusFiftyThree = refl

record StructuredAssociatedGraded : Set where
  constructor structuredAssociatedGraded
  field
    ordinaryHarmonicPiece : Nat
    completionHarmonicPiece : Nat
    reducedQuotientPiece : Nat
    totalDimension : Nat
    totalIsThreePieces :
      totalDimension
      ≡ ordinaryHarmonicPiece
        + completionHarmonicPiece
        + reducedQuotientPiece

open StructuredAssociatedGraded public

canonicalStructuredAssociatedGraded : StructuredAssociatedGraded
canonicalStructuredAssociatedGraded =
  structuredAssociatedGraded 177147 19683 53 196883 refl

record StructuredBulkBoundary : Set where
  constructor structuredBulkBoundary
  field
    tenIsPrimitiveSymmetryMultiplicity : Set
    tenIsNotPrimitiveSymmetryMultiplicity :
      tenIsPrimitiveSymmetryMultiplicity → Set

    structuredChannelsAreMonsterInvariantSummands : Set
    structuredChannelsAreNotClaimedMonsterInvariantSummands :
      structuredChannelsAreMonsterInvariantSummands → Set

    structuredCarrierIsFullTetrationalAssignmentSpace : Set
    structuredCarrierIsNotFullTetrationalAssignmentSpace :
      structuredCarrierIsFullTetrationalAssignmentSpace → Set

canonicalStructuredBulkBoundary : StructuredBulkBoundary
canonicalStructuredBulkBoundary =
  structuredBulkBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Empty using (⊥)
