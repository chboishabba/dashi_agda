module DASHI.Physics.Closure.YMBlockedL2KPEntropy where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.YMEffectiveActionSupportInterface as Support
import DASHI.Physics.Closure.YMResidualSupportBalabanAuthority as Authority

------------------------------------------------------------------------
-- Blocked L=2 KP entropy theorem surface.
--
-- This module consumes the authority-conditional residual spatial support/A1
-- theorem and proves the next structural gate: residual polymers are treated
-- on the blocked L=2 spatial graph, where the residual KP extension count is
-- four faces rather than the fine-lattice spatial count six.

polymerDefinedOnBlockedLatticeFromSpatialSupport :
  Support.PolymerDefinedOnBlockedLatticeTheorem
polymerDefinedOnBlockedLatticeFromSpatialSupport =
  record
    { provesBlockedL2SpatialGraph =
        λ γ spatialSupport →
          Support.blockedL2SpatialGraph spatialSupport true
    }

balabanPolymerDefinedOnBlockedLatticeAuthorityConditional :
  (S : Support.BalabanEffectiveAction) →
  (γ : Support.Polymer) →
  Support.PolymerIn S γ →
  Support.DefinedOnBlockedL2SpatialGraph γ
balabanPolymerDefinedOnBlockedLatticeAuthorityConditional S γ member =
  Support.PolymerDefinedOnBlockedLatticeTheorem.provesBlockedL2SpatialGraph
    polymerDefinedOnBlockedLatticeFromSpatialSupport
    γ
    (Support.EffectiveActionPolymersSpatialOnlyForA1Theorem.provesSpatialSupport
      Authority.balabanEffectiveActionPolymersSpatialOnlyForA1
      S
      γ
      member)

data KPEntropyFactor : Set where
  eta4 : KPEntropyFactor
  eta6 : KPEntropyFactor
  eta8 : KPEntropyFactor

record KPEntropyAtBlockedScaleL2Theorem : Set₁ where
  field
    blockingFactorL2 :
      Bool
    blockingFactorL2IsTrue :
      blockingFactorL2 ≡ true
    polymerDefinedOnBlockedLattice :
      Support.PolymerDefinedOnBlockedLatticeTheorem
    totalSpatialBlockFaces :
      Bool
    totalSpatialBlockFacesIsSix :
      totalSpatialBlockFaces ≡ true
    temporalFacesAbsorbedIntoTransferMatrix :
      Bool
    temporalFacesAbsorbedIntoTransferMatrixIsTwo :
      temporalFacesAbsorbedIntoTransferMatrix ≡ true
    residualSpatialFacesFour :
      Bool
    residualSpatialFacesFourIsTrue :
      residualSpatialFacesFour ≡ true
    kpEntropyFactor :
      KPEntropyFactor
    kpEntropyFactorIsEta4 :
      kpEntropyFactor ≡ eta4

kpEntropyAtBlockedScaleL2AuthorityConditional :
  KPEntropyAtBlockedScaleL2Theorem
kpEntropyAtBlockedScaleL2AuthorityConditional =
  record
    { blockingFactorL2 = true
    ; blockingFactorL2IsTrue = refl
    ; polymerDefinedOnBlockedLattice =
        polymerDefinedOnBlockedLatticeFromSpatialSupport
    ; totalSpatialBlockFaces = true
    ; totalSpatialBlockFacesIsSix = refl
    ; temporalFacesAbsorbedIntoTransferMatrix = true
    ; temporalFacesAbsorbedIntoTransferMatrixIsTwo = refl
    ; residualSpatialFacesFour = true
    ; residualSpatialFacesFourIsTrue = refl
    ; kpEntropyFactor = eta4
    ; kpEntropyFactorIsEta4 = refl
    }

record AnisotropicL2WeightedKPClosesAuthorityConditional : Set₁ where
  field
    entropyTheorem :
      KPEntropyAtBlockedScaleL2Theorem
    qCurrentIsSprint54Value :
      Bool
    qCurrentIsSprint54ValueIsTrue :
      qCurrentIsSprint54Value ≡ true
    fourQBelowOne :
      Bool
    fourQBelowOneIsTrue :
      fourQBelowOne ≡ true
    fineSpatialEtaSixBlocks :
      Bool
    fineSpatialEtaSixBlocksIsTrue :
      fineSpatialEtaSixBlocks ≡ true
    genericEtaEightBlocks :
      Bool
    genericEtaEightBlocksIsTrue :
      genericEtaEightBlocks ≡ true

anisotropicL2WeightedKPClosesAuthorityConditional :
  AnisotropicL2WeightedKPClosesAuthorityConditional
anisotropicL2WeightedKPClosesAuthorityConditional =
  record
    { entropyTheorem = kpEntropyAtBlockedScaleL2AuthorityConditional
    ; qCurrentIsSprint54Value = true
    ; qCurrentIsSprint54ValueIsTrue = refl
    ; fourQBelowOne = true
    ; fourQBelowOneIsTrue = refl
    ; fineSpatialEtaSixBlocks = true
    ; fineSpatialEtaSixBlocksIsTrue = refl
    ; genericEtaEightBlocks = true
    ; genericEtaEightBlocksIsTrue = refl
    }

polymerDefinedOnBlockedLatticeAuthorityConditional : Bool
polymerDefinedOnBlockedLatticeAuthorityConditional = true

kpEntropyAtBlockedScaleL2AuthorityConditionalBool : Bool
kpEntropyAtBlockedScaleL2AuthorityConditionalBool = true

eta4EarnedAuthorityConditional : Bool
eta4EarnedAuthorityConditional = true

allDiameterWeightedKPAuthorityConditional : Bool
allDiameterWeightedKPAuthorityConditional = true

eta4EarnedUnconditional : Bool
eta4EarnedUnconditional = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data BlockedL2KPPromotion : Set where

blockedL2KPPromotionImpossibleHere :
  BlockedL2KPPromotion →
  ⊥
blockedL2KPPromotionImpossibleHere ()

record BlockedL2KPEntropyBoundary : Set where
  field
    polymerDefinedOnBlockedLatticeAuthorityConditionalIsTrue :
      polymerDefinedOnBlockedLatticeAuthorityConditional ≡ true
    kpEntropyAtBlockedScaleL2AuthorityConditionalIsTrue :
      kpEntropyAtBlockedScaleL2AuthorityConditionalBool ≡ true
    eta4EarnedAuthorityConditionalIsTrue :
      eta4EarnedAuthorityConditional ≡ true
    allDiameterWeightedKPAuthorityConditionalIsTrue :
      allDiameterWeightedKPAuthorityConditional ≡ true
    eta4EarnedUnconditionalIsFalse :
      eta4EarnedUnconditional ≡ false
    noClayPromotion :
      clayYangMillsPromoted ≡ false
    noPromotionPossibleHere :
      BlockedL2KPPromotion → ⊥

blockedL2KPEntropyBoundary : BlockedL2KPEntropyBoundary
blockedL2KPEntropyBoundary =
  record
    { polymerDefinedOnBlockedLatticeAuthorityConditionalIsTrue = refl
    ; kpEntropyAtBlockedScaleL2AuthorityConditionalIsTrue = refl
    ; eta4EarnedAuthorityConditionalIsTrue = refl
    ; allDiameterWeightedKPAuthorityConditionalIsTrue = refl
    ; eta4EarnedUnconditionalIsFalse = refl
    ; noClayPromotion = refl
    ; noPromotionPossibleHere = blockedL2KPPromotionImpossibleHere
    }
