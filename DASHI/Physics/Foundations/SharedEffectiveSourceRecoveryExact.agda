module DASHI.Physics.Foundations.SharedEffectiveSourceRecoveryExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld

------------------------------------------------------------------------
-- BIDI source seam.
--
-- The literal GR source and the TOTAL QFT stress-energy factor through ONE
-- effective source produced from the SAME coarse-grained candidate:
--
--       literal GR StressEnergy
--                |
--                v
--       shared effective source
--                |
--                v
--       total QFT stress-energy
--                ^
--                |
--       aggregation of literal group-indexed QFT stresses
--
-- Thus the cross-sector equality is algebraic after the genuinely physical
-- factorisation and aggregation receipts are supplied.
------------------------------------------------------------------------

record SharedEffectiveSourceTheory (U : Weld.UnifiedCandidate) : Set₁ where
  constructor sharedEffectiveSourceTheory
  field
    effectiveSource :
      Weld.Candidate U → Weld.Regime U → Weld.SharedStressEnergy U

    sourceAfterCoarseGraining :
      Weld.Candidate U → Weld.Regime U → Weld.SharedStressEnergy U

    sourceCoarseGrainingCommutes :
      ∀ candidate regime →
      sourceAfterCoarseGraining candidate regime
      ≡ effectiveSource (Weld.coarseGrain U candidate regime) regime

open SharedEffectiveSourceTheory public

record GRSourceFactorisation
    {U : Weld.UnifiedCandidate}
    (source : SharedEffectiveSourceTheory U) : Set₁ where
  field
    grSourceFactorises :
      ∀ candidate regime →
      Weld.grRegime U regime →
      Weld.grStressToShared U (Weld.coarseGrain U candidate regime)
        (Weld.actualGRStressEnergy U (Weld.coarseGrain U candidate regime))
      ≡
      effectiveSource source (Weld.coarseGrain U candidate regime) regime

open GRSourceFactorisation public

record QFTSourceFactorisation
    {U : Weld.UnifiedCandidate}
    (source : SharedEffectiveSourceTheory U) : Set₁ where
  field
    -- Literal group-indexed QFT stresses genuinely compose to the declared
    -- total stress-energy; the aggregation rule is application-owned.
    qftStressAggregates : ∀ candidate →
      Weld.QFTStressAggregation U candidate
        (Weld.actualQFTSectorStressShared U candidate)
        (Weld.qftTotalStressShared U candidate)

    -- The common effective source is then identified with the TOTAL QFT source.
    qftTotalSourceFactorises :
      ∀ candidate regime →
      Weld.qftRegime U regime →
      effectiveSource source (Weld.coarseGrain U candidate regime) regime
      ≡
      Weld.qftTotalStressShared U (Weld.coarseGrain U candidate regime)

open QFTSourceFactorisation public

sharedSourceImpliesSameStressEnergy :
  ∀ {U : Weld.UnifiedCandidate}
    (source : SharedEffectiveSourceTheory U) →
  GRSourceFactorisation source →
  QFTSourceFactorisation source →
  Weld.StressEnergyWeldToken U →
  Weld.SameStressEnergyWeld U
sharedSourceImpliesSameStressEnergy source grFactor qftFactor token = record
  { Weld.SameStressEnergyWeld.qftStressAggregation =
      QFTSourceFactorisation.qftStressAggregates qftFactor
  ; Weld.SameStressEnergyWeld.sameStressEnergyOnOverlap =
      λ candidate regime grAtRegime qftAtRegime →
        trans
          (GRSourceFactorisation.grSourceFactorises
            grFactor candidate regime grAtRegime)
          (QFTSourceFactorisation.qftTotalSourceFactorises
            qftFactor candidate regime qftAtRegime)
  ; Weld.SameStressEnergyWeld.stressWeldPromotionToken = token
  }

record SharedSourceRegimeControl
    {U : Weld.UnifiedCandidate}
    (source : SharedEffectiveSourceTheory U) : Set₁ where
  field
    overlapRegime : Weld.Regime U
    overlapIsGR : Weld.grRegime U overlapRegime
    overlapIsQFT : Weld.qftRegime U overlapRegime

    backreactionFromSharedSource : ∀ candidate →
      Weld.BackreactionConsistent U
        (Weld.coarseGrain U candidate overlapRegime) overlapRegime

    correctionsControlledOnSharedSource : ∀ candidate →
      Weld.CorrectionsControlled U
        (Weld.coarseGrain U candidate overlapRegime) overlapRegime

    regimeToken : Weld.RegimeRecoveryToken U

open SharedSourceRegimeControl public

sharedSourceControlImpliesCommonRegimeRecovery :
  ∀ {U : Weld.UnifiedCandidate}
    {source : SharedEffectiveSourceTheory U} →
  SharedSourceRegimeControl source →
  Weld.CommonRegimeRecovery U
sharedSourceControlImpliesCommonRegimeRecovery control = record
  { Weld.CommonRegimeRecovery.overlapRegime = overlapRegime control
  ; Weld.CommonRegimeRecovery.overlapIsGR = overlapIsGR control
  ; Weld.CommonRegimeRecovery.overlapIsQFT = overlapIsQFT control
  ; Weld.CommonRegimeRecovery.backreactionConsistency =
      backreactionFromSharedSource control
  ; Weld.CommonRegimeRecovery.correctionControl =
      correctionsControlledOnSharedSource control
  ; Weld.CommonRegimeRecovery.regimePromotionToken = regimeToken control
  }

record SharedSourceCrossSectorReceipt
    (U : Weld.UnifiedCandidate) : Set₁ where
  field
    source : SharedEffectiveSourceTheory U
    grFactorisation : GRSourceFactorisation source
    qftFactorisation : QFTSourceFactorisation source
    stressWeldToken : Weld.StressEnergyWeldToken U
    regimeControl : SharedSourceRegimeControl source

open SharedSourceCrossSectorReceipt public

sharedSourceCrossSectorReceiptCompiles :
  ∀ {U : Weld.UnifiedCandidate} →
  SharedSourceCrossSectorReceipt U →
  Weld.SameStressEnergyWeld U × Weld.CommonRegimeRecovery U
sharedSourceCrossSectorReceiptCompiles receipt =
  sharedSourceImpliesSameStressEnergy
    (source receipt)
    (grFactorisation receipt)
    (qftFactorisation receipt)
    (stressWeldToken receipt)
  ,
  sharedSourceControlImpliesCommonRegimeRecovery (regimeControl receipt)

record SharedSourceBoundary : Set where
  constructor sharedSourceBoundary
  field
    namingOneObjectEffectiveActionProvesStressWeld : Bool
    namingOneObjectEffectiveActionProvesStressWeldIsFalse :
      namingOneObjectEffectiveActionProvesStressWeld ≡ false

    separateGRAndQFTSourceFitsProveSameObject : Bool
    separateGRAndQFTSourceFitsProveSameObjectIsFalse :
      separateGRAndQFTSourceFitsProveSameObject ≡ false

    oneGaugeSectorStressEqualsTotalEinsteinSource : Bool
    oneGaugeSectorStressEqualsTotalEinsteinSourceIsFalse :
      oneGaugeSectorStressEqualsTotalEinsteinSource ≡ false

    exactAggregationAndTwoFactorisationsProveWeld : Bool
    exactAggregationAndTwoFactorisationsProveWeldIsTrue :
      exactAggregationAndTwoFactorisationsProveWeld ≡ true

canonicalSharedSourceBoundary : SharedSourceBoundary
canonicalSharedSourceBoundary =
  sharedSourceBoundary false refl false refl false refl true refl
