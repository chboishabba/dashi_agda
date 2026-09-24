{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119GRAnchoredStressEqualityCoreExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.StressEnergyEqualityCoreExact as Equality
import DASHI.Physics.Foundations.GRAnchoredSharedEffectiveSourceExact as GRSource
import DASHI.Physics.Foundations.CMP119PinnedYMGRQFTSectorStressBridgeExact as CMP
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalConstructionExact as Pinned
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as C

------------------------------------------------------------------------
-- PURE GR-ANCHORED CMP119 EQUALITY CUT
--
-- For one selected physical YM sector, the only physics equation required to
-- identify GR and that selected QFT stress is supplied explicitly below.
-- No QFTStressAggregation witness and no promotion token occurs here.
------------------------------------------------------------------------

record CMP119GRAnchoredCrossSectorEquality
    (U : Weld.UnifiedCandidate)
    (pinned :
      Pinned.PinnedYangMillsConstruction
        {C = Weld.qftCarriers U}
        (Weld.qftSemantics U))
    (group : Top.CompactSimpleGroup (Weld.qftCarriers U))
    {X Configuration Position CurvaturePolynomial LocalOperator OPECoefficient
     Hilbert Vector Algebra Scale Volume Root ContinuumFamily CoreCarrier
     sequenceLimit limitLaws quotient division S osInputs reconstruction}
    (inputs :
      C.PinnedCMP119ConcreteLocalCInputs
        (Top.CompactSimpleGroup (Weld.qftCarriers U))
        X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient (Top.StressTensor (Weld.qftCarriers U))
        Hilbert Vector (Top.Hamiltonian (Weld.qftCarriers U)) Algebra
        Scale Volume Root ContinuumFamily CoreCarrier
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} osInputs reconstruction group) : Set₁ where
  field
    cmp119SharedStressEqualsGRSource :
      ∀ candidate regime →
      Weld.grRegime U regime →
      Weld.qftRegime U regime →
      Weld.grStressToShared U (Weld.coarseGrain U candidate regime)
        (Weld.actualGRStressEnergy U (Weld.coarseGrain U candidate regime))
      ≡
      Weld.qftSectorStressToShared U group (C.stressTensor inputs)

    selectedSectorIsDeclaredQFTTotal :
      ∀ candidate →
      Weld.qftSectorStressToShared U group (C.stressTensor inputs)
      ≡
      Weld.qftTotalStressShared U candidate

open CMP119GRAnchoredCrossSectorEquality public

cmp119GRAnchoredCrossSectorBuildsStressEqualityCore :
  ∀ {U : Weld.UnifiedCandidate}
    {pinned :
      Pinned.PinnedYangMillsConstruction
        {C = Weld.qftCarriers U}
        (Weld.qftSemantics U)}
    {group : Top.CompactSimpleGroup (Weld.qftCarriers U)}
    {X Configuration Position CurvaturePolynomial LocalOperator OPECoefficient
     Hilbert Vector Algebra Scale Volume Root ContinuumFamily CoreCarrier
     sequenceLimit limitLaws quotient division S osInputs reconstruction}
    {inputs :
      C.PinnedCMP119ConcreteLocalCInputs
        (Top.CompactSimpleGroup (Weld.qftCarriers U))
        X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient (Top.StressTensor (Weld.qftCarriers U))
        Hilbert Vector (Top.Hamiltonian (Weld.qftCarriers U)) Algebra
        Scale Volume Root ContinuumFamily CoreCarrier
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} osInputs reconstruction group} →
  CMP119GRAnchoredCrossSectorEquality U pinned group inputs →
  Equality.StressEnergyEqualityCore U
cmp119GRAnchoredCrossSectorBuildsStressEqualityCore equality = record
  { Equality.StressEnergyEqualityCore.sameStressEnergyOnOverlap =
      λ candidate regime grAtRegime qftAtRegime →
        trans
          (cmp119SharedStressEqualsGRSource
            equality candidate regime grAtRegime qftAtRegime)
          (selectedSectorIsDeclaredQFTTotal
            equality (Weld.coarseGrain _ candidate regime))
  }

legacyQFTAggregationNeededForPhysicalStressEquality : Bool
legacyQFTAggregationNeededForPhysicalStressEquality = false

legacyQFTAggregationNeededForPhysicalStressEqualityIsFalse :
  legacyQFTAggregationNeededForPhysicalStressEquality ≡ false
legacyQFTAggregationNeededForPhysicalStressEqualityIsFalse = refl

selectedSectorTotalEqualityStillPhysical : Bool
selectedSectorTotalEqualityStillPhysical = true

selectedSectorTotalEqualityStillPhysicalIsTrue :
  selectedSectorTotalEqualityStillPhysical ≡ true
selectedSectorTotalEqualityStillPhysicalIsTrue = refl
