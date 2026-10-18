{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119GRAnchoredStressMathematicalCoreExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.StressEnergyWeldMathematicalCoreExact as Core
import DASHI.Physics.Foundations.GRAnchoredSharedEffectiveSourceExact as GRSource
import DASHI.Physics.Foundations.CMP119SingleActiveSectorSourceFactorisationExact as Single
import DASHI.Physics.Foundations.SharedEffectiveSourceRecoveryExact as Shared
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalConstructionExact as Pinned
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as C

------------------------------------------------------------------------
-- SHORTEST MATHEMATICAL T-CUT
--
-- No promotion token occurs here.
--
-- The GR-anchored shared source makes GR factorisation reflexive.  The QFT side
-- is supplied by the selected single-active-sector CMP119 source compiler.
-- The resulting two factorisations determine:
--
--   * the QFT stress-totalisation witness;
--   * GR shared stress = declared QFT total stress on overlap.
------------------------------------------------------------------------

record CMP119GRAnchoredStressMathematicalInputs
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
    qftSourceInputs :
      Single.CMP119SingleActiveSectorSourceInputs
        U (GRSource.grAnchoredSharedSource U) pinned group inputs

open CMP119GRAnchoredStressMathematicalInputs public

cmp119GRAnchoredBuildsMathematicalStressCore :
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
  CMP119GRAnchoredStressMathematicalInputs U pinned group inputs →
  Core.StressEnergyWeldMathematicalCore U
cmp119GRAnchoredBuildsMathematicalStressCore
    {U = U} mathInputs =
  let
    qftFactorisation =
      Single.cmp119SingleActiveSectorBuildsQFTSourceFactorisation
        (qftSourceInputs mathInputs)
  in
  record
    { Core.StressEnergyWeldMathematicalCore.qftStressAggregation =
        Shared.QFTSourceFactorisation.qftStressAggregates qftFactorisation
    ; Core.StressEnergyWeldMathematicalCore.sameStressEnergyOnOverlap =
        λ candidate regime grAtRegime qftAtRegime →
          trans
            (sym
              (Shared.GRSourceFactorisation.grSourceFactorises
                GRSource.grAnchoredSourceFactorisesGR
                candidate regime grAtRegime))
            (Shared.QFTSourceFactorisation.qftTotalSourceFactorises
              qftFactorisation candidate regime qftAtRegime)
    }

promotionTokenRequiredToProveMathematicalStressEquality : Bool
promotionTokenRequiredToProveMathematicalStressEquality = false

promotionTokenRequiredToProveMathematicalStressEqualityIsFalse :
  promotionTokenRequiredToProveMathematicalStressEquality ≡ false
promotionTokenRequiredToProveMathematicalStressEqualityIsFalse = refl
