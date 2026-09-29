{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119SingleSectorSharedSourceStressWeldExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.SharedEffectiveSourceRecoveryExact as Shared
import DASHI.Physics.Foundations.CMP119SingleActiveSectorSourceFactorisationExact as Single
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalConstructionExact as Pinned
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as C

------------------------------------------------------------------------
-- MINIMAL SHARED-SOURCE STRESS WELD
--
-- The common-action/metric-variation route is useful corroborating structure,
-- but it is not logically required once ONE shared effective source is already
-- factorised exactly through the literal GR source and the selected physical
-- QFT total.
--
-- This compiler consumes:
--   * direct GR source factorisation;
--   * the single-active-sector CMP119 QFT source compiler;
--   * the existing stress-weld promotion token.
--
-- No Einstein metric-variation receipt or CommonMetricProducerLanguage is
-- required by this shortest route.
------------------------------------------------------------------------

record CMP119SingleSectorSharedSourceStressWeldInputs
    (U : Weld.UnifiedCandidate)
    (source : Shared.SharedEffectiveSourceTheory U)
    (pinned :
      Pinned.PinnedYangMillsConstruction
        {C = Weld.qftCarriers U}
        (Weld.qftSemantics U))
    (group : Top.CompactSimpleGroup (Weld.qftCarriers U))
    {X Configuration Position CurvaturePolynomial LocalOperator OPECoefficient
     Hilbert Vector Algebra Scale Volume Root ContinuumFamily Core
     sequenceLimit limitLaws quotient division S osInputs reconstruction}
    (inputs :
      C.PinnedCMP119ConcreteLocalCInputs
        (Top.CompactSimpleGroup (Weld.qftCarriers U))
        X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient (Top.StressTensor (Weld.qftCarriers U))
        Hilbert Vector (Top.Hamiltonian (Weld.qftCarriers U)) Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} osInputs reconstruction group) : Set₁ where
  field
    grSourceFactorisation :
      Shared.GRSourceFactorisation source

    qftSourceInputs :
      Single.CMP119SingleActiveSectorSourceInputs
        U source pinned group inputs

    stressWeldToken :
      Weld.StressEnergyWeldToken U

open CMP119SingleSectorSharedSourceStressWeldInputs public

cmp119SingleSectorSharedSourceBuildsStressWeld :
  ∀ {U : Weld.UnifiedCandidate}
    {source : Shared.SharedEffectiveSourceTheory U}
    {pinned :
      Pinned.PinnedYangMillsConstruction
        {C = Weld.qftCarriers U}
        (Weld.qftSemantics U)}
    {group : Top.CompactSimpleGroup (Weld.qftCarriers U)}
    {X Configuration Position CurvaturePolynomial LocalOperator OPECoefficient
     Hilbert Vector Algebra Scale Volume Root ContinuumFamily Core
     sequenceLimit limitLaws quotient division S osInputs reconstruction}
    {inputs :
      C.PinnedCMP119ConcreteLocalCInputs
        (Top.CompactSimpleGroup (Weld.qftCarriers U))
        X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient (Top.StressTensor (Weld.qftCarriers U))
        Hilbert Vector (Top.Hamiltonian (Weld.qftCarriers U)) Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} osInputs reconstruction group} →
  CMP119SingleSectorSharedSourceStressWeldInputs
    U source pinned group inputs →
  Weld.SameStressEnergyWeld U
cmp119SingleSectorSharedSourceBuildsStressWeld
    {source = source} weldInputs =
  Shared.sharedSourceImpliesSameStressEnergy
    source
    (grSourceFactorisation weldInputs)
    (Single.cmp119SingleActiveSectorBuildsQFTSourceFactorisation
      (qftSourceInputs weldInputs))
    (stressWeldToken weldInputs)

commonEinsteinMetricVariationRequiredOnMinimalSharedSourceRoute : Bool
commonEinsteinMetricVariationRequiredOnMinimalSharedSourceRoute = false

commonEinsteinMetricVariationRequiredOnMinimalSharedSourceRouteIsFalse :
  commonEinsteinMetricVariationRequiredOnMinimalSharedSourceRoute ≡ false
commonEinsteinMetricVariationRequiredOnMinimalSharedSourceRouteIsFalse = refl

commonMetricProducerLanguageRequiredOnMinimalSharedSourceRoute : Bool
commonMetricProducerLanguageRequiredOnMinimalSharedSourceRoute = false

commonMetricProducerLanguageRequiredOnMinimalSharedSourceRouteIsFalse :
  commonMetricProducerLanguageRequiredOnMinimalSharedSourceRoute ≡ false
commonMetricProducerLanguageRequiredOnMinimalSharedSourceRouteIsFalse = refl

directGRSourceFactorisationStillRequired : Bool
directGRSourceFactorisationStillRequired = true

directGRSourceFactorisationStillRequiredIsTrue :
  directGRSourceFactorisationStillRequired ≡ true
directGRSourceFactorisationStillRequiredIsTrue = refl
