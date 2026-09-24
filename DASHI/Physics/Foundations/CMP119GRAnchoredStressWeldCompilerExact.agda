{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119GRAnchoredStressWeldCompilerExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.GRAnchoredSharedEffectiveSourceExact as GRSource
import DASHI.Physics.Foundations.CMP119SingleActiveSectorSourceFactorisationExact as Single
import DASHI.Physics.Foundations.SharedEffectiveSourceRecoveryExact as Shared
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalConstructionExact as Pinned
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as C

------------------------------------------------------------------------
-- SHORTEST CURRENT T-SEAM
--
-- GR side:
--   shared source := literal GR source                    (definition)
--   GR source factorisation                              (refl)
--
-- QFT side:
--   CMP119 -> literal pinned -> selected/recovered stress (existing compiler)
--   selected active sector -> declared physical total    (application witness)
--
-- Remaining cross-sector theorem:
--
--   GR shared stress = CMP119 selected-sector shared stress
--
-- on the same coarse-grained candidate/regime.
------------------------------------------------------------------------

record CMP119GRAnchoredStressWeldInputs
    (U : Weld.UnifiedCandidate)
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
    qftSourceInputs :
      Single.CMP119SingleActiveSectorSourceInputs
        U (GRSource.grAnchoredSharedSource U) pinned group inputs

    stressWeldToken :
      Weld.StressEnergyWeldToken U

open CMP119GRAnchoredStressWeldInputs public

cmp119GRAnchoredBuildsStressWeld :
  ∀ {U : Weld.UnifiedCandidate}
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
  CMP119GRAnchoredStressWeldInputs U pinned group inputs →
  Weld.SameStressEnergyWeld U
cmp119GRAnchoredBuildsStressWeld {U = U} weldInputs =
  Shared.sharedSourceImpliesSameStressEnergy
    (GRSource.grAnchoredSharedSource U)
    GRSource.grAnchoredSourceFactorisesGR
    (Single.cmp119SingleActiveSectorBuildsQFTSourceFactorisation
      (qftSourceInputs weldInputs))
    (stressWeldToken weldInputs)

primitiveGRSourceFactorisationLeafRequired : Bool
primitiveGRSourceFactorisationLeafRequired = false

primitiveGRSourceFactorisationLeafRequiredIsFalse :
  primitiveGRSourceFactorisationLeafRequired ≡ false
primitiveGRSourceFactorisationLeafRequiredIsFalse = refl

crossSectorGRToCMP119StressEqualityRequired : Bool
crossSectorGRToCMP119StressEqualityRequired = true

crossSectorGRToCMP119StressEqualityRequiredIsTrue :
  crossSectorGRToCMP119StressEqualityRequired ≡ true
crossSectorGRToCMP119StressEqualityRequiredIsTrue = refl
