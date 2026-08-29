module DASHI.Physics.Foundations.SharedEffectiveSourceRecoveryExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as QFT

------------------------------------------------------------------------
-- BIDI source seam.
--
-- The previous tranche made equality of the literal GR source and literal QFT
-- stress tensor an explicit obligation.  This module factors that equality
-- through ONE effective source produced from the SAME coarse-grained candidate.
--
--       literal GR StressEnergy
--                |
--                v
--       shared effective source
--                |
--                v
--       literal QFT stressTensor
--
-- Therefore the cross-sector weld is derived by equality transitivity once the
-- two sector-identification theorems are supplied.  The weld itself is not a
-- new independent physical assumption.
------------------------------------------------------------------------

record SharedEffectiveSourceTheory (U : Weld.UnifiedCandidate) : Set₁ where
  constructor sharedEffectiveSourceTheory
  field
    -- One source functional/output at one candidate and one declared regime.
    effectiveSource :
      Weld.Candidate U → Weld.Regime U → Weld.SharedStressEnergy U

    -- Optional finite/microscopic provenance is represented as a literal
    -- commutation law, not by the name "effective action" alone.
    sourceAfterCoarseGraining :
      Weld.Candidate U → Weld.Regime U → Weld.SharedStressEnergy U

    sourceCoarseGrainingCommutes :
      ∀ candidate regime →
      sourceAfterCoarseGraining candidate regime
      ≡ effectiveSource (Weld.coarseGrain U candidate regime) regime

open SharedEffectiveSourceTheory public

------------------------------------------------------------------------
-- Sector factorisations through the common source.
------------------------------------------------------------------------

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
    qftSourceFactorises :
      ∀ candidate regime group →
      Weld.qftRegime U regime →
      effectiveSource source (Weld.coarseGrain U candidate regime) regime
      ≡
      Weld.qftStressToShared U
        (Weld.actualQFTStressTensor U
          (Weld.coarseGrain U candidate regime) group)

open QFTSourceFactorisation public

------------------------------------------------------------------------
-- The same-object theorem: two factorisations through one source imply the
-- literal stress-energy weld required by the unification consumer.
------------------------------------------------------------------------

sharedSourceImpliesSameStressEnergy :
  ∀ {U : Weld.UnifiedCandidate}
    (source : SharedEffectiveSourceTheory U) →
  GRSourceFactorisation source →
  QFTSourceFactorisation source →
  Weld.StressEnergyWeldToken U →
  Weld.SameStressEnergyWeld U
sharedSourceImpliesSameStressEnergy source grFactor qftFactor token = record
  { Weld.SameStressEnergyWeld.sameStressEnergyOnOverlap =
      λ candidate regime group grAtRegime qftAtRegime →
        trans
          (GRSourceFactorisation.grSourceFactorises
            grFactor candidate regime grAtRegime)
          (QFTSourceFactorisation.qftSourceFactorises
            qftFactor candidate regime group qftAtRegime)
  ; Weld.SameStressEnergyWeld.stressWeldPromotionToken = token
  }

------------------------------------------------------------------------
-- Common-regime source dynamics.
--
-- Backreaction and correction control remain physical theorems.  What this
-- layer enforces is that they are stated on the SAME coarse-grained candidate
-- and the SAME overlap regime used by the stress-source factorisation.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Combined cross-sector compiler.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Why this is a genuine compression of the frontier.
--
-- Once an application proves the two factorisations, stress-energy equality is
-- downstream algebra.  The remaining mathematics is therefore concentrated in
-- deriving ONE effective source from the microscopic candidate and proving its
-- GR and QFT identifications under one coarse-graining convention.
------------------------------------------------------------------------

record SharedSourceBoundary : Set where
  constructor sharedSourceBoundary
  field
    namingOneObjectEffectiveActionProvesStressWeld : Bool
    namingOneObjectEffectiveActionProvesStressWeldIsFalse :
      namingOneObjectEffectiveActionProvesStressWeld ≡ false

    separateGRAndQFTSourceFitsProveSameObject : Bool
    separateGRAndQFTSourceFitsProveSameObjectIsFalse :
      separateGRAndQFTSourceFitsProveSameObject ≡ false

    twoExactFactorisationsThroughOneSourceProveWeld : Bool
    twoExactFactorisationsThroughOneSourceProveWeldIsTrue :
      twoExactFactorisationsThroughOneSourceProveWeld ≡ true

canonicalSharedSourceBoundary : SharedSourceBoundary
canonicalSharedSourceBoundary =
  sharedSourceBoundary false refl false refl true refl
