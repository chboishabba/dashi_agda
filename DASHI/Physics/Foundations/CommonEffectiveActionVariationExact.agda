module DASHI.Physics.Foundations.CommonEffectiveActionVariationExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.HistoryLocalActionAccumulationExact as Local
import DASHI.Physics.Foundations.ActionPhaseLiftBoundaryExact as Phase
import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.SharedEffectiveSourceRecoveryExact as Source

------------------------------------------------------------------------
-- Forward BIDI compiler from an action-bearing microscopic description to the
-- shared effective source used by the QFT/GR weld.
--
-- The finite local-action owner supplies exact additivity and symmetry, but not
-- a physical continuum variation.  Accordingly this record does NOT invent a
-- derivative.  It requires the application to supply the effective source
-- variation and its coarse-graining commutation theorem explicitly.
------------------------------------------------------------------------

record CommonEffectiveActionVariation
    (U : Weld.UnifiedCandidate) : Set₁ where
  constructor commonEffectiveActionVariation
  field
    localActionSystem : Local.LocalActionSystem

    -- Same unified candidate represented in the finite action system.
    candidateActionState :
      Weld.Candidate U → Local.State localActionSystem

    -- Histories on which the finite action owner can be used.
    History : Set
    historySteps : History → List (Local.Step localActionSystem)

    finiteAction : History → Nat
    finiteActionIsLiteralHistoryAction : ∀ history →
      finiteAction history
      ≡ Local.historyAction localActionSystem (historySteps history)

    -- Continuum/effective source variation.  This is the physical theorem
    -- socket; finite Nat-valued additivity alone cannot construct it.
    effectiveSourceVariation :
      Weld.Candidate U → Weld.Regime U → Weld.SharedStressEnergy U

    sourceVariationAfterCoarseGraining :
      Weld.Candidate U → Weld.Regime U → Weld.SharedStressEnergy U

    sourceVariationCommutesWithCoarseGraining :
      ∀ candidate regime →
      sourceVariationAfterCoarseGraining candidate regime
      ≡ effectiveSourceVariation
          (Weld.coarseGrain U candidate regime) regime

open CommonEffectiveActionVariation public

variationBuildsSharedEffectiveSource :
  ∀ {U : Weld.UnifiedCandidate} →
  CommonEffectiveActionVariation U →
  Source.SharedEffectiveSourceTheory U
variationBuildsSharedEffectiveSource variation = record
  { Source.SharedEffectiveSourceTheory.effectiveSource =
      effectiveSourceVariation variation
  ; Source.SharedEffectiveSourceTheory.sourceAfterCoarseGraining =
      sourceVariationAfterCoarseGraining variation
  ; Source.SharedEffectiveSourceTheory.sourceCoarseGrainingCommutes =
      sourceVariationCommutesWithCoarseGraining variation
  }

------------------------------------------------------------------------
-- Literal sector identifications of that SAME variation.
------------------------------------------------------------------------

record EinsteinVariationIdentification
    {U : Weld.UnifiedCandidate}
    (variation : CommonEffectiveActionVariation U) : Set₁ where
  field
    variationEqualsEinsteinSource :
      ∀ candidate regime →
      Weld.grRegime U regime →
      Weld.grStressToShared U (Weld.coarseGrain U candidate regime)
        (Weld.actualGRStressEnergy U (Weld.coarseGrain U candidate regime))
      ≡
      effectiveSourceVariation variation
        (Weld.coarseGrain U candidate regime) regime

open EinsteinVariationIdentification public

record QFTVariationIdentification
    {U : Weld.UnifiedCandidate}
    (variation : CommonEffectiveActionVariation U) : Set₁ where
  field
    literalQFTStressAggregates : ∀ candidate →
      Weld.QFTStressAggregation U candidate
        (Weld.actualQFTSectorStressShared U candidate)
        (Weld.qftTotalStressShared U candidate)

    variationEqualsTotalQFTStress :
      ∀ candidate regime →
      Weld.qftRegime U regime →
      effectiveSourceVariation variation
        (Weld.coarseGrain U candidate regime) regime
      ≡
      Weld.qftTotalStressShared U (Weld.coarseGrain U candidate regime)

open QFTVariationIdentification public

variationIdentifiesGRSource :
  ∀ {U : Weld.UnifiedCandidate}
    (variation : CommonEffectiveActionVariation U) →
  EinsteinVariationIdentification variation →
  Source.GRSourceFactorisation (variationBuildsSharedEffectiveSource variation)
variationIdentifiesGRSource variation identification = record
  { Source.GRSourceFactorisation.grSourceFactorises =
      EinsteinVariationIdentification.variationEqualsEinsteinSource identification
  }

variationIdentifiesQFTSource :
  ∀ {U : Weld.UnifiedCandidate}
    (variation : CommonEffectiveActionVariation U) →
  QFTVariationIdentification variation →
  Source.QFTSourceFactorisation (variationBuildsSharedEffectiveSource variation)
variationIdentifiesQFTSource variation identification = record
  { Source.QFTSourceFactorisation.qftStressAggregates =
      QFTVariationIdentification.literalQFTStressAggregates identification
  ; Source.QFTSourceFactorisation.qftTotalSourceFactorises =
      QFTVariationIdentification.variationEqualsTotalQFTStress identification
  }

------------------------------------------------------------------------
-- The action-variation BIDI compiler closes the stress weld once the two
-- physical variation-identification theorems are supplied.
------------------------------------------------------------------------

commonVariationImpliesStressWeld :
  ∀ {U : Weld.UnifiedCandidate}
    (variation : CommonEffectiveActionVariation U) →
  EinsteinVariationIdentification variation →
  QFTVariationIdentification variation →
  Weld.StressEnergyWeldToken U →
  Weld.SameStressEnergyWeld U
commonVariationImpliesStressWeld variation grIdentification qftIdentification token =
  Source.sharedSourceImpliesSameStressEnergy
    (variationBuildsSharedEffectiveSource variation)
    (variationIdentifiesGRSource variation grIdentification)
    (variationIdentifiesQFTSource variation qftIdentification)
    token

------------------------------------------------------------------------
-- Boundary: this file deliberately stops where real analysis/physics begins.
------------------------------------------------------------------------

record CommonActionVariationBoundary : Set where
  constructor commonActionVariationBoundary
  field
    finiteAdditiveNatActionDefinesMetricFunctionalDerivative : Bool
    finiteAdditiveNatActionDefinesMetricFunctionalDerivativeIsFalse :
      finiteAdditiveNatActionDefinesMetricFunctionalDerivative ≡ false

    actionPhaseLiftDefinesStressTensor : Bool
    actionPhaseLiftDefinesStressTensorIsFalse :
      actionPhaseLiftDefinesStressTensor ≡ false

    separatelyNamedGRAndQFTActionsAreOneCommonAction : Bool
    separatelyNamedGRAndQFTActionsAreOneCommonActionIsFalse :
      separatelyNamedGRAndQFTActionsAreOneCommonAction ≡ false

    commonVariationPlusLiteralIdentificationsClosesStressWeld : Bool
    commonVariationPlusLiteralIdentificationsClosesStressWeldIsTrue :
      commonVariationPlusLiteralIdentificationsClosesStressWeld ≡ true

canonicalCommonActionVariationBoundary : CommonActionVariationBoundary
canonicalCommonActionVariationBoundary =
  commonActionVariationBoundary false refl false refl false refl true refl
