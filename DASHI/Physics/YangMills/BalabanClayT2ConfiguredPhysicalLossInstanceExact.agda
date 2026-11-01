module DASHI.Physics.YangMills.BalabanClayT2ConfiguredPhysicalLossInstanceExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (_≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayCommonLogSixteenCertificateExact as Log16
import DASHI.Physics.YangMills.BalabanClayT2ConfiguredComponentLossBoundsExact as Components
import DASHI.Physics.YangMills.BalabanClayT2ConfiguredLossBudgetCertificateExact as Budget

------------------------------------------------------------------------
-- Literature normalization.
--
-- Barry Simon, "Trace Ideals and Their Applications", second edition,
-- American Mathematical Society (2005). DOI: 10.1090/surv/120
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. II. Cluster Expansions", Communications in Mathematical Physics
-- 116 (1988), 1--22. DOI: 10.1007/BF01239022
--
-- Relationship: the source mechanisms are represented by the component
-- witnesses.  This file performs only the exact order-embedding and
-- gain-minus-loss assembly into the final physical budget record.
------------------------------------------------------------------------

record ConfiguredEmbeddedPhysicalLossData
    (Scale Polymer Scalar : Set) : Set₁ where
  field
    logAuthority : Log16.LogSixteenAnalyticAuthority Scalar
    componentLosses : Components.ConfiguredPhysicalComponentLosses Scale Polymer

    actionGain : Scale → Polymer → Scalar
    actionGainDominatesConfigured : ∀ scale polymer →
      Log16.LessEqual logAuthority
        (Log16.rational logAuthority Budget.configuredActionGain)
        (actionGain scale polymer)

    add subtract : Scalar → Scalar → Scalar

    addMonotone : ∀ {a b c d} →
      Log16.LessEqual logAuthority a b →
      Log16.LessEqual logAuthority c d →
      Log16.LessEqual logAuthority (add a c) (add b d)

    subtractMonotoneAntitone : ∀ {actionLower action loss lossUpper} →
      Log16.LessEqual logAuthority actionLower action →
      Log16.LessEqual logAuthority loss lossUpper →
      Log16.LessEqual logAuthority
        (subtract actionLower lossUpper) (subtract action loss)

    rationalOrderEmbedding : ∀ {left right} →
      left ≤ right →
      Log16.LessEqual logAuthority
        (Log16.rational logAuthority left)
        (Log16.rational logAuthority right)

    rationalNestedLossExact :
      add
        (Log16.rational logAuthority Budget.configuredJacobianLoss)
        (add
          (Log16.rational logAuthority Budget.configuredDeterminantLoss)
          (add
            (Log16.rational logAuthority Budget.configuredBCHLoss)
            (add
              (Log16.rational logAuthority Budget.configuredLocalizationLoss)
              (Log16.rational logAuthority Budget.configuredPatchLoss))))
      ≡ Log16.rational logAuthority Budget.configuredTotalLoss

    rationalNetGainExact :
      subtract
        (Log16.rational logAuthority Budget.configuredActionGain)
        (Log16.rational logAuthority Budget.configuredTotalLoss)
      ≡ Log16.rational logAuthority Budget.configuredNetGain

open ConfiguredEmbeddedPhysicalLossData public

embeddedJacobianLoss dataSet scale polymer =
  Log16.rational (logAuthority dataSet)
    (Components.haarLoss (componentLosses dataSet) scale polymer)

embeddedDeterminantLoss dataSet scale polymer =
  Log16.rational (logAuthority dataSet)
    (Components.determinantLoss (componentLosses dataSet) scale polymer)

embeddedBCHLoss dataSet scale polymer =
  Log16.rational (logAuthority dataSet)
    (Components.bchLoss (componentLosses dataSet) scale polymer)

embeddedLocalizationLoss dataSet scale polymer =
  Log16.rational (logAuthority dataSet)
    (Components.localizationLoss (componentLosses dataSet) scale polymer)

embeddedPatchLoss dataSet scale polymer =
  Log16.rational (logAuthority dataSet)
    (Components.patchLoss (componentLosses dataSet) scale polymer)

embeddedTotalLoss dataSet scale polymer =
  add dataSet (embeddedJacobianLoss dataSet scale polymer)
    (add dataSet (embeddedDeterminantLoss dataSet scale polymer)
      (add dataSet (embeddedBCHLoss dataSet scale polymer)
        (add dataSet (embeddedLocalizationLoss dataSet scale polymer)
          (embeddedPatchLoss dataSet scale polymer))))

embeddedNetGain dataSet scale polymer =
  subtract dataSet (actionGain dataSet scale polymer)
    (embeddedTotalLoss dataSet scale polymer)

configuredPhysicalLossDominationInstance :
  ∀ {Scale Polymer Scalar} →
  ConfiguredEmbeddedPhysicalLossData Scale Polymer Scalar →
  Budget.ConfiguredPhysicalLossDomination Scale Polymer Scalar
configuredPhysicalLossDominationInstance dataSet = record
  { logAuthority = logAuthority dataSet
  ; actionGain = actionGain dataSet
  ; jacobianLoss =
      embeddedJacobianLoss dataSet
  ; determinantLoss =
      embeddedDeterminantLoss dataSet
  ; bchLoss = embeddedBCHLoss dataSet
  ; localizationLoss =
      embeddedLocalizationLoss dataSet
  ; patchLoss = embeddedPatchLoss dataSet
  ; add = add dataSet
  ; subtract = subtract dataSet
  ; addMonotone = addMonotone dataSet
  ; subtractMonotoneAntitone =
      subtractMonotoneAntitone dataSet
  ; actionGainDominatesConfigured =
      actionGainDominatesConfigured dataSet
  ; jacobianLossBelowConfigured =
      λ scale polymer → rationalOrderEmbedding dataSet
        (Components.haarLossBelowConfigured
          (componentLosses dataSet) scale polymer)
  ; determinantLossBelowConfigured =
      λ scale polymer → rationalOrderEmbedding dataSet
        (Components.determinantLossBelowConfigured
          (componentLosses dataSet) scale polymer)
  ; bchLossBelowConfigured =
      λ scale polymer → rationalOrderEmbedding dataSet
        (Components.bchLossBelowConfigured
          (componentLosses dataSet) scale polymer)
  ; localizationLossBelowConfigured =
      λ scale polymer → rationalOrderEmbedding dataSet
        (Components.localizationLossBelowConfigured
          (componentLosses dataSet) scale polymer)
  ; patchLossBelowConfigured =
      λ scale polymer → rationalOrderEmbedding dataSet
        (Components.patchLossBelowConfigured
          (componentLosses dataSet) scale polymer)
  ; totalLoss = embeddedTotalLoss dataSet
  ; netGain = embeddedNetGain dataSet
  ; totalLossDefinition =
      λ scale polymer → refl
  ; netGainDefinition =
      λ scale polymer → refl
  ; configuredTotalLossEmbeddingExact =
      rationalNestedLossExact dataSet
  ; configuredNetGainEmbeddingExact =
      rationalNetGainExact dataSet
  }

configuredEmbeddedLossInstanceLevel : ProofLevel
configuredEmbeddedLossInstanceLevel = machineChecked

physicalActionAndComponentInputsLevel : ProofLevel
physicalActionAndComponentInputsLevel = conditional
