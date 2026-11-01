module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseObservableIdentityPromotionGateValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseObservableIdentityPromotionGateExact as Gate

positiveEndpointPromotionAllowed :
  Gate.ObservablePromotionReceipt.numericPromotionAllowed Gate.openEndpointDLnPromotionReceipt ≡ true
positiveEndpointPromotionAllowed = refl

sameLabelOnlyPromotionBlocked :
  Gate.ObservablePromotionReceipt.numericPromotionAllowed Gate.sameLabelOnlyDLnPromotionAttempt ≡ false
sameLabelOnlyPromotionBlocked = refl

articleIdentityOnlyPromotionBlocked :
  Gate.ObservablePromotionReceipt.numericPromotionAllowed Gate.articleIdentityOnlyPromotionAttempt ≡ false
articleIdentityOnlyPromotionBlocked = refl

boundaryRetainsDefinitionGate :
  Gate.AdKObservableIdentityPromotionBoundary.observableDefinitionRequired
    Gate.canonicalAdKObservableIdentityPromotionBoundary ≡ true
boundaryRetainsDefinitionGate = refl

boundaryBlocksLabelOnlyIdentity :
  Gate.AdKObservableIdentityPromotionBoundary.sameVariableLabelCreatesSameObservable
    Gate.canonicalAdKObservableIdentityPromotionBoundary ≡ false
boundaryBlocksLabelOnlyIdentity = refl
