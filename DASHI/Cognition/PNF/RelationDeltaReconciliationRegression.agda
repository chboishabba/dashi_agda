module DASHI.Cognition.PNF.RelationDeltaReconciliationRegression where

open import Agda.Builtin.Equality using (refl)
open import DASHI.Cognition.PNF.RelationDeltaReconciliationExact

oneAddOneRemoveOneReplaceOneSkip : RelationDeltaReceipt
oneAddOneRemoveOneReplaceOneSkip =
  relationDeltaReceipt
    3
    3
    1
    1
    1
    1
    4
    refl
    refl
    refl

transitionBoundary : RelationDeltaTransitionBoundary
transitionBoundary =
  relationDeltaTransitionBoundary
    oneAddOneRemoveOneReplaceOneSkip
    4
    refl
