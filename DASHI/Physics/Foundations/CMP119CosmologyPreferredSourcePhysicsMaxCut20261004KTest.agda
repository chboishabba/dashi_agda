{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261004KTest where

import DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261004KExact as K

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat)

regressionResidualCount : Nat
regressionResidualCount = K.preferredSourceEvidenceResidualCount

regressionCompilerDebtCount : Nat
regressionCompilerDebtCount = K.remainingCompilerDebtCount

regressionA1NaturalityIsPreferred : Bool
regressionA1NaturalityIsPreferred = K.a1PreferredProducerIsSourceNaturalityAndGeometry

regressionA2StillPhysical : Bool
regressionA2StillPhysical = K.a2SelectedInsertionSemanticsRemainsSourceEvidence

regressionB1StillPhysical : Bool
regressionB1StillPhysical = K.b1DirectTailAnchorRemainsSourceEvidence

regressionB1CannotMoveScaleForFree : Bool
regressionB1CannotMoveScaleForFree = K.singleCutoffB1DoesNotProvideLaterCutoffB1

regressionB2IsPartitionResponse : Bool
regressionB2IsPartitionResponse = K.b2PreferredProducerIsPartitionDerivativeTailDominance

regressionCompilerSaturated : Bool
regressionCompilerSaturated = K.preferredRouteCompilerSaturated
