module DASHI.Reasoning.NonginRecursiveObserverFibreTowerBridgeValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.NonginRecursiveObserverFibreTowerBridgeExact as Bridge

boundary : Bridge.NonginRecursiveObserverFibreTowerBridgeBoundary
boundary = Bridge.canonicalNonginRecursiveObserverFibreTowerBridgeBoundary

fibreTowerAdapterPaid :
  Bridge.fibreTowerAdapterPaid boundary ≡ true
fibreTowerAdapterPaid = refl

inverseLimitFromObserverStreamPaid :
  Bridge.inverseLimitFromObserverStreamPaid boundary ≡ true
inverseLimitFromObserverStreamPaid = refl

historicalSyntaxProjectionCommutes :
  Bridge.historicalSyntaxProjectionCommutes boundary ≡ true
historicalSyntaxProjectionCommutes = refl

pAdicMetricStillNotPromoted :
  Bridge.pAdicMetricPromoted boundary ≡ false
pAdicMetricStillNotPromoted = refl
