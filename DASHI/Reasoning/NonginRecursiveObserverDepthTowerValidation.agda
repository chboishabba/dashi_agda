module DASHI.Reasoning.NonginRecursiveObserverDepthTowerValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.NonginRecursiveObserverDepthTowerExact as Tower

boundary : Tower.NonginRecursiveObserverDepthTowerBoundary
boundary = Tower.canonicalNonginRecursiveObserverDepthTowerBoundary

depthPresheafPaid : Tower.depthPresheafPaid boundary ≡ true
depthPresheafPaid = refl

coarseCollisionPaid : Tower.coarseCollisionPaid boundary ≡ true
coarseCollisionPaid = refl

residualReopeningPaid : Tower.residualReopeningPaid boundary ≡ true
residualReopeningPaid = refl

syntaxBridgePaid : Tower.observerTermBridgePaid boundary ≡ true
syntaxBridgePaid = refl

syntaxNotIdentifiedWithDepthSemantics :
  Tower.syntaxEqualsDepthSemantics boundary ≡ false
syntaxNotIdentifiedWithDepthSemantics = refl
