module DASHI.Wikimedia.IbrahimMonster369OEISSeparatingHyperfabricValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Wikimedia.IbrahimMonster369OEISSeparatingHyperfabricExact as H

boundary : H.Monster369SeparatingHyperfabricBoundary
boundary = H.canonicalMonster369SeparatingHyperfabricBoundary

reusesExistingAtlasRegression :
  H.reusesExistingOEIS369Atlas boundary ≡ true
reusesExistingAtlasRegression = refl

typedCoordinatesRegression :
  H.typedMonsterCoordinatesRetained boundary ≡ true
typedCoordinatesRegression = refl

consumerEdgesRegression :
  H.monsterNativeConsumerEdgesTyped boundary ≡ true
consumerEdgesRegression = refl

typedSelectionHitsRegression :
  H.canonicalTypedSelectionHitsEveryDeclaredConsumer boundary ≡ true
typedSelectionHitsRegression = refl

oeisOnlyFailsRegression :
  H.oeisOnlySelectionHitsEveryRepresentationConsumer boundary ≡ false
oeisOnlyFailsRegression = refl

semanticFirewallRegression :
  H.oeisIdentityCreatesMonsterAction boundary ≡ false
semanticFirewallRegression = refl

minimumFirewallRegression :
  H.minimumHittingSetKernelProved boundary ≡ false
minimumFirewallRegression = refl

residualRegression :
  H.consumerCollisionReopensTypedResidual boundary ≡ true
residualRegression = refl
