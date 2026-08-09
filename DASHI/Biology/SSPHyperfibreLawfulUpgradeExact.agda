module DASHI.Biology.SSPHyperfibreLawfulUpgradeExact where

open import DASHI.Core.Prelude

import DASHI.Core.IndexedWeaveHyperfabricExact as Indexed
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SSP
import DASHI.Biology.SSPHyperfibreSymmetryTowerExact as Tower
import DASHI.Biology.SSPIndexedWeaveHyperfabricExact as Lawful

------------------------------------------------------------------------
-- Compatibility with the pre-existing indexed hyperfabric implementation.
--
-- The old atlas already had prime-indexed fibres, typed paths, transport and
-- residuals, but no identity/composition laws.  This module maps each legacy
-- path to the lawful weave and proves transport and residual agreement.
------------------------------------------------------------------------

upgradeLegacyPath :
  {source target : SSP.SSPPrime} →
  Tower.LanePath source target →
  Lawful.SSPWeavePath source target
upgradeLegacyPath (Tower.identityLanePath lane) =
  Lawful.lanePath SSP.mediatedOrientation
upgradeLegacyPath (Tower.forwardLanePath source target) =
  Lawful.lanePath SSP.forwardOrientation
upgradeLegacyPath (Tower.inverseLanePath source target) =
  Lawful.lanePath SSP.inverseOrientation

legacyFibreAgrees :
  (lane : SSP.SSPPrime) →
  Tower.Fibre Tower.canonicalSSPHyperfibreAtlas lane
  ≡ Lawful.SSPWeaveState lane
legacyFibreAgrees lane = refl

legacyTransportAgrees :
  {source target : SSP.SSPPrime} →
  (path : Tower.LanePath source target) →
  (state : Tower.LaneState) →
  Lawful.transportSSP (upgradeLegacyPath path) state
  ≡ Tower.transport Tower.canonicalSSPHyperfibreAtlas path state
legacyTransportAgrees (Tower.identityLanePath lane) state = refl
legacyTransportAgrees (Tower.forwardLanePath source target) state = refl
legacyTransportAgrees (Tower.inverseLanePath source target) state = refl

legacyResidualAgrees :
  {source target : SSP.SSPPrime} →
  (path : Tower.LanePath source target) →
  (state : Tower.LaneState) →
  Lawful.sspResidualAfter (upgradeLegacyPath path) state
  ≡ Tower.residualAfter Tower.canonicalSSPHyperfibreAtlas path state
legacyResidualAgrees (Tower.identityLanePath lane) state = refl
legacyResidualAgrees (Tower.forwardLanePath source target) state = refl
legacyResidualAgrees (Tower.inverseLanePath source target) state = refl

canonicalSSPHyperfibreLawfulUpgrade :
  Indexed.LawfulHyperfibreUpgrade SSP.SSPPrime Lawful.SSPWeaveState
canonicalSSPHyperfibreLawfulUpgrade =
  Indexed.lawfulHyperfibreUpgrade Lawful.canonicalSSPIndexedWeave

record LegacyAtlasUpgradeBoundary : Set where
  constructor legacyAtlasUpgradeBoundary
  field
    pathUpgrade :
      {source target : SSP.SSPPrime} →
      Tower.LanePath source target →
      Lawful.SSPWeavePath source target
    transportAgreement :
      {source target : SSP.SSPPrime} →
      (path : Tower.LanePath source target) →
      (state : Tower.LaneState) →
      Lawful.transportSSP (pathUpgrade path) state
      ≡ Tower.transport Tower.canonicalSSPHyperfibreAtlas path state
    residualAgreement :
      {source target : SSP.SSPPrime} →
      (path : Tower.LanePath source target) →
      (state : Tower.LaneState) →
      Lawful.sspResidualAfter (pathUpgrade path) state
      ≡ Tower.residualAfter Tower.canonicalSSPHyperfibreAtlas path state

canonicalLegacyAtlasUpgradeBoundary : LegacyAtlasUpgradeBoundary
canonicalLegacyAtlasUpgradeBoundary =
  legacyAtlasUpgradeBoundary
    upgradeLegacyPath
    legacyTransportAgrees
    legacyResidualAgrees
