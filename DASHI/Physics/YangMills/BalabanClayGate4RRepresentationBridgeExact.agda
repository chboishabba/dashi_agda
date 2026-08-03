module DASHI.Physics.YangMills.BalabanClayGate4RRepresentationBridgeExact where

open import Data.Rational using (_*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRationalConstantsExact as BishopConstants
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geometric
import DASHI.Physics.YangMills.BalabanCriticalMapRGCutsetCompletion as ExistingRG
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanClayGate4CountingAndLocalizationReuseExact as Reuse

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
-- Project Euclid stable identifier: euclid:cmp/1104161193.
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
------------------------------------------------------------------------

record ConcreteRRepresentationBridge
    {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density Scale Volume Root : Set}
    (rg : ExistingRG.OneStepRGCutset Configuration Background Fluctuation
      GaugeOrbit Polymer Region Coupling Bound Density)
    (shellData : Shell.TraversalShellData Scale Volume Root)
    (RExpression : Set) : Set₁ where
  field
    rootedFamily : Reuse.ExactRootedFamilyRepresentation
      Scale Volume Root shellData
    expressionToFamily : RExpression → Reuse.Family rootedFamily
    localization : Reuse.RLocalizationNormInterpretation rg RExpression

open ConcreteRRepresentationBridge public

rExpressionRootedCounting :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density Scale Volume Root RExpression}
    {rg : ExistingRG.OneStepRGCutset Configuration Background Fluctuation
      GaugeOrbit Polymer Region Coupling Bound Density}
    {shellData : Shell.TraversalShellData Scale Volume Root}
    (bridge : ConcreteRRepresentationBridge rg shellData RExpression)
    (expression : RExpression) →
  Reuse.familyMass (rootedFamily bridge) (expressionToFamily bridge expression)
  ≤ BishopConstants.quarter * Geometric.halfPower
      (Reuse.depthOf (rootedFamily bridge)
        (expressionToFamily bridge expression))
rExpressionRootedCounting bridge expression =
  Reuse.exactRootedFamilyCounting
    (rootedFamily bridge) (expressionToFamily bridge expression)

rExpressionLocalizationBudget :
  ∀ {Configuration Background Fluctuation GaugeOrbit Polymer Region Coupling
      Bound Density Scale Volume Root RExpression}
    {rg : ExistingRG.OneStepRGCutset Configuration Background Fluctuation
      GaugeOrbit Polymer Region Coupling Bound Density}
    {shellData : Shell.TraversalShellData Scale Volume Root}
    (bridge : ConcreteRRepresentationBridge rg shellData RExpression)
    expression →
  ExistingRG.LessEqual rg
    (Reuse.localizedNorm (localization bridge) expression)
    (Reuse.localizationNormUpper (localization bridge) expression)
rExpressionLocalizationBudget bridge =
  Reuse.rLocalizationBudgetFromExistingRG (localization bridge)

rRepresentationBridgeAssemblyLevel : ProofLevel
rRepresentationBridgeAssemblyLevel = machineChecked

rRootedCountingConsequenceLevel : ProofLevel
rRootedCountingConsequenceLevel = machineChecked

rLocalizationBudgetConsequenceLevel : ProofLevel
rLocalizationBudgetConsequenceLevel = machineChecked

rExpressionToCanonicalRootedFamilyInputsLevel : ProofLevel
rExpressionToCanonicalRootedFamilyInputsLevel = conditional

rExpressionLocalizationMeaningInputsLevel : ProofLevel
rExpressionLocalizationMeaningInputsLevel = conditional
