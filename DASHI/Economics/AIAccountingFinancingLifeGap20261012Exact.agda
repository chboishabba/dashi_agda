module DASHI.Economics.AIAccountingFinancingLifeGap20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Economics.AICoreWeaveAssetLifeObsolescenceBoundary20261012Exact as CoreWeaveLife
import DASHI.Economics.AICapitalParetoAcquisitionSourceAtlas2026Exact as Sources
import DASHI.Economics.AICoreWeaveSameObjectFinancingClock20261016Exact as SameObject

------------------------------------------------------------------------
-- CROSS-OBJECT ACCOUNTING / GENERIC-MARKET HORIZON COMPARISON
--
-- This owner is retained as historical/source context, but Oct-16 primary
-- CoreWeave credit-agreement evidence changes its promotion status.
------------------------------------------------------------------------

record LifeGapObservation : Set where
  constructor life-gap-observation
  field
    accountingEntity : String
    accountingAssetClass : String
    accountingLifeMonths : Nat
    financingAssetClass : String
    lenderHorizonLowerMonths : Nat
    lenderHorizonUpperMonths : Nat
    gapLowerMonths : Nat
    gapUpperMonths : Nat
    sameEntityAppraisal : Bool
    sameAccountingDefinition : Bool
    lifeGapIsObsolescencePressureEvidence : Bool
    crossObjectStressScenarioOnly : Bool
    coreWeaveEconomicLifeIdentified : Bool
    impairmentEstablished : Bool
    replacementCapexIdentified : Bool
    accountingSource : Source.AttributedSource
    financingSource : Source.AttributedSource

open LifeGapObservation public

coreWeaveAccountingVsLenderGPUHorizon : LifeGapObservation
coreWeaveAccountingVsLenderGPUHorizon = life-gap-observation
  "CoreWeave"
  "technology equipment used in data centers"
  72
  "generic GPU collateral / AI chips"
  36
  48
  24
  36
  false
  false
  false
  true
  false
  false
  false
  CoreWeaveLife.coreWeave2025AnnualReportSource
  Sources.gpuCollateralReuters20261001

coreWeaveAccountingLifeMonthsIs72 : accountingLifeMonths coreWeaveAccountingVsLenderGPUHorizon ≡ 72
coreWeaveAccountingLifeMonthsIs72 = refl

lenderHorizonLowerMonthsIs36 : lenderHorizonLowerMonths coreWeaveAccountingVsLenderGPUHorizon ≡ 36
lenderHorizonLowerMonthsIs36 = refl

lenderHorizonUpperMonthsIs48 : lenderHorizonUpperMonths coreWeaveAccountingVsLenderGPUHorizon ≡ 48
lenderHorizonUpperMonthsIs48 = refl

selectedGapLowerMonthsIs24 : gapLowerMonths coreWeaveAccountingVsLenderGPUHorizon ≡ 24
selectedGapLowerMonthsIs24 = refl

selectedGapUpperMonthsIs36 : gapUpperMonths coreWeaveAccountingVsLenderGPUHorizon ≡ 36
selectedGapUpperMonthsIs36 = refl

upperLenderHorizonPlusLowerGapIsAccountingLife :
  lenderHorizonUpperMonths coreWeaveAccountingVsLenderGPUHorizon +
  gapLowerMonths coreWeaveAccountingVsLenderGPUHorizon ≡
  accountingLifeMonths coreWeaveAccountingVsLenderGPUHorizon
upperLenderHorizonPlusLowerGapIsAccountingLife = refl

lowerLenderHorizonPlusUpperGapIsAccountingLife :
  lenderHorizonLowerMonths coreWeaveAccountingVsLenderGPUHorizon +
  gapUpperMonths coreWeaveAccountingVsLenderGPUHorizon ≡
  accountingLifeMonths coreWeaveAccountingVsLenderGPUHorizon
lowerLenderHorizonPlusUpperGapIsAccountingLife = refl

obsolescencePressureCoordinatePaid :
  lifeGapIsObsolescencePressureEvidence coreWeaveAccountingVsLenderGPUHorizon ≡ false
obsolescencePressureCoordinatePaid = refl

crossObjectScenarioRetained :
  crossObjectStressScenarioOnly coreWeaveAccountingVsLenderGPUHorizon ≡ true
crossObjectScenarioRetained = refl

sameObjectCorrectionPaid :
  SameObject.commonObservedContractualGPUUsefulLifeMonths SameObject.coreWeaveSameObjectFinancingClock ≡ 72
sameObjectCorrectionPaid = SameObject.sameObjectSixYearDepreciationPaid

coreWeaveEconomicLifeStillOpen : coreWeaveEconomicLifeIdentified coreWeaveAccountingVsLenderGPUHorizon ≡ false
coreWeaveEconomicLifeStillOpen = refl

data GenericLenderHorizonDeterminesCoreWeaveEconomicLifePermission : Set where
data AccountingFinancingGapImpliesImpairmentPermission : Set where
data AccountingFinancingGapDeterminesReplacementCapexPermission : Set where

genericLenderHorizonDoesNotDetermineCoreWeaveEconomicLife : GenericLenderHorizonDeterminesCoreWeaveEconomicLifePermission → ⊥
genericLenderHorizonDoesNotDetermineCoreWeaveEconomicLife ()

lifeGapDoesNotAutoProveImpairment : AccountingFinancingGapImpliesImpairmentPermission → ⊥
lifeGapDoesNotAutoProveImpairment ()

lifeGapDoesNotDetermineReplacementCapex : AccountingFinancingGapDeterminesReplacementCapexPermission → ⊥
lifeGapDoesNotDetermineReplacementCapex ()

boundary : String
boundary =
  "The arithmetic 72-versus-36-48-month comparison is retained only as a cross-object market stress scenario. It is no longer promoted as a CoreWeave obsolescence-pressure coordinate because primary CoreWeave GPU-backed credit agreements disclose same-object contractual depreciation bases of about 66-78 months, commonly six years, including used-GPU contribution mechanics. The generic market report and CoreWeave accounting policy have different objects and definitions. Realised CoreWeave economic life, impairment, refresh schedule and replacement capex remain empirical."
