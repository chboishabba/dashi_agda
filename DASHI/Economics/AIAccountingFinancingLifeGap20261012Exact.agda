module DASHI.Economics.AIAccountingFinancingLifeGap20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Economics.AICoreWeaveAssetLifeObsolescenceBoundary20261012Exact as CoreWeaveLife
import DASHI.Economics.AICapitalParetoAcquisitionSourceAtlas2026Exact as Sources

------------------------------------------------------------------------
-- ACCOUNTING-LIFE / FINANCING-LIFE GAP
--
-- CoreWeave's primary filing uses a six-year accounting useful life for its
-- technology equipment. Separately, Reuters reports lender/credit practice
-- applying roughly three-to-four-year GPU depreciation horizons in AI-chip
-- collateral structures. The scopes are not identical: the lender evidence is
-- market-generic and secondary rather than a CoreWeave-specific appraisal.
--
-- The comparison nevertheless pays a bounded financing-vs-accounting horizon
-- mismatch: 24-36 months shorter on the lender side. This is an obsolescence /
-- collateral-pressure coordinate, not an impairment theorem or a replacement-
-- capex estimate.
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
  "GPU collateral / AI chips"
  36
  48
  24
  36
  false
  false
  true
  false
  false
  false
  CoreWeaveLife.coreWeave2025AnnualReportSource
  Sources.gpuCollateralReuters20261001

coreWeaveAccountingLifeMonthsIs72 :
  accountingLifeMonths coreWeaveAccountingVsLenderGPUHorizon ≡ 72
coreWeaveAccountingLifeMonthsIs72 = refl

lenderHorizonLowerMonthsIs36 :
  lenderHorizonLowerMonths coreWeaveAccountingVsLenderGPUHorizon ≡ 36
lenderHorizonLowerMonthsIs36 = refl

lenderHorizonUpperMonthsIs48 :
  lenderHorizonUpperMonths coreWeaveAccountingVsLenderGPUHorizon ≡ 48
lenderHorizonUpperMonthsIs48 = refl

selectedGapLowerMonthsIs24 :
  gapLowerMonths coreWeaveAccountingVsLenderGPUHorizon ≡ 24
selectedGapLowerMonthsIs24 = refl

selectedGapUpperMonthsIs36 :
  gapUpperMonths coreWeaveAccountingVsLenderGPUHorizon ≡ 36
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
  lifeGapIsObsolescencePressureEvidence coreWeaveAccountingVsLenderGPUHorizon ≡ true
obsolescencePressureCoordinatePaid = refl

coreWeaveEconomicLifeStillOpen :
  coreWeaveEconomicLifeIdentified coreWeaveAccountingVsLenderGPUHorizon ≡ false
coreWeaveEconomicLifeStillOpen = refl

data GenericLenderHorizonDeterminesCoreWeaveEconomicLifePermission : Set where
data AccountingFinancingGapImpliesImpairmentPermission : Set where
data AccountingFinancingGapDeterminesReplacementCapexPermission : Set where

genericLenderHorizonDoesNotDetermineCoreWeaveEconomicLife :
  GenericLenderHorizonDeterminesCoreWeaveEconomicLifePermission → ⊥
genericLenderHorizonDoesNotDetermineCoreWeaveEconomicLife ()

lifeGapDoesNotAutoProveImpairment :
  AccountingFinancingGapImpliesImpairmentPermission → ⊥
lifeGapDoesNotAutoProveImpairment ()

lifeGapDoesNotDetermineReplacementCapex :
  AccountingFinancingGapDeterminesReplacementCapexPermission → ⊥
lifeGapDoesNotDetermineReplacementCapex ()

boundary : String
boundary =
  "CoreWeave accounts for technology equipment over 72 months, while secondary market evidence reports roughly 36-48 month lender depreciation horizons for GPU collateral. The resulting selected 24-36 month horizon mismatch is a source-bounded financing/obsolescence pressure coordinate. The scopes are not the same entity appraisal or accounting definition, so the gap does not identify CoreWeave's economic retirement life, impairment, refresh schedule or replacement capex."
