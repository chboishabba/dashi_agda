module DASHI.Economics.AISlimMoECostCompression2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Economics.AIUbiquityRentInversionExact as Ubiquity
import DASHI.Economics.AICapitalRecoveryEntanglement2026Exact as Capital

------------------------------------------------------------------------
-- MICROSOFT SLIMMOE COST-COMPRESSION WITNESS
------------------------------------------------------------------------

slimMoEPaper : Source.AttributedSource
slimMoEPaper = Source.mkDOISource
  "Zichong Li; Chen Liang; Zixuan Zhang; Ilgee Hong; Young Jin Kim; Weizhu Chen; Tuo Zhao"
  "SlimMoE: Structured Compression of Large MoE Models via Expert Slimming and Distillation"
  "COLM 2025 / arXiv"
  "2025"
  "10.48550/arXiv.2506.18349"
  "https://arxiv.org/abs/2506.18349"
  Source.academicArticleSource
  "primary academic carrier for the reported Phi-3.5-MoE compression sizes, training-token budget, single-GPU fine-tuning feasibility and benchmark comparisons"
  Source.publicAttribution

record MoESizeReading : Set where
  constructor moeSizeReading
  field
    model : String
    totalParameters : String
    activatedParameters : String

open MoESizeReading public

phi35MoE : MoESizeReading
phi35MoE = moeSizeReading "Phi-3.5-MoE" "41.9B" "6.6B"

phiMiniMoE : MoESizeReading
phiMiniMoE = moeSizeReading "Phi-mini-MoE" "7.6B" "2.4B"

phiTinyMoE : MoESizeReading
phiTinyMoE = moeSizeReading "Phi-tiny-MoE" "3.8B" "1.1B"

record SlimMoECompressionReceipt : Set where
  constructor slimMoECompressionReceipt
  field
    source : Source.AttributedSource
    original : MoESizeReading
    mini : MoESizeReading
    tiny : MoESizeReading
    distillationTokens : String
    originalTrainingFractionReading : String
    miniSingleGPUFineTuning : Bool
    tinySingleGPUFineTuning : Bool
    qualityComparisonSourceBounded : Bool
    provesFrontierClosedNoMoat : Bool

open SlimMoECompressionReceipt public

canonicalSlimMoEReceipt : SlimMoECompressionReceipt
canonicalSlimMoEReceipt = slimMoECompressionReceipt
  slimMoEPaper
  phi35MoE
  phiMiniMoE
  phiTinyMoE
  "400B tokens"
  "reported as less than 10 percent of the original training-data budget"
  true
  true
  true
  false

------------------------------------------------------------------------
-- Economic interpretation boundary.
------------------------------------------------------------------------

record CostCompressionPressure : Set where
  constructor costCompressionPressure
  field
    activeParameterCountFalls : Bool
    memoryFootprintPressureFalls : Bool
    fineTuningAccessibilityRises : Bool
    substitutabilityPressureCanRise : Bool
    proprietaryPriceMustFall : Bool

open CostCompressionPressure public

slimMoECostCompressionPressure : CostCompressionPressure
slimMoECostCompressionPressure =
  costCompressionPressure true true true true false

data CompressionImpliesEquivalentCapabilityPermission : Set where
data SmallerModelImpliesLowerFullSystemCostPermission : Set where
data CompressionImpliesNoClosedMoatPermission : Set where

compressionDoesNotAutoProveEquivalentCapability :
  CompressionImpliesEquivalentCapabilityPermission → ⊥
compressionDoesNotAutoProveEquivalentCapability ()

smallerModelDoesNotAutoProveLowerFullSystemCost :
  SmallerModelImpliesLowerFullSystemCostPermission → ⊥
smallerModelDoesNotAutoProveLowerFullSystemCost ()

compressionDoesNotAutoProveNoClosedMoat :
  CompressionImpliesNoClosedMoatPermission → ⊥
compressionDoesNotAutoProveNoClosedMoat ()

ubiquityBoundary : Ubiquity.TechnologySuccessCapitalLossBoundary
ubiquityBoundary = Ubiquity.canonicalTechnologySuccessCapitalLossBoundary

scarcitySpreadType : Set₁
scarcitySpreadType = Capital.AIScarcityRentSpread
