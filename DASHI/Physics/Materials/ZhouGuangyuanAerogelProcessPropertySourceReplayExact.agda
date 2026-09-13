module DASHI.Physics.Materials.ZhouGuangyuanAerogelProcessPropertySourceReplayExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Materials.ZhouGuangyuanPolyimideAerogelBidiExact as Base

record ZhouProcessPropertyReplay : Set where
  constructor zhou-process-property-replay
  field
    sourceReference : String
    minimumReportedShrinkageTenthsPercent : Nat
    minimumReportedPorosityPercent : Nat
    specificSurfaceAreaTenthsM2PerG : Nat
    td5MinimumC : Nat
    tgMinimumC : Nat
    conductivityAt200CTenthsMilliWPerMPerK : Nat
    exactMultiSampleTablePaid : Bool
    exactSynthesisRecipePaid : Bool

open ZhouProcessPropertyReplay public

zhouProcessPropertyReplay : ZhouProcessPropertyReplay
zhouProcessPropertyReplay = zhou-process-property-replay
  "DOI 10.1016/j.cej.2023.147642"
  77
  91
  6748
  580
  299
  543
  false
  false

baseState : Base.PolyimideAerogelState
baseState = Base.canonicalZhouAerogelState

scalarPropertyPortfolioIsSourceBacked : Bool
scalarPropertyPortfolioIsSourceBacked = true

scalarPortfolioDefinesUniversalProcessLaw : Bool
scalarPortfolioDefinesUniversalProcessLaw = false

multiSampleReplayStillRequired : Bool
multiSampleReplayStillRequired = true
