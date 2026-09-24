module DASHI.Wikimedia.IbrahimMonsterNineOrbitD4N3BScreenAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Wikimedia.IbrahimMonsterFiveOrbitD4KernelCharacterExact as Kernel
import DASHI.Wikimedia.IbrahimMonsterFiveOrbitD4N3BScreenReceiptExact as Screen

------------------------------------------------------------------------
-- Canonical NineOrbit -> merged five-point D4/N(3B) screen adapter.
--
-- The merged GAP screen uses point order
--   1 zero, 2 first-axis, 3 second-axis, 4 equal-sign, 5 opposite-sign
-- with generators r=(2 3)(4 5), s=(4 5).  Under the chart below these are
-- exactly Kernel.rotateOrbit and Kernel.reflectAxisOrbit.
--
-- This pays the carrier/action adapter only.  It imports no GAP verdict,
-- compatible fusion, actual subgroup realization, selected Monster action,
-- or intertwiner.
------------------------------------------------------------------------

data ScreenPoint5 : Set where
  screenPoint1 screenPoint2 screenPoint3 screenPoint4 screenPoint5 : ScreenPoint5

nineOrbitToScreenPoint : Triadic.NineOrbit → ScreenPoint5
nineOrbitToScreenPoint Triadic.zeroOrbit = screenPoint1
nineOrbitToScreenPoint Triadic.firstAxisOrbit = screenPoint2
nineOrbitToScreenPoint Triadic.secondAxisOrbit = screenPoint3
nineOrbitToScreenPoint Triadic.equalSignOrbit = screenPoint4
nineOrbitToScreenPoint Triadic.oppositeSignOrbit = screenPoint5

screenPointToNineOrbit : ScreenPoint5 → Triadic.NineOrbit
screenPointToNineOrbit screenPoint1 = Triadic.zeroOrbit
screenPointToNineOrbit screenPoint2 = Triadic.firstAxisOrbit
screenPointToNineOrbit screenPoint3 = Triadic.secondAxisOrbit
screenPointToNineOrbit screenPoint4 = Triadic.equalSignOrbit
screenPointToNineOrbit screenPoint5 = Triadic.oppositeSignOrbit

nineOrbitScreenRoundTrip :
  (o : Triadic.NineOrbit) → screenPointToNineOrbit (nineOrbitToScreenPoint o) ≡ o
nineOrbitScreenRoundTrip Triadic.zeroOrbit = refl
nineOrbitScreenRoundTrip Triadic.firstAxisOrbit = refl
nineOrbitScreenRoundTrip Triadic.secondAxisOrbit = refl
nineOrbitScreenRoundTrip Triadic.equalSignOrbit = refl
nineOrbitScreenRoundTrip Triadic.oppositeSignOrbit = refl

screenNineOrbitRoundTrip :
  (p : ScreenPoint5) → nineOrbitToScreenPoint (screenPointToNineOrbit p) ≡ p
screenNineOrbitRoundTrip screenPoint1 = refl
screenNineOrbitRoundTrip screenPoint2 = refl
screenNineOrbitRoundTrip screenPoint3 = refl
screenNineOrbitRoundTrip screenPoint4 = refl
screenNineOrbitRoundTrip screenPoint5 = refl

screenQuarterTurn : ScreenPoint5 → ScreenPoint5
screenQuarterTurn screenPoint1 = screenPoint1
screenQuarterTurn screenPoint2 = screenPoint3
screenQuarterTurn screenPoint3 = screenPoint2
screenQuarterTurn screenPoint4 = screenPoint5
screenQuarterTurn screenPoint5 = screenPoint4

screenAxisReflection : ScreenPoint5 → ScreenPoint5
screenAxisReflection screenPoint1 = screenPoint1
screenAxisReflection screenPoint2 = screenPoint2
screenAxisReflection screenPoint3 = screenPoint3
screenAxisReflection screenPoint4 = screenPoint5
screenAxisReflection screenPoint5 = screenPoint4

kernelQuarterTurn : Triadic.NineOrbit → Triadic.NineOrbit
kernelQuarterTurn = Kernel.rotateOrbit

kernelAxisReflection : Triadic.NineOrbit → Triadic.NineOrbit
kernelAxisReflection = Kernel.reflectAxisOrbit

quarterTurnEquivariance :
  (o : Triadic.NineOrbit) →
  nineOrbitToScreenPoint (kernelQuarterTurn o) ≡ screenQuarterTurn (nineOrbitToScreenPoint o)
quarterTurnEquivariance Triadic.zeroOrbit = refl
quarterTurnEquivariance Triadic.firstAxisOrbit = refl
quarterTurnEquivariance Triadic.secondAxisOrbit = refl
quarterTurnEquivariance Triadic.equalSignOrbit = refl
quarterTurnEquivariance Triadic.oppositeSignOrbit = refl

axisReflectionEquivariance :
  (o : Triadic.NineOrbit) →
  nineOrbitToScreenPoint (kernelAxisReflection o) ≡ screenAxisReflection (nineOrbitToScreenPoint o)
axisReflectionEquivariance Triadic.zeroOrbit = refl
axisReflectionEquivariance Triadic.firstAxisOrbit = refl
axisReflectionEquivariance Triadic.secondAxisOrbit = refl
axisReflectionEquivariance Triadic.equalSignOrbit = refl
axisReflectionEquivariance Triadic.oppositeSignOrbit = refl

kernelCharacterBoundary : Kernel.FiveOrbitD4KernelCharacterBoundary
kernelCharacterBoundary = Kernel.currentFiveOrbitD4KernelCharacterBoundary

mergedScreenReceipt : Screen.FiveOrbitD4N3BScreenReceipt
mergedScreenReceipt = Screen.currentFiveOrbitD4N3BScreenReceipt

data AdapterCreatesGAPRuntimeVerdict : Set where
data AdapterCreatesSelectedMonsterAction : Set where
data FivePointBijectionCreatesCharacterCompatibility : Set where

adapterDoesNotCreateGAPRuntimeVerdict : AdapterCreatesGAPRuntimeVerdict → ⊥
adapterDoesNotCreateGAPRuntimeVerdict ()
adapterDoesNotCreateSelectedMonsterAction : AdapterCreatesSelectedMonsterAction → ⊥
adapterDoesNotCreateSelectedMonsterAction ()
fivePointBijectionDoesNotCreateCharacterCompatibility : FivePointBijectionCreatesCharacterCompatibility → ⊥
fivePointBijectionDoesNotCreateCharacterCompatibility ()

record NineOrbitScreenAdapterBoundary : Set where
  constructor nineorbit-screen-adapter-boundary
  field
    canonicalNineOrbitCarrierReused : Bool
    mergedKernelD4ActionReused : Bool
    mergedN3BScreenReceiptReused : Bool
    pointOrderBijectionPaid : Bool
    quarterTurnGeneratorEquivariancePaid : Bool
    axisReflectionGeneratorEquivariancePaid : Bool
    nineOrbitToMergedScreenAdapterPaid : Bool
    gapRuntimeVerdictImported : Bool
    characterCompatibleFusionImported : Bool
    adapterCreatesSelectedMonsterAction : Bool
    nextResidual : String
open NineOrbitScreenAdapterBoundary public

currentNineOrbitScreenAdapterBoundary : NineOrbitScreenAdapterBoundary
currentNineOrbitScreenAdapterBoundary =
  nineorbit-screen-adapter-boundary
    true true true true true true true false false false
    "Canonical NineOrbit is explicitly charted to the five-point carrier consumed by the merged D4/N(3B) screen. The GAP generators r=(2 3)(4 5) and s=(4 5) agree under this chart with the existing kernel quarter-turn and axis-reflection actions. No GAP runtime verdict, compatible fusion, actual D4 subgroup, selected Monster action, or intertwiner is imported. The remaining debt is execution/certification of the already-merged screen on a current revision."

nineOrbitToMergedScreenAdapterPaidIsTrue :
  nineOrbitToMergedScreenAdapterPaid currentNineOrbitScreenAdapterBoundary ≡ true
nineOrbitToMergedScreenAdapterPaidIsTrue = refl

gapRuntimeVerdictImportedIsFalse :
  gapRuntimeVerdictImported currentNineOrbitScreenAdapterBoundary ≡ false
gapRuntimeVerdictImportedIsFalse = refl

adapterCreatesSelectedMonsterActionIsFalse :
  adapterCreatesSelectedMonsterAction currentNineOrbitScreenAdapterBoundary ≡ false
adapterCreatesSelectedMonsterActionIsFalse = refl
