module DASHI.Foundations.JChartSuccessorBoundary where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.String using (String)

record ChartIndex : Set where
  constructor chart
  field chartNat : Nat
open ChartIndex public

nextChart : ChartIndex → ChartIndex
nextChart (chart j) = chart (suc j)

record CompiledChartStep : Set where
  constructor compiledChartStep
  field
    currentChart : ChartIndex
    successorChart : ChartIndex
    successorChecks : successorChart ≡ nextChart currentChart
    cachedInverseStillGlues : Bool
    overflowRequiresRechart : Bool
    interpretation : String

mkOverflowStep : ChartIndex → CompiledChartStep
mkOverflowStep j = compiledChartStep j (nextChart j) refl false false
  "j+1 is the typed successor chart available when the compiled inverse at j stops gluing; this receipt does not assert that overflow has occurred"

data JRole : Set where
  chartIndexRole : JRole
  modularInvariantRole : JRole
  representationLabelRole : JRole

record JRoleBoundary : Set where
  constructor jRoleBoundary
  field
    chartJ : JRole
    modularJ : JRole
    representationJ : JRole
    chartAndModularIdentifiedWithoutBridge : Bool
    chartAndModularIdentifiedWithoutBridgeIsFalse : chartAndModularIdentifiedWithoutBridge ≡ false
    chartAndRepresentationIdentifiedWithoutBridge : Bool
    chartAndRepresentationIdentifiedWithoutBridgeIsFalse : chartAndRepresentationIdentifiedWithoutBridge ≡ false
    interpretation : String

canonicalJRoleBoundary : JRoleBoundary
canonicalJRoleBoundary =
  jRoleBoundary chartIndexRole modularInvariantRole representationLabelRole
    false refl false refl
    "j as compiled chart, j as modular invariant, and j as representation/spin label are separate typed roles; j+1 in the chart lane is successor/rechart semantics"

record IdentitySuccessorSplit : Set where
  constructor identitySuccessorSplit
  field
    identityMeaning : String
    successorMeaning : String
    meaningsCollapsed : Bool
    meaningsCollapsedIsFalse : meaningsCollapsed ≡ false

canonicalIdentitySuccessorSplit : IdentitySuccessorSplit
canonicalIdentitySuccessorSplit =
  identitySuccessorSplit
    "1 as neutral/identity carrier or one-dimensional summand"
    "+1 as successor, overflow witness, or transition to a new chart"
    false refl
