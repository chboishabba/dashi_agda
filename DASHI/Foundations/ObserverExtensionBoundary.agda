module DASHI.Foundations.ObserverExtensionBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (_+_; _*_)
open import Agda.Builtin.String using (String)

import DASHI.Foundations.JChartSuccessorBoundary as Charts
import DASHI.Promotion.MetacognitiveFrameBearingState as Meta

data NineState : Set where
  n0 n1 n2 n3 n4 n5 n6 n7 n8 : NineState

data ExceptionalObserver (X : Set) : Set where
  ordinaryPoint : X → ExceptionalObserver X
  starPoint : ExceptionalObserver X

record ReflexiveObserver (X : Set) : Set where
  constructor reflexiveObserver
  field
    baseState : X
    stance : Meta.ReflexiveStance

open ReflexiveObserver public

exceptionalObserverCount : 9 + 1 ≡ 10
exceptionalObserverCount = refl

reflexiveObserverCount : 9 * 2 ≡ 18
reflexiveObserverCount = refl

starChart : Charts.ChartIndex
starChart = Charts.chart 10

starSuccessorChart : Charts.ChartIndex
starSuccessorChart = Charts.nextChart starChart

starSuccessorIsEleven : starSuccessorChart ≡ Charts.chart 11
starSuccessorIsEleven = refl

canonicalImmersedNine : ReflexiveObserver NineState
canonicalImmersedNine = reflexiveObserver n3 Meta.immersedInFrame

canonicalObservingNine : ReflexiveObserver NineState
canonicalObservingNine = reflexiveObserver n3 Meta.observingFrame

observerStanceCanChangeWithoutChangingBase :
  baseState canonicalImmersedNine ≡ baseState canonicalObservingNine
observerStanceCanChangeWithoutChangingBase = refl

record ObserverExtensionBoundary : Set where
  constructor observerExtensionBoundary
  field
    exceptionalConstructionLabel reflexiveConstructionLabel : String
    exceptionalArithmeticCountChecked reflexiveArithmeticCountChecked : Bool
    observerIsAlwaysExceptionalPoint : Bool
    observerIsAlwaysExceptionalPointIsFalse : observerIsAlwaysExceptionalPoint ≡ false
    observerCoordinateEqualsCoproductMarker : Bool
    observerCoordinateEqualsCoproductMarkerIsFalse : observerCoordinateEqualsCoproductMarker ≡ false
    chartTenAndObserverAreArithmeticIdentity : Bool
    chartTenAndObserverAreArithmeticIdentityIsFalse : chartTenAndObserverAreArithmeticIdentity ≡ false
    interpretation : String

canonicalObserverExtensionBoundary : ObserverExtensionBoundary
canonicalObserverExtensionBoundary =
  observerExtensionBoundary
    "X plus one exceptional star/overflow marker"
    "X times a binary immersed/frame-aware stance fibre"
    true true
    false refl
    false refl
    false refl
    "9+1=10 models an exceptional observer marker, while 9*2=18 models reflexive stance over every nine-state point"
