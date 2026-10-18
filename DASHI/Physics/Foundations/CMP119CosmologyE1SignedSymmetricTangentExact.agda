{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyE1SignedSymmetricTangentExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K

data Axis4 : Set where
  axis0 axis1 axis2 axis3 : Axis4

data BasisSign : Set where
  plus minus : BasisSign

multiplySign : BasisSign → BasisSign → BasisSign
multiplySign plus sign = sign
multiplySign minus plus = minus
multiplySign minus minus = plus

record SignedSymmetricComponent : Set where
  constructor signed-component
  field
    sign : BasisSign
    component : K.SymmetricTensorComponent4

open SignedSymmetricComponent public

componentOfPair : Axis4 → Axis4 → K.SymmetricTensorComponent4
componentOfPair axis0 axis0 = K.component00
componentOfPair axis0 axis1 = K.component01
componentOfPair axis0 axis2 = K.component02
componentOfPair axis0 axis3 = K.component03
componentOfPair axis1 axis0 = K.component01
componentOfPair axis1 axis1 = K.component11
componentOfPair axis1 axis2 = K.component12
componentOfPair axis1 axis3 = K.component13
componentOfPair axis2 axis0 = K.component02
componentOfPair axis2 axis1 = K.component12
componentOfPair axis2 axis2 = K.component22
componentOfPair axis2 axis3 = K.component23
componentOfPair axis3 axis0 = K.component03
componentOfPair axis3 axis1 = K.component13
componentOfPair axis3 axis2 = K.component23
componentOfPair axis3 axis3 = K.component33

componentAxes : K.SymmetricTensorComponent4 → Axis4 × Axis4
componentAxes K.component00 = axis0 , axis0
componentAxes K.component01 = axis0 , axis1
componentAxes K.component02 = axis0 , axis2
componentAxes K.component03 = axis0 , axis3
componentAxes K.component11 = axis1 , axis1
componentAxes K.component12 = axis1 , axis2
componentAxes K.component13 = axis1 , axis3
componentAxes K.component22 = axis2 , axis2
componentAxes K.component23 = axis2 , axis3
componentAxes K.component33 = axis3 , axis3

record SignedAxisAction : Set₁ where
  field
    axisImage : Axis4 → Axis4
    axisSign : Axis4 → BasisSign

open SignedAxisAction public

actSignedComponent :
  SignedAxisAction →
  K.SymmetricTensorComponent4 →
  SignedSymmetricComponent
actSignedComponent action component with componentAxes component
... | left , right =
  signed-component
    (multiplySign (axisSign action left) (axisSign action right))
    (componentOfPair (axisImage action left) (axisImage action right))

forgetSign : SignedSymmetricComponent → K.SymmetricTensorComponent4
forgetSign = component

identityAxisAction : SignedAxisAction
identityAxisAction = record
  { SignedAxisAction.axisImage = λ axis → axis
  ; SignedAxisAction.axisSign = λ _ → plus
  }

timeReflection : SignedAxisAction
timeReflection = record
  { SignedAxisAction.axisImage = λ axis → axis
  ; SignedAxisAction.axisSign = timeSign
  }
  where
    timeSign : Axis4 → BasisSign
    timeSign axis0 = minus
    timeSign axis1 = plus
    timeSign axis2 = plus
    timeSign axis3 = plus

timeReflectionKeeps00Positive :
  actSignedComponent timeReflection K.component00
  ≡ signed-component plus K.component00
timeReflectionKeeps00Positive = refl

timeReflectionFlips01 :
  actSignedComponent timeReflection K.component01
  ≡ signed-component minus K.component01
timeReflectionFlips01 = refl

timeReflectionFlips02 :
  actSignedComponent timeReflection K.component02
  ≡ signed-component minus K.component02
timeReflectionFlips02 = refl

timeReflectionFlips03 :
  actSignedComponent timeReflection K.component03
  ≡ signed-component minus K.component03
timeReflectionFlips03 = refl

timeReflectionLeavesSpatial12Positive :
  actSignedComponent timeReflection K.component12
  ≡ signed-component plus K.component12
timeReflectionLeavesSpatial12Positive = refl

bareTenSlotCarrierForgetsReflectionSign :
  forgetSign (actSignedComponent timeReflection K.component01)
  ≡ K.component01
bareTenSlotCarrierForgetsReflectionSign = refl

fullReflectionActionNeedsSignedLift : Bool
fullReflectionActionNeedsSignedLift = true

plainTenSlotPermutationAloneClosesFullE1 : Bool
plainTenSlotPermutationAloneClosesFullE1 = false
