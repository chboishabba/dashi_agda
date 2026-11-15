module DASHI.Physics.Measurement.BioEMErrorBudgetExact where

-- Abstract three-stage triangle error transport with explicit monotonicity
-- and associativity assumptions. Empirical estimates remain separate.

open import Agda.Primitive using (Level)

record AdditiveErrorGeometry {ℓ : Level}
  (Signal Error : Set ℓ) : Set ℓ where
  field
    distance : Signal → Signal → Error
    combine : Error → Error → Error
    bounded : Error → Error → Set ℓ
    triangle :
      (x y z : Signal) →
      bounded (distance x z)
        (combine (distance x y) (distance y z))
    rightMonotone :
      (a b c : Error) →
      bounded a b → bounded (combine c a) (combine c b)
    leftMonotone :
      (a b c : Error) →
      bounded a b → bounded (combine a c) (combine b c)
    transitive :
      (a b c : Error) →
      bounded a b → bounded b c → bounded a c
    associateBound :
      (a b c : Error) →
      bounded (combine (combine a b) c)
              (combine a (combine b c))
open AdditiveErrorGeometry public

record ThreeStageErrorReceipt {ℓ : Level}
  {Signal Error : Set ℓ}
  (g : AdditiveErrorGeometry Signal Error)
  (actual physical sensor processed : Signal)
  (ePhysical eSensor eProcess : Error) : Set ℓ where
  field
    physicalBound : bounded g (distance g actual physical) ePhysical
    sensorBound : bounded g (distance g physical sensor) eSensor
    processBound : bounded g (distance g sensor processed) eProcess
open ThreeStageErrorReceipt public

totalErrorBound :
  ∀ {ℓ} {Signal Error : Set ℓ}
    (g : AdditiveErrorGeometry Signal Error)
    (actual physical sensor processed : Signal)
    (ep es er : Error) →
    ThreeStageErrorReceipt g actual physical sensor processed ep es er →
    bounded g (distance g actual processed)
      (combine g ep (combine g es er))
totalErrorBound g actual physical sensor processed ep es er receipt =
  let
    open AdditiveErrorGeometry g
    open ThreeStageErrorReceipt receipt
    dAP = distance actual physical
    dPS = distance physical sensor
    dAS = distance actual sensor
    dSR = distance sensor processed
    first : bounded dAS (combine ep es)
    first =
      transitive dAS (combine dAP dPS) (combine ep es)
        (triangle actual physical sensor)
        (transitive (combine dAP dPS) (combine ep dPS)
          (combine ep es)
          (leftMonotone dAP ep dPS physicalBound)
          (rightMonotone dPS es ep sensorBound))
    second :
      bounded (distance actual processed)
        (combine (combine ep es) er)
    second =
      transitive (distance actual processed) (combine dAS dSR)
        (combine (combine ep es) er)
        (triangle actual sensor processed)
        (transitive (combine dAS dSR) (combine (combine ep es) dSR)
          (combine (combine ep es) er)
          (leftMonotone dAS (combine ep es) dSR first)
          (rightMonotone dSR er (combine ep es) processBound))
  in
  transitive (distance actual processed)
    (combine (combine ep es) er)
    (combine ep (combine es er))
    second
    (associateBound ep es er)
