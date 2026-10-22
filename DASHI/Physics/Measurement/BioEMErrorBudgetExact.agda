module DASHI.Physics.Measurement.BioEMErrorBudgetExact where

-- Abstract triangle-inequality error transport. Each real experimental
-- error bound must be supplied by an independently justified receipt.
-- No probability distribution or uncertainty level is inferred by this code.

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_; refl)

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
    (ePhysical eSensor eProcess : Error) →
    ThreeStageErrorReceipt g actual physical sensor processed
      ePhysical eSensor eProcess →
    bounded g (distance g actual processed)
      (combine g ePhysical (combine g eSensor eProcess))
totalErrorBound g actual physical sensor processed ep es er receipt =
  let
    open AdditiveErrorGeometry g
    open ThreeStageErrorReceipt receipt
    first : bounded (distance actual sensor) (combine ep es)
    first = transitive _ _ _
      (triangle actual physical sensor)
      (rightMonotone _ _ _ physicalBound)
  in
  transitive _ _ _
    (triangle actual sensor processed)
    (transitive _ _ _
      (leftMonotone _ _ _ first)
      (leftMonotone _ _ _ processBound))
