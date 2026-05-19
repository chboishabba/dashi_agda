module Ontology.Hecke.PressureAdapter where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (s≤s; z≤n)

open import DASHI.Pressure using
  ( Pressure
  ; low
  ; medium
  ; high
  ; _⊑p_
  )
open import Ontology.Hecke.DefectOrbitCollapsePressure using
  ( PressureClass
  ; lowPressure
  ; mediumPressure
  ; highPressure
  )
open import Ontology.Hecke.DefectOrbitPressureOrder using
  ( PressureDescentLaw
  ; pressureDescentLaw
  ; _≤P_
  ; low≤low
  ; low≤medium
  ; low≤high
  ; medium≤medium
  ; medium≤high
  ; high≤high
  )

embedPressureClass : PressureClass → Pressure
embedPressureClass lowPressure = low
embedPressureClass mediumPressure = medium
embedPressureClass highPressure = high

embedPressureClass-low : embedPressureClass lowPressure ≡ low
embedPressureClass-low = refl

embedPressureClass-medium : embedPressureClass mediumPressure ≡ medium
embedPressureClass-medium = refl

embedPressureClass-high : embedPressureClass highPressure ≡ high
embedPressureClass-high = refl

embedPressureClass-monotone :
  ∀ {a b} →
  a ≤P b →
  embedPressureClass a ⊑p embedPressureClass b
embedPressureClass-monotone low≤low = s≤s z≤n
embedPressureClass-monotone low≤medium = s≤s z≤n
embedPressureClass-monotone low≤high = s≤s z≤n
embedPressureClass-monotone medium≤medium = s≤s (s≤s z≤n)
embedPressureClass-monotone medium≤high = s≤s (s≤s z≤n)
embedPressureClass-monotone high≤high = s≤s (s≤s (s≤s z≤n))

record PressureDescentLawSurface : Set₁ where
  field
    coarseLaw : PressureDescentLaw
    liftedMonotone :
      ∀ {a b} →
      a ≤P b →
      embedPressureClass a ⊑p embedPressureClass b

pressureDescentLawSurface : PressureDescentLawSurface
pressureDescentLawSurface =
  record
    { coarseLaw = pressureDescentLaw
    ; liftedMonotone = embedPressureClass-monotone
    }
