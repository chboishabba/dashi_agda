module DASHI.Moonshine.AbelOriginalTriadicTowerTransportExact where

-- Original finite cusp-level tower, same-object 27 -> 9 -> 3.
-- This constructs actual AbelCarrier instances from prior modular actions.
-- It does NOT conflate finite cusp translations with complex exponentiation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Moonshine.AbelCarrierFixedLocusTransportExact as Carrier
import DASHI.Moonshine.JInvariant369ModularLevelCuspObserversExact as Cusp
import DASHI.Moonshine.JInvariant369PhaseLevelSeparationExact as NoFixed
import DASHI.Foundations.TriadicFiniteQuotient as Q

level9Carrier : Carrier.AbelCarrier
level9Carrier = record
  { Carrier.AbelCarrier.Fine = Cusp.level9CuspFibre
  ; Carrier.AbelCarrier.Coordinate = Cusp.level9CuspFibre
  ; Carrier.AbelCarrier.Base = ⊤
  ; Carrier.AbelCarrier.step = Cusp.translateTriadic Q.two
  ; Carrier.AbelCarrier.translate = Cusp.translateTriadic Q.two
  ; Carrier.AbelCarrier.abel = λ x → x
  ; Carrier.AbelCarrier.quotient = λ _ → tt
  ; Carrier.AbelCarrier.abelCommutes = λ _ → refl
  ; Carrier.AbelCarrier.quotientInvariant = λ _ → refl
  }

level27Carrier : Carrier.AbelCarrier
level27Carrier = record
  { Carrier.AbelCarrier.Fine = Cusp.level27CuspFibre
  ; Carrier.AbelCarrier.Coordinate = Cusp.level27CuspFibre
  ; Carrier.AbelCarrier.Base = ⊤
  ; Carrier.AbelCarrier.step = Cusp.translateTriadic Q.three
  ; Carrier.AbelCarrier.translate = Cusp.translateTriadic Q.three
  ; Carrier.AbelCarrier.abel = λ x → x
  ; Carrier.AbelCarrier.quotient = λ _ → tt
  ; Carrier.AbelCarrier.abelCommutes = λ _ → refl
  ; Carrier.AbelCarrier.quotientInvariant = λ _ → refl
  }

level9StepNoFixed :
  (x : Carrier.Fine level9Carrier) →
  Carrier.Fixed (Carrier.step level9Carrier) x →
  NoFixed.Empty
level9StepNoFixed = NoFixed.level9TranslationNoFixedPoint

level27StepNoFixed :
  (x : Carrier.Fine level27Carrier) →
  Carrier.Fixed (Carrier.step level27Carrier) x →
  NoFixed.Empty
level27StepNoFixed = NoFixed.level27TranslationNoFixedPoint

level9QuotientInvariant :
  (x : Carrier.Fine level9Carrier) →
  Carrier.observed level9Carrier (Carrier.step level9Carrier x) ≡
  Carrier.observed level9Carrier x
level9QuotientInvariant =
  Carrier.quotientStepInvariant level9Carrier

level27QuotientInvariant :
  (x : Carrier.Fine level27Carrier) →
  Carrier.observed level27Carrier (Carrier.step level27Carrier x) ≡
  Carrier.observed level27Carrier x
level27QuotientInvariant =
  Carrier.quotientStepInvariant level27Carrier

-- These maps are the existing exact covering projections, not newly
-- fabricated digit encodings or inverse/reconstruction claims.

level27To9StepNaturality :
  (x : Carrier.Fine level27Carrier) →
  Cusp.level27To9CoveringProjection
    (Carrier.step level27Carrier x)
  ≡
  Carrier.step level9Carrier
    (Cusp.level27To9CoveringProjection x)
level27To9StepNaturality =
  Cusp.level27To9TranslationEquivariant

level9To3StepNaturality :
  (x : Carrier.Fine level9Carrier) →
  Cusp.level9To3CoveringProjection
    (Carrier.step level9Carrier x)
  ≡
  Cusp.translateTriadic Q.one
    (Cusp.level9To3CoveringProjection x)
level9To3StepNaturality =
  Cusp.level9To3TranslationEquivariant

level27To3StepNaturality :
  (x : Carrier.Fine level27Carrier) →
  Cusp.level9To3CoveringProjection
    (Cusp.level27To9CoveringProjection
      (Carrier.step level27Carrier x))
  ≡
  Cusp.translateTriadic Q.one
    (Cusp.level9To3CoveringProjection
      (Cusp.level27To9CoveringProjection x))
level27To3StepNaturality x =
  trans
    (cong Cusp.level9To3CoveringProjection
      (level27To9StepNaturality x))
    (level9To3StepNaturality
      (Cusp.level27To9CoveringProjection x))

-- Exact existing roundtrips map finite observer labels to their original
-- modular cusp residues. They are not analytic inverse Abel maps.

level9ObserverRoundTrip :
  (x : Cusp.level9CuspFibre) →
  Cusp.observer9ToLevel9 (Cusp.level9ToObserver9 x) ≡ x
level9ObserverRoundTrip = Cusp.level9ObserverRoundTrip

level27ObserverRoundTrip :
  (x : Cusp.level27CuspFibre) →
  Cusp.observer27ToLevel27 (Cusp.level27ToObserver27 x) ≡ x
level27ObserverRoundTrip = Cusp.level27ObserverRoundTrip

-- A moving fine level is not the constant invariant quotient.
-- The previous level-9/27 no-fixed-point theorems certify that these
-- two roles cannot be silently identified.
