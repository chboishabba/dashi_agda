module DASHI.Moonshine.AbelOriginalLevel3CarrierInstanceExact where

-- A concrete *finite* same-point modular level-3 translation example.
-- This is NOT a complex Kneser Abel coordinate or p-adic exponential.
-- Reuse the original DASHI level-3 cusp translation/no-fixed-point theorem.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
import DASHI.Moonshine.AbelCarrierFixedLocusTransportExact as Carrier
import DASHI.Moonshine.JInvariant369PhaseLevelSeparationExact as Level
import DASHI.Moonshine.JInvariant369CanonicalLevelObserverTowerExact as Tower
import DASHI.Moonshine.JInvariant369ModularLevelCuspObserversExact as Cusp

level3Carrier : Carrier.AbelCarrier
level3Carrier = record
  { Carrier.AbelCarrier.Fine = Cusp.level3CuspFibre
  ; Carrier.AbelCarrier.Coordinate = Cusp.level3CuspFibre
  ; Carrier.AbelCarrier.Base = ⊤
  ; Carrier.AbelCarrier.step = Tower.translateLevel3Residue
  ; Carrier.AbelCarrier.translate = Tower.translateLevel3Residue
  ; Carrier.AbelCarrier.abel = λ x → x
  ; Carrier.AbelCarrier.quotient = λ _ → tt
  ; Carrier.AbelCarrier.abelCommutes = λ _ → refl
  ; Carrier.AbelCarrier.quotientInvariant = λ _ → refl
  }

level3CannotBeFixed :
  (x : Carrier.Fine level3Carrier) →
  Carrier.Fixed (Carrier.step level3Carrier) x → Level.Empty
level3CannotBeFixed x fixed =
  Level.level3TranslationNoFixedPoint x fixed

level3CoarseInvariant :
  (x : Carrier.Fine level3Carrier) →
  Carrier.observed level3Carrier (Carrier.step level3Carrier x) ≡
  Carrier.observed level3Carrier x
level3CoarseInvariant =
  Carrier.quotientStepInvariant level3Carrier

level3CoordinateCannotDescend :
  (decode : Carrier.Base level3Carrier →
            Carrier.Coordinate level3Carrier) →
  ((x : Carrier.Fine level3Carrier) →
    Carrier.abel level3Carrier x ≡
    decode (Carrier.observed level3Carrier x)) →
  (x : Carrier.Fine level3Carrier) → Level.Empty
level3CoordinateCannotDescend decode factor x =
  Level.level3TranslationNoFixedPoint x
    (Carrier.coordinateDescentForcesTranslationFixed
       level3Carrier
       (record { Carrier.CoordinateDescent.decode = decode
               ; Carrier.CoordinateDescent.factors = factor })
       x)

-- Negative control: an identity translation DOES have fixed points.
-- Therefore the no-fixed-point theorem requires a real translation law.

identityCarrier : Carrier.AbelCarrier
identityCarrier = record
  { Carrier.AbelCarrier.Fine = ⊤
  ; Carrier.AbelCarrier.Coordinate = ⊤
  ; Carrier.AbelCarrier.Base = ⊤
  ; Carrier.AbelCarrier.step = λ x → x
  ; Carrier.AbelCarrier.translate = λ x → x
  ; Carrier.AbelCarrier.abel = λ x → x
  ; Carrier.AbelCarrier.quotient = λ x → x
  ; Carrier.AbelCarrier.abelCommutes = λ _ → refl
  ; Carrier.AbelCarrier.quotientInvariant = λ _ → refl
  }

identityTranslationHasFixedPoint :
  Carrier.Fixed (Carrier.translate identityCarrier) tt
identityTranslationHasFixedPoint = refl

identityCoordinateDoesDescend :
  Carrier.CoordinateDescent identityCarrier
identityCoordinateDoesDescend = record
  { Carrier.CoordinateDescent.decode = λ x → x
  ; Carrier.CoordinateDescent.factors = λ _ → refl
  }
