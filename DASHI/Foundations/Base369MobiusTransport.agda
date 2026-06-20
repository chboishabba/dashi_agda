module DASHI.Foundations.Base369MobiusTransport where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (_+_)

open import Base369 using
  ( HexTruth
  ; TriTruth
  ; fromHexIndex
  ; fromTriIndex
  ; hex-index
  ; hex-0
  ; hex-1
  ; hex-2
  ; hex-3
  ; hex-4
  ; hex-5
  ; tri-low
  ; tri-mid
  ; tri-high
  )

------------------------------------------------------------------------
-- Mod-6 Möbius transport on HexTruth.

mobiusTransport : HexTruth → HexTruth
mobiusTransport x = fromHexIndex (hex-index x + 3)

data OrientationPolarity : Set where
  positive : OrientationPolarity
  negative : OrientationPolarity

flipOrientationPolarity : OrientationPolarity → OrientationPolarity
flipOrientationPolarity positive = negative
flipOrientationPolarity negative = positive

hexOrientationPolarity : HexTruth → OrientationPolarity
hexOrientationPolarity hex-0 = positive
hexOrientationPolarity hex-1 = positive
hexOrientationPolarity hex-2 = positive
hexOrientationPolarity hex-3 = negative
hexOrientationPolarity hex-4 = negative
hexOrientationPolarity hex-5 = negative

hexTriadicPhase : HexTruth → TriTruth
hexTriadicPhase x = fromTriIndex (hex-index x)

mobiusTransport-flipsOrientationPolarity :
  (x : HexTruth) →
  hexOrientationPolarity (mobiusTransport x) ≡
  flipOrientationPolarity (hexOrientationPolarity x)
mobiusTransport-flipsOrientationPolarity hex-0 = refl
mobiusTransport-flipsOrientationPolarity hex-1 = refl
mobiusTransport-flipsOrientationPolarity hex-2 = refl
mobiusTransport-flipsOrientationPolarity hex-3 = refl
mobiusTransport-flipsOrientationPolarity hex-4 = refl
mobiusTransport-flipsOrientationPolarity hex-5 = refl

mobiusTransport-preservesTriadicPhase :
  (x : HexTruth) →
  hexTriadicPhase (mobiusTransport x) ≡ hexTriadicPhase x
mobiusTransport-preservesTriadicPhase hex-0 = refl
mobiusTransport-preservesTriadicPhase hex-1 = refl
mobiusTransport-preservesTriadicPhase hex-2 = refl
mobiusTransport-preservesTriadicPhase hex-3 = refl
mobiusTransport-preservesTriadicPhase hex-4 = refl
mobiusTransport-preservesTriadicPhase hex-5 = refl

mobiusTransport-squares-to-identity :
  (x : HexTruth) →
  mobiusTransport (mobiusTransport x) ≡ x
mobiusTransport-squares-to-identity hex-0 = refl
mobiusTransport-squares-to-identity hex-1 = refl
mobiusTransport-squares-to-identity hex-2 = refl
mobiusTransport-squares-to-identity hex-3 = refl
mobiusTransport-squares-to-identity hex-4 = refl
mobiusTransport-squares-to-identity hex-5 = refl

------------------------------------------------------------------------
-- Compact receipt surface for downstream callers.

record MobiusTransportReceipt : Set where
  field
    transport :
      HexTruth → HexTruth

    flipsOrientationPolarity :
      (x : HexTruth) →
      hexOrientationPolarity (transport x) ≡
      flipOrientationPolarity (hexOrientationPolarity x)

    preservesTriadicPhase :
      (x : HexTruth) →
      hexTriadicPhase (transport x) ≡ hexTriadicPhase x

    squaresToIdentity :
      (x : HexTruth) →
      transport (transport x) ≡ x

mobiusTransportReceipt : MobiusTransportReceipt
mobiusTransportReceipt =
  record
    { transport = mobiusTransport
    ; flipsOrientationPolarity = mobiusTransport-flipsOrientationPolarity
    ; preservesTriadicPhase = mobiusTransport-preservesTriadicPhase
    ; squaresToIdentity = mobiusTransport-squares-to-identity
    }
