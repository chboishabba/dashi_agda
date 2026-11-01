module DASHI.Foundations.Base369MobiusTransportRegression where

open import Agda.Builtin.Equality using (_≡_; refl)

open import Base369 using
  ( hex-0
  ; hex-1
  ; hex-2
  ; hex-3
  ; hex-4
  ; hex-5
  ; tri-low
  ; tri-mid
  ; tri-high
  )

open import DASHI.Foundations.Base369MobiusTransport using
  ( mobiusTransport
  ; hexOrientationPolarity
  ; hexTriadicPhase
  ; OrientationPolarity
  ; positive
  ; negative
  )

------------------------------------------------------------------------
-- Smoke tests that anchor the transport table and its receipts.

mobiusTransport-0 : mobiusTransport hex-0 ≡ hex-3
mobiusTransport-0 = refl

mobiusTransport-1 : mobiusTransport hex-1 ≡ hex-4
mobiusTransport-1 = refl

mobiusTransport-2 : mobiusTransport hex-2 ≡ hex-5
mobiusTransport-2 = refl

mobiusTransport-orientation-0 :
  hexOrientationPolarity (mobiusTransport hex-0) ≡ negative
mobiusTransport-orientation-0 = refl

mobiusTransport-orientation-3 :
  hexOrientationPolarity (mobiusTransport hex-3) ≡ positive
mobiusTransport-orientation-3 = refl

mobiusTransport-phase-0 :
  hexTriadicPhase (mobiusTransport hex-0) ≡ tri-low
mobiusTransport-phase-0 = refl

mobiusTransport-phase-1 :
  hexTriadicPhase (mobiusTransport hex-1) ≡ tri-mid
mobiusTransport-phase-1 = refl

mobiusTransport-phase-2 :
  hexTriadicPhase (mobiusTransport hex-2) ≡ tri-high
mobiusTransport-phase-2 = refl

mobiusTransport-square-0 :
  mobiusTransport (mobiusTransport hex-0) ≡ hex-0
mobiusTransport-square-0 = refl

mobiusTransport-square-4 :
  mobiusTransport (mobiusTransport hex-4) ≡ hex-4
mobiusTransport-square-4 = refl
