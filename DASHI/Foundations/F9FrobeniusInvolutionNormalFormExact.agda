module DASHI.Foundations.F9FrobeniusInvolutionNormalFormExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Rudolf Lidl and Harald Niederreiter,
-- "Finite Fields", 2nd ed., Cambridge University Press, 1997.
-- DOI: 10.1017/CBO9780511525926.
--
-- DASHI CONTRIBUTION
--
-- Turn the F9 Frobenius calculation into an explicit instance of the existing
-- generic finite-involution orbit normal form.  The three base-field points
-- (a,0) are fixed and, for each a in F3, the two points (a,1),(a,2) form one
-- Frobenius pair.  Thus
--
--   F9  ~=  Fin 3  disjoint-union  (Fin 3 x Bit2)
--
-- with spectrum fixed=3, paired=3, total=9, and the chart literally
-- intertwines x |-> x^3 = conjugation with the normal-form involution.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)

import Base369 as Base
import DASHI.Foundations.TernaryNineRingFieldFibreSeparationExact as Nine
import DASHI.Foundations.FiniteInvolutionOrbitNormalFormExact as Orbit

f3Index : Nine.F3 → Fin 3
f3Index Base.tri-low = zero
f3Index Base.tri-mid = suc zero
f3Index Base.tri-high = suc (suc zero)

indexF3 : Fin 3 → Nine.F3
indexF3 zero = Base.tri-low
indexF3 (suc zero) = Base.tri-mid
indexF3 (suc (suc zero)) = Base.tri-high

f3IndexRoundTrip : (a : Nine.F3) → indexF3 (f3Index a) ≡ a
f3IndexRoundTrip Base.tri-low = refl
f3IndexRoundTrip Base.tri-mid = refl
f3IndexRoundTrip Base.tri-high = refl

indexF3RoundTrip : (i : Fin 3) → f3Index (indexF3 i) ≡ i
indexF3RoundTrip zero = refl
indexF3RoundTrip (suc zero) = refl
indexF3RoundTrip (suc (suc zero)) = refl

f9Spectrum : Orbit.InvolutionOrbitSpectrum
f9Spectrum = Orbit.involution-orbit-spectrum 3 3 9 refl

F9Normal : Set
F9Normal = Orbit.OrbitNormalFormCarrier 3 3

f9ToNormal : Nine.F9 → F9Normal
f9ToNormal (a , Base.tri-low) = inj₁ (f3Index a)
f9ToNormal (a , Base.tri-mid) = inj₂ (f3Index a , Orbit.bit0)
f9ToNormal (a , Base.tri-high) = inj₂ (f3Index a , Orbit.bit1)

f9FromNormal : F9Normal → Nine.F9
f9FromNormal (inj₁ i) = indexF3 i , Base.tri-low
f9FromNormal (inj₂ (i , Orbit.bit0)) = indexF3 i , Base.tri-mid
f9FromNormal (inj₂ (i , Orbit.bit1)) = indexF3 i , Base.tri-high

f9FromAfterTo : (x : Nine.F9) → f9FromNormal (f9ToNormal x) ≡ x
f9FromAfterTo (Base.tri-low , Base.tri-low) = refl
f9FromAfterTo (Base.tri-low , Base.tri-mid) = refl
f9FromAfterTo (Base.tri-low , Base.tri-high) = refl
f9FromAfterTo (Base.tri-mid , Base.tri-low) = refl
f9FromAfterTo (Base.tri-mid , Base.tri-mid) = refl
f9FromAfterTo (Base.tri-mid , Base.tri-high) = refl
f9FromAfterTo (Base.tri-high , Base.tri-low) = refl
f9FromAfterTo (Base.tri-high , Base.tri-mid) = refl
f9FromAfterTo (Base.tri-high , Base.tri-high) = refl

f9ToAfterFrom : (x : F9Normal) → f9ToNormal (f9FromNormal x) ≡ x
f9ToAfterFrom (inj₁ zero) = refl
f9ToAfterFrom (inj₁ (suc zero)) = refl
f9ToAfterFrom (inj₁ (suc (suc zero))) = refl
f9ToAfterFrom (inj₂ (zero , Orbit.bit0)) = refl
f9ToAfterFrom (inj₂ (zero , Orbit.bit1)) = refl
f9ToAfterFrom (inj₂ (suc zero , Orbit.bit0)) = refl
f9ToAfterFrom (inj₂ (suc zero , Orbit.bit1)) = refl
f9ToAfterFrom (inj₂ (suc (suc zero) , Orbit.bit0)) = refl
f9ToAfterFrom (inj₂ (suc (suc zero) , Orbit.bit1)) = refl

f9IntertwinesFrobenius :
  (x : Nine.F9) →
  f9ToNormal (Nine.f9Conjugate x)
  ≡ Orbit.orbitInvolution (f9ToNormal x)
f9IntertwinesFrobenius (Base.tri-low , Base.tri-low) = refl
f9IntertwinesFrobenius (Base.tri-low , Base.tri-mid) = refl
f9IntertwinesFrobenius (Base.tri-low , Base.tri-high) = refl
f9IntertwinesFrobenius (Base.tri-mid , Base.tri-low) = refl
f9IntertwinesFrobenius (Base.tri-mid , Base.tri-mid) = refl
f9IntertwinesFrobenius (Base.tri-mid , Base.tri-high) = refl
f9IntertwinesFrobenius (Base.tri-high , Base.tri-low) = refl
f9IntertwinesFrobenius (Base.tri-high , Base.tri-mid) = refl
f9IntertwinesFrobenius (Base.tri-high , Base.tri-high) = refl

f9FrobeniusNormalFormRealization :
  Orbit.InvolutionNormalFormRealization Nine.F9 Nine.f9Conjugate f9Spectrum
f9FrobeniusNormalFormRealization = record
  { Orbit.toNormal = f9ToNormal
  ; Orbit.fromNormal = f9FromNormal
  ; Orbit.fromAfterTo = f9FromAfterTo
  ; Orbit.toAfterFrom = f9ToAfterFrom
  ; Orbit.intertwinesInvolution = f9IntertwinesFrobenius
  }

f9FixedOrbitCountIsThree : Orbit.fixedOrbitCount f9Spectrum ≡ 3
f9FixedOrbitCountIsThree = refl

f9PairedOrbitCountIsThree : Orbit.pairedOrbitCount f9Spectrum ≡ 3
f9PairedOrbitCountIsThree = refl

f9TotalCountIsNine : Orbit.totalCarrierCount f9Spectrum ≡ 9
f9TotalCountIsNine = refl

record F9FrobeniusNormalFormBoundary : Set where
  field
    explicitThreeFixedThreePairChartConstructed : Bool
    explicitThreeFixedThreePairChartConstructedIsTrue :
      explicitThreeFixedThreePairChartConstructed ≡ true

    frobeniusIntertwiningConstructed : Bool
    frobeniusIntertwiningConstructedIsTrue :
      frobeniusIntertwiningConstructed ≡ true

    f9IdentifiedWithSupersingularFrobeniusCarrier : Bool
    f9IdentifiedWithSupersingularFrobeniusCarrierIsFalse :
      f9IdentifiedWithSupersingularFrobeniusCarrier ≡ false

canonicalF9FrobeniusNormalFormBoundary : F9FrobeniusNormalFormBoundary
canonicalF9FrobeniusNormalFormBoundary = record
  { explicitThreeFixedThreePairChartConstructed = true
  ; explicitThreeFixedThreePairChartConstructedIsTrue = refl
  ; frobeniusIntertwiningConstructed = true
  ; frobeniusIntertwiningConstructedIsTrue = refl
  ; f9IdentifiedWithSupersingularFrobeniusCarrier = false
  ; f9IdentifiedWithSupersingularFrobeniusCarrierIsFalse = refl
  }
