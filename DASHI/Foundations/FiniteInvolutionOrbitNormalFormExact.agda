module DASHI.Foundations.FiniteInvolutionOrbitNormalFormExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Graduate Texts in Mathematics 42,
-- Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- Give a finite normal-form carrier for an involution with a prescribed number
-- of singleton fixed orbits and two-cycles:
--
--   fixed + 2 * paired.
--
-- The fixed summand is pointwise fixed; the paired summand carries a Bit fibre
-- whose flip is fixed-point-free and involutive.  This is a generic finite
-- orbit grammar only; identifying a domain-specific involution with this normal
-- form requires a separate equivalence/realization witness.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin)
open import Data.Sum using (_⊎_; inj₁; inj₂)


data Bit2 : Set where
  bit0 bit1 : Bit2

flipBit : Bit2 → Bit2
flipBit bit0 = bit1
flipBit bit1 = bit0

flipBitInvolutive : (bit : Bit2) → flipBit (flipBit bit) ≡ bit
flipBitInvolutive bit0 = refl
flipBitInvolutive bit1 = refl

flipBitNoFixedPoint : (bit : Bit2) → flipBit bit ≡ bit → ⊥
flipBitNoFixedPoint bit0 ()
flipBitNoFixedPoint bit1 ()

OrbitNormalFormCarrier : Nat → Nat → Set
OrbitNormalFormCarrier fixed paired =
  Fin fixed ⊎ (Fin paired × Bit2)

orbitInvolution :
  ∀ {fixed paired} →
  OrbitNormalFormCarrier fixed paired →
  OrbitNormalFormCarrier fixed paired
orbitInvolution (inj₁ fixedIndex) = inj₁ fixedIndex
orbitInvolution (inj₂ (pairIndex , bit)) =
  inj₂ (pairIndex , flipBit bit)

orbitInvolutionInvolutive :
  ∀ {fixed paired}
    (x : OrbitNormalFormCarrier fixed paired) →
  orbitInvolution (orbitInvolution x) ≡ x
orbitInvolutionInvolutive (inj₁ fixedIndex) = refl
orbitInvolutionInvolutive (inj₂ (pairIndex , bit0)) = refl
orbitInvolutionInvolutive (inj₂ (pairIndex , bit1)) = refl

fixedSummandReallyFixed :
  ∀ {fixed paired}
    (index : Fin fixed) →
  orbitInvolution {fixed} {paired} (inj₁ index) ≡ inj₁ index
fixedSummandReallyFixed index = refl

pairedSummandHasNoFixedPoint :
  ∀ {fixed paired}
    (index : Fin paired)
    (bit : Bit2) →
  orbitInvolution {fixed} {paired} (inj₂ (index , bit))
  ≡ inj₂ (index , bit) →
  ⊥
pairedSummandHasNoFixedPoint index bit0 ()
pairedSummandHasNoFixedPoint index bit1 ()

orbitCarrierCardinality : Nat → Nat → Nat
orbitCarrierCardinality fixed paired = fixed + 2 * paired

record InvolutionOrbitSpectrum : Set where
  constructor involution-orbit-spectrum
  field
    fixedOrbitCount : Nat
    pairedOrbitCount : Nat
    totalCarrierCount : Nat
    carrierCountExact :
      totalCarrierCount
      ≡ orbitCarrierCardinality fixedOrbitCount pairedOrbitCount

open InvolutionOrbitSpectrum public

fullyFixed : InvolutionOrbitSpectrum → Bool
fullyFixed spectrum with pairedOrbitCount spectrum
... | zero = true
... | suc _ = false

record InvolutionNormalFormRealization
    (Carrier : Set)
    (involution : Carrier → Carrier)
    (spectrum : InvolutionOrbitSpectrum) : Set₁ where
  field
    toNormal :
      Carrier →
      OrbitNormalFormCarrier
        (fixedOrbitCount spectrum)
        (pairedOrbitCount spectrum)

    fromNormal :
      OrbitNormalFormCarrier
        (fixedOrbitCount spectrum)
        (pairedOrbitCount spectrum) →
      Carrier

    fromAfterTo : (x : Carrier) → fromNormal (toNormal x) ≡ x
    toAfterFrom :
      (x : OrbitNormalFormCarrier
        (fixedOrbitCount spectrum)
        (pairedOrbitCount spectrum)) →
      toNormal (fromNormal x) ≡ x

    intertwinesInvolution :
      (x : Carrier) →
      toNormal (involution x) ≡ orbitInvolution (toNormal x)

open InvolutionNormalFormRealization public

record FiniteInvolutionNormalFormBoundary : Set where
  field
    singletonAndTwoCycleNormalFormConstructed : Bool
    singletonAndTwoCycleNormalFormConstructedIsTrue :
      singletonAndTwoCycleNormalFormConstructed ≡ true

    pairedFibreFixedPointFree : Bool
    pairedFibreFixedPointFreeIsTrue : pairedFibreFixedPointFree ≡ true

    domainSpecificRealizationAutomaticFromCounts : Bool
    domainSpecificRealizationAutomaticFromCountsIsFalse :
      domainSpecificRealizationAutomaticFromCounts ≡ false

canonicalFiniteInvolutionNormalFormBoundary :
  FiniteInvolutionNormalFormBoundary
canonicalFiniteInvolutionNormalFormBoundary =
  record
    { singletonAndTwoCycleNormalFormConstructed = true
    ; singletonAndTwoCycleNormalFormConstructedIsTrue = refl
    ; pairedFibreFixedPointFree = true
    ; pairedFibreFixedPointFreeIsTrue = refl
    ; domainSpecificRealizationAutomaticFromCounts = false
    ; domainSpecificRealizationAutomaticFromCountsIsFalse = refl
    }
