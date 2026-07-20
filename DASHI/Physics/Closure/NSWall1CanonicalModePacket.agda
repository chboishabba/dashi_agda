module DASHI.Physics.Closure.NSWall1CanonicalModePacket where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)

open import DASHI.Physics.Closure.NSIntegerFourierLattice
open import DASHI.Physics.Closure.NSFourierBiotSavartTriadKernel hiding (NonZeroMode)

------------------------------------------------------------------------
-- A minimal exact Wall-1 Fourier packet.
--
-- The packet is deliberately finite and algebraic.  It fixes concrete Z^3
-- modes and resonance identities, but keeps nonzero and shell-membership
-- witnesses explicit so no numerical classification is promoted silently.
------------------------------------------------------------------------

p100 : FourierMode
p100 = mode (+ 1) (+ 0) (+ 0)

p010 : FourierMode
p010 = mode (+ 0) (+ 1) (+ 0)

p001 : FourierMode
p001 = mode (+ 0) (+ 0) (+ 1)

p110 : FourierMode
p110 = mode (+ 1) (+ 1) (+ 0)

p101 : FourierMode
p101 = mode (+ 1) (+ 0) (+ 1)

p011 : FourierMode
p011 = mode (+ 0) (+ 1) (+ 1)

canonicalLowModes : List FourierMode
canonicalLowModes = p100 ∷ p010 ∷ p001 ∷ []

canonicalHighModes : List FourierMode
canonicalHighModes = p110 ∷ p101 ∷ p011 ∷ []

record CanonicalModeWitnesses : Set₁ where
  field
    p100NonZero : NonZeroMode p100
    p010NonZero : NonZeroMode p010
    p001NonZero : NonZeroMode p001

open CanonicalModeWitnesses public

triad100010110 :
  CanonicalModeWitnesses →
  ResonantFourierTriad FourierMode addMode NonZeroMode
triad100010110 W = record
  { pMode = p100
  ; qMode = p010
  ; targetMode = p110
  ; resonance = refl
  ; pNonZero = p100NonZero W
  ; qNonZero = p010NonZero W
  }

triad100001101 :
  CanonicalModeWitnesses →
  ResonantFourierTriad FourierMode addMode NonZeroMode
triad100001101 W = record
  { pMode = p100
  ; qMode = p001
  ; targetMode = p101
  ; resonance = refl
  ; pNonZero = p100NonZero W
  ; qNonZero = p001NonZero W
  }

triad010001011 :
  CanonicalModeWitnesses →
  ResonantFourierTriad FourierMode addMode NonZeroMode
triad010001011 W = record
  { pMode = p010
  ; qMode = p001
  ; targetMode = p011
  ; resonance = refl
  ; pNonZero = p010NonZero W
  ; qNonZero = p001NonZero W
  }

canonicalTriads :
  CanonicalModeWitnesses →
  List (ResonantFourierTriad FourierMode addMode NonZeroMode)
canonicalTriads W =
  triad100010110 W
  ∷ triad100001101 W
  ∷ triad010001011 W
  ∷ []

canonicalResonance100010 : addMode p100 p010 ≡ p110
canonicalResonance100010 = refl

canonicalResonance100001 : addMode p100 p001 ≡ p101
canonicalResonance100001 = refl

canonicalResonance010001 : addMode p010 p001 ≡ p011
canonicalResonance010001 = refl
