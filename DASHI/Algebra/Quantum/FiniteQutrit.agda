module DASHI.Algebra.Quantum.FiniteQutrit where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Algebra.Quantum.Dirac

------------------------------------------------------------------------
-- Canonical finite qutrit basis and basis-level Dirac semantics.
--
-- This module deliberately proves only finite basis facts.  General
-- superpositions require a concrete complex scalar implementation and are
-- therefore kept outside this carrier-level bridge.

data QutritBasis : Set where
  ket0 : QutritBasis
  ket1 : QutritBasis
  ket2 : QutritBasis

data DeltaAmplitude : Set where
  amp0 : DeltaAmplitude
  amp1 : DeltaAmplitude

basisPair : Bra QutritBasis → Ket QutritBasis → DeltaAmplitude
basisPair (bra ket0) (ket ket0) = amp1
basisPair (bra ket0) (ket ket1) = amp0
basisPair (bra ket0) (ket ket2) = amp0
basisPair (bra ket1) (ket ket0) = amp0
basisPair (bra ket1) (ket ket1) = amp1
basisPair (bra ket1) (ket ket2) = amp0
basisPair (bra ket2) (ket ket0) = amp0
basisPair (bra ket2) (ket ket1) = amp0
basisPair (bra ket2) (ket ket2) = amp1

finiteQutritDiracPairing : DiracPairing QutritBasis DeltaAmplitude
finiteQutritDiracPairing = record { pair = basisPair }

qket0 : Ket QutritBasis
qket0 = ket ket0

qket1 : Ket QutritBasis
qket1 = ket ket1

qket2 : Ket QutritBasis
qket2 = ket ket2

ket0Normalized :
  braKet finiteQutritDiracPairing (braOf qket0) qket0 ≡ amp1
ket0Normalized = refl

ket1Normalized :
  braKet finiteQutritDiracPairing (braOf qket1) qket1 ≡ amp1
ket1Normalized = refl

ket2Normalized :
  braKet finiteQutritDiracPairing (braOf qket2) qket2 ≡ amp1
ket2Normalized = refl

ket0OrthogonalKet1 :
  braKet finiteQutritDiracPairing (braOf qket0) qket1 ≡ amp0
ket0OrthogonalKet1 = refl

ket0OrthogonalKet2 :
  braKet finiteQutritDiracPairing (braOf qket0) qket2 ≡ amp0
ket0OrthogonalKet2 = refl

ket1OrthogonalKet2 :
  braKet finiteQutritDiracPairing (braOf qket1) qket2 ≡ amp0
ket1OrthogonalKet2 = refl

basisInnerProductKronecker :
  (i j : QutritBasis) →
  basisPair (bra i) (ket j) ≡
  basisPair (bra j) (ket i)
basisInnerProductKronecker ket0 ket0 = refl
basisInnerProductKronecker ket0 ket1 = refl
basisInnerProductKronecker ket0 ket2 = refl
basisInnerProductKronecker ket1 ket0 = refl
basisInnerProductKronecker ket1 ket1 = refl
basisInnerProductKronecker ket1 ket2 = refl
basisInnerProductKronecker ket2 ket0 = refl
basisInnerProductKronecker ket2 ket1 = refl
basisInnerProductKronecker ket2 ket2 = refl
