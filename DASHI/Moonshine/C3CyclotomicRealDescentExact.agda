module DASHI.Moonshine.C3CyclotomicRealDescentExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Lawrence C. Washington,
-- "Introduction to Cyclotomic Fields", Second Edition,
-- Springer Graduate Texts in Mathematics 83, 1997.
-- DOI: 10.1007/978-1-4612-1934-7.
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications",
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- DASHI CONTRIBUTION
--
-- Make the fixed-plus-conjugate-pair decomposition explicit and expose the
-- simplest exact real-valued invariants of the third roots of unity.  For
-- Q(zeta_3)/Q the field trace and norm on the phase basis are
--
--   Tr(1)=2,    Tr(zeta)=Tr(zeta^2)=-1,
--   N(1)=N(zeta)=N(zeta^2)=1.
--
-- Thus conjugation/inversion changes the nontrivial phase label while leaving
-- these real invariants fixed.  This module does not claim that the finite C3
-- carrier alone constructs the real numbers; it isolates the exact descent
-- mechanism that later amplitude/completion layers may use.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

import DASHI.Algebra.TriadicDepthOneCharacters as C3
import DASHI.Moonshine.C3FourierConjugationExact as Fourier

------------------------------------------------------------------------
-- Conjugation orbits: one fixed singleton and one two-element inverse pair.

data C3ConjugationOrbit : Set where
  fixedSingleton : C3ConjugationOrbit
  nontrivialInversePair : C3ConjugationOrbit

conjugationOrbit : C3.C3Phase → C3ConjugationOrbit
conjugationOrbit C3.phase0 = fixedSingleton
conjugationOrbit C3.phase1 = nontrivialInversePair
conjugationOrbit C3.phase2 = nontrivialInversePair

conjugationPreservesOrbit :
  (phase : C3.C3Phase) →
  conjugationOrbit (Fourier.inversePhase phase)
  ≡ conjugationOrbit phase
conjugationPreservesOrbit C3.phase0 = refl
conjugationPreservesOrbit C3.phase1 = refl
conjugationPreservesOrbit C3.phase2 = refl

fixedOrbitSize : Nat
fixedOrbitSize = 1

nontrivialOrbitSize : Nat
nontrivialOrbitSize = 2

fullPhaseSize : Nat
fullPhaseSize = fixedOrbitSize + nontrivialOrbitSize

fullPhaseSizeIsThree : fullPhaseSize ≡ 3
fullPhaseSizeIsThree = refl

------------------------------------------------------------------------
-- A tiny signed-integer literal carrier is sufficient for the exact trace
-- values {-1,2} without importing an analytic real-number implementation.

data SignedNat : Set where
  nonnegative : Nat → SignedNat
  negative : Nat → SignedNat

cyclotomicTrace : C3.C3Phase → SignedNat
cyclotomicTrace C3.phase0 = nonnegative 2
cyclotomicTrace C3.phase1 = negative 1
cyclotomicTrace C3.phase2 = negative 1

cyclotomicNorm : C3.C3Phase → Nat
cyclotomicNorm C3.phase0 = 1
cyclotomicNorm C3.phase1 = 1
cyclotomicNorm C3.phase2 = 1

traceOfOneIsTwo : cyclotomicTrace Fourier.one ≡ nonnegative 2
traceOfOneIsTwo = refl

traceOfZetaIsMinusOne : cyclotomicTrace Fourier.zeta ≡ negative 1
traceOfZetaIsMinusOne = refl

traceOfInverseZetaIsMinusOne :
  cyclotomicTrace (Fourier.inversePhase Fourier.zeta) ≡ negative 1
traceOfInverseZetaIsMinusOne = refl

normOfZetaIsOne : cyclotomicNorm Fourier.zeta ≡ 1
normOfZetaIsOne = refl

normOfInverseZetaIsOne :
  cyclotomicNorm (Fourier.inversePhase Fourier.zeta) ≡ 1
normOfInverseZetaIsOne = refl

traceIsConjugationInvariant :
  (phase : C3.C3Phase) →
  cyclotomicTrace (Fourier.inversePhase phase)
  ≡ cyclotomicTrace phase
traceIsConjugationInvariant C3.phase0 = refl
traceIsConjugationInvariant C3.phase1 = refl
traceIsConjugationInvariant C3.phase2 = refl

normIsConjugationInvariant :
  (phase : C3.C3Phase) →
  cyclotomicNorm (Fourier.inversePhase phase)
  ≡ cyclotomicNorm phase
normIsConjugationInvariant C3.phase0 = refl
normIsConjugationInvariant C3.phase1 = refl
normIsConjugationInvariant C3.phase2 = refl

------------------------------------------------------------------------
-- Realification bookkeeping.  The fixed character contributes one real axis;
-- the conjugate nontrivial character pair contributes a real two-plane.

data RealifiedC3Sector : Set where
  fixedRealAxis : RealifiedC3Sector
  transverseConjugatePlane : RealifiedC3Sector

realifiedSector : C3ConjugationOrbit → RealifiedC3Sector
realifiedSector fixedSingleton = fixedRealAxis
realifiedSector nontrivialInversePair = transverseConjugatePlane

realifiedDimension : RealifiedC3Sector → Nat
realifiedDimension fixedRealAxis = 1
realifiedDimension transverseConjugatePlane = 2

fixedRealDimensionIsOne : realifiedDimension fixedRealAxis ≡ 1
fixedRealDimensionIsOne = refl

transverseRealDimensionIsTwo :
  realifiedDimension transverseConjugatePlane ≡ 2
transverseRealDimensionIsTwo = refl

fullRealifiedDimensionIsThree :
  realifiedDimension fixedRealAxis
  + realifiedDimension transverseConjugatePlane ≡ 3
fullRealifiedDimensionIsThree = refl
