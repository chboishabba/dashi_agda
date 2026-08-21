module DASHI.Analysis.RiemannReflectionOrbitDefectExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / 2026 CALIBRATION
--
-- Levent Alpöge and Ralph Furman,
-- "More than two thirds of the zeta zeros are simple and on the critical line",
-- arXiv:2608.13637 (2026).
-- DOI: 10.48550/arXiv.2608.13637.
--
-- The paper proves unconditionally that at least 2/3 of the nontrivial zeta
-- zeros (counted with multiplicity) are simple and on Re(s)=1/2, with a
-- stronger Montgomery--Taylor-window constant about 0.6725.  Its new linear
-- algebra step replaces RH-dependent positivity by a rank/trace inequality on
-- a finite compression of Weil's Hermitian form; Sylvester inertia handles
-- off-critical-line reflection pairs.
--
-- DASHI CONTRIBUTION / CLAIM BOUNDARY
--
-- This module does NOT reconstruct the paper's analytic Weil form.  It closes
-- the exact algebraic quotient that any such analytic producer may target:
--
--   centred displacement  alpha
--   reflection             alpha <-> -alpha
--   orbit quotient         forget orientation, retain magnitude
--   residual defect        magnitude^2
--
-- The concrete carrier below is deliberately discrete (Nat magnitude).  It is
-- a proof-bearing model of the reflection-orbit geometry, not an assertion
-- that actual zero displacements are natural numbers.  An analytic adapter
-- must separately prove that its zero/reflection data descends to this shape.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Exact fixed-centre + inverse-pair carrier.
------------------------------------------------------------------------

data ReflectionSide : Set where
  left right : ReflectionSide

data CentredReflectionState : Set where
  criticalCentre : CentredReflectionState
  offLine : ReflectionSide → Nat → CentredReflectionState

reflect : CentredReflectionState → CentredReflectionState
reflect criticalCentre = criticalCentre
reflect (offLine left n) = offLine right n
reflect (offLine right n) = offLine left n

reflectInvolutive :
  (x : CentredReflectionState) → reflect (reflect x) ≡ x
reflectInvolutive criticalCentre = refl
reflectInvolutive (offLine left n) = refl
reflectInvolutive (offLine right n) = refl

criticalCentreFixed : reflect criticalCentre ≡ criticalCentre
criticalCentreFixed = refl

reflectionFixedImpliesCriticalCentre :
  (x : CentredReflectionState) → reflect x ≡ x → x ≡ criticalCentre
reflectionFixedImpliesCriticalCentre criticalCentre refl = refl
reflectionFixedImpliesCriticalCentre (offLine left n) ()
reflectionFixedImpliesCriticalCentre (offLine right n) ()

------------------------------------------------------------------------
-- Orientation quotient and nonnegative residual defect.
--
-- offLine side n represents positive magnitude suc n.  This prevents a
-- duplicate off-line encoding at zero distance.
------------------------------------------------------------------------

orbitMagnitude : CentredReflectionState → Nat
orbitMagnitude criticalCentre = zero
orbitMagnitude (offLine _ n) = suc n

orbitMagnitudeReflectionInvariant :
  (x : CentredReflectionState) →
  orbitMagnitude (reflect x) ≡ orbitMagnitude x
orbitMagnitudeReflectionInvariant criticalCentre = refl
orbitMagnitudeReflectionInvariant (offLine left n) = refl
orbitMagnitudeReflectionInvariant (offLine right n) = refl

squaredDefect : CentredReflectionState → Nat
squaredDefect x = orbitMagnitude x * orbitMagnitude x

squaredDefectReflectionInvariant :
  (x : CentredReflectionState) →
  squaredDefect (reflect x) ≡ squaredDefect x
squaredDefectReflectionInvariant criticalCentre = refl
squaredDefectReflectionInvariant (offLine left n) = refl
squaredDefectReflectionInvariant (offLine right n) = refl

criticalCentreHasZeroDefect : squaredDefect criticalCentre ≡ zero
criticalCentreHasZeroDefect = refl

zeroDefectImpliesCriticalCentre :
  (x : CentredReflectionState) →
  squaredDefect x ≡ zero →
  x ≡ criticalCentre
zeroDefectImpliesCriticalCentre criticalCentre refl = refl
zeroDefectImpliesCriticalCentre (offLine left n) ()
zeroDefectImpliesCriticalCentre (offLine right n) ()

criticalCentreIffZeroDefectForward :
  (x : CentredReflectionState) →
  x ≡ criticalCentre → squaredDefect x ≡ zero
criticalCentreIffZeroDefectForward .criticalCentre refl = refl

------------------------------------------------------------------------
-- Pairwise symmetric data.
--
-- The signed first moment is deliberately absent from the quotient: reflection
-- makes it cancel.  Magnitude and squaredDefect are the surviving observables.
------------------------------------------------------------------------

record ReflectionOrbitObservable : Set where
  constructor orbitObservable
  field
    magnitude : Nat
    defectSquared : Nat

observeOrbit : CentredReflectionState → ReflectionOrbitObservable
observeOrbit x = orbitObservable (orbitMagnitude x) (squaredDefect x)

observeOrbitReflectionInvariant :
  (x : CentredReflectionState) → observeOrbit (reflect x) ≡ observeOrbit x
observeOrbitReflectionInvariant criticalCentre = refl
observeOrbitReflectionInvariant (offLine left n) = refl
observeOrbitReflectionInvariant (offLine right n) = refl

------------------------------------------------------------------------
-- Exact finite population ledger for reflection-paired zeros.
--
-- pairCount counts two-element off-line reflection orbits.  Therefore each
-- side has exactly pairCount members and the non-fixed population is even.
------------------------------------------------------------------------

record ReflectionPopulation : Set where
  constructor reflectionPopulation
  field
    fixedCount : Nat
    pairCount : Nat

open ReflectionPopulation public

leftCount : ReflectionPopulation → Nat
leftCount p = pairCount p

rightCount : ReflectionPopulation → Nat
rightCount p = pairCount p

nonFixedCount : ReflectionPopulation → Nat
nonFixedCount p = pairCount p + pairCount p

totalCount : ReflectionPopulation → Nat
totalCount p = fixedCount p + nonFixedCount p

leftRightCountsEqual :
  (p : ReflectionPopulation) → leftCount p ≡ rightCount p
leftRightCountsEqual p = refl

nonFixedSplitsIntoEqualSides :
  (p : ReflectionPopulation) →
  nonFixedCount p ≡ leftCount p + rightCount p
nonFixedSplitsIntoEqualSides p = refl

totalSplitsIntoFixedAndInversePair :
  (p : ReflectionPopulation) →
  totalCount p ≡ fixedCount p + (leftCount p + rightCount p)
totalSplitsIntoFixedAndInversePair p = refl

-- Small exact checksum for the sharp 2/3 geometry: four fixed states plus one
-- inverse pair gives six total states, with one state on each off-centre side.
-- This is a finite arithmetic model only; the analytic asymptotic theorem is
-- sourced above and is not derived from this checksum.

twoThirdsChecksumPopulation : ReflectionPopulation
twoThirdsChecksumPopulation = reflectionPopulation 4 1

twoThirdsChecksumTotalIsSix : totalCount twoThirdsChecksumPopulation ≡ 6
twoThirdsChecksumTotalIsSix = refl

twoThirdsChecksumFixedIsFour : fixedCount twoThirdsChecksumPopulation ≡ 4
twoThirdsChecksumFixedIsFour = refl

twoThirdsChecksumLeftIsOne : leftCount twoThirdsChecksumPopulation ≡ 1
twoThirdsChecksumLeftIsOne = refl

twoThirdsChecksumRightIsOne : rightCount twoThirdsChecksumPopulation ≡ 1
twoThirdsChecksumRightIsOne = refl

------------------------------------------------------------------------
-- Authority boundary for the frontier experiment.
------------------------------------------------------------------------

record ReflectionOrbitDefectBoundary : Set where
  field
    reflectionOrbitAlgebraConstructed : Bool
    orientationQuotientConstructed : Bool
    squaredDefectConstructed : Bool
    exactSidePairingConstructed : Bool
    actualZetaZeroCarrierConstructedHere : Bool
    actualWeilHermitianCompressionConstructedHere : Bool
    paperInertiaBlockIdentifiedWithSquaredDefectHere : Bool
    weightedOffLineMomentBoundProvedHere : Bool
    riemannHypothesisProvedHere : Bool

reflectionOrbitDefectBoundary : ReflectionOrbitDefectBoundary
reflectionOrbitDefectBoundary = record
  { reflectionOrbitAlgebraConstructed = true
  ; orientationQuotientConstructed = true
  ; squaredDefectConstructed = true
  ; exactSidePairingConstructed = true
  ; actualZetaZeroCarrierConstructedHere = false
  ; actualWeilHermitianCompressionConstructedHere = false
  ; paperInertiaBlockIdentifiedWithSquaredDefectHere = false
  ; weightedOffLineMomentBoundProvedHere = false
  ; riemannHypothesisProvedHere = false
  }
