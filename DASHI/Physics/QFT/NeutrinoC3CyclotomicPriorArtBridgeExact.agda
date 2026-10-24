module DASHI.Physics.QFT.NeutrinoC3CyclotomicPriorArtBridgeExact where

------------------------------------------------------------------------
-- REUSE-FIRST OWNERS, NOT A NEW PHASE ALGEBRA
--
-- Cyclotomic values, exact ternary sum zero, nonnegative norms:
--   DASHI.Reasoning.RelationalTernaryPhaseGeometry (Eisenstein Z[zeta])
-- Symbolic depth-one phases and Monster transport:
--   DASHI.Algebra.TriadicDepthOneCharacters
--   DASHI.Moonshine.C3FourierConjugationExact
-- Existing three-flavour rational mixer (separate toy):
--   DASHI.Physics.QFT.NeutrinoThreeFlavourFiniteExact
--
-- External original prior art:
--   Altarelli & Feruglio 2005/2006 A4 lepton flavour models
--   Grimus, arXiv:1301.0495 (2013), vanishing root-of-unity sums
--   NuFIT 6.1 (2025), IC24+SK parameter ranges
--
-- New contribution: an exact FINITE three-flavour Eisenstein
-- interference computation on the *existing* phase carrier.
-- Physical PMNS, flavour-sector residual-symmetry breaking and mass
-- spectra are NOT built from the coincidence of three phases and
-- three flavour labels.  A vanishing sum is an additive amplitude,
-- not a zero-norm unitary eigenphase.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤ᵇ_)
open import Data.Integer using (ℤ; +_; _+_; _*_)
open import Data.Empty using (⊥)

import DASHI.Reasoning.RelationalTernaryPhaseGeometry as E
import DASHI.Algebra.TriadicDepthOneCharacters as C3
import DASHI.Moonshine.C3FourierConjugationExact as Fourier
import DASHI.Physics.QFT.NeutrinoThreeFlavourFiniteExact as Three

------------------------------------------------------------------------
-- Same values as existing Z[zeta] owner, not a new complex embedding.
------------------------------------------------------------------------

phaseWave : C3.C3Phase → E.EisensteinWave
phaseWave C3.phase0 = E.rootOne
phaseWave C3.phase1 = E.rootOmega
phaseWave C3.phase2 = E.rootOmegaSquared

zetaIsExistingRoot :
  phaseWave Fourier.zeta ≡ E.rootOmega
zetaIsExistingRoot = refl

zetaSquaredIsExistingRoot :
  phaseWave Fourier.zetaSquared ≡ E.rootOmegaSquared
zetaSquaredIsExistingRoot = refl

threeCyclicPhaseSumZero :
  E.addE
    (phaseWave Fourier.one)
    (E.addE (phaseWave Fourier.zeta)
            (phaseWave Fourier.zetaSquared))
    ≡ E.zeroE
threeCyclicPhaseSumZero = refl

unitPhaseNorm :
  (p : C3.C3Phase) → E.normE (phaseWave p) ≡ + 1
unitPhaseNorm C3.phase0 = refl
unitPhaseNorm C3.phase1 = refl
unitPhaseNorm C3.phase2 = refl

cancelledAmplitudeNormZero : E.normE E.zeroE ≡ + 0
cancelledAmplitudeNormZero = refl

-- In particular: the identity sum gives zero amplitude, NOT a fourth
-- phase.  The C3 phase type has exactly three cases and each has norm 1.

------------------------------------------------------------------------
-- Fixed original three-flavour mixer donor M/3, combined with the
-- actual C3 cyclotomic phases.  The raw squared amplitudes are
-- divided by 81 because M M^T = 9 I.
------------------------------------------------------------------------

scaleWave : ℤ → E.EisensteinWave → E.EisensteinWave
scaleWave n (E.eisensteinWave a b) =
  E.eisensteinWave (n * a) (n * b)

weightPair : Three.Flavour → Three.Flavour → Three.MassBasis → ℤ
weightPair a b i = Three.weight a i * Three.weight b i

c3AmplitudeNumerator :
  Three.Flavour → Three.Flavour →
  C3.C3Phase → C3.C3Phase → C3.C3Phase →
  E.EisensteinWave
c3AmplitudeNumerator a b p q r =
  E.addE
    (scaleWave (weightPair a b Three.mass1) (phaseWave p))
    (E.addE
      (scaleWave (weightPair a b Three.mass2) (phaseWave q))
      (scaleWave (weightPair a b Three.mass3) (phaseWave r)))

c3ProbabilityNumerator :
  Three.Flavour → Three.Flavour →
  C3.C3Phase → C3.C3Phase → C3.C3Phase → ℤ
c3ProbabilityNumerator a b p q r =
  E.normE (c3AmplitudeNumerator a b p q r)

c3TotalProbabilityNumerator :
  Three.Flavour →
  C3.C3Phase → C3.C3Phase → C3.C3Phase → ℤ
c3TotalProbabilityNumerator a p q r =
  c3ProbabilityNumerator a Three.electron p q r +
  (c3ProbabilityNumerator a Three.muon p q r +
   c3ProbabilityNumerator a Three.tau p q r)

-- 3^3 phase triples x three distinct source flavours = 81
-- exhaustive definitional checks; no new axioms, fit parameters,
-- postulates or assumed normalization authority.
c3AllThreeFlavourConservation :
  (a : Three.Flavour)
  (p q r : C3.C3Phase) →
  c3TotalProbabilityNumerator a p q r ≡ + 81
c3AllThreeFlavourConservation Three.electron C3.phase0 C3.phase0 C3.phase0 = refl
c3AllThreeFlavourConservation Three.electron C3.phase0 C3.phase0 C3.phase1 = refl
c3AllThreeFlavourConservation Three.electron C3.phase0 C3.phase0 C3.phase2 = refl
c3AllThreeFlavourConservation Three.electron C3.phase0 C3.phase1 C3.phase0 = refl
c3AllThreeFlavourConservation Three.electron C3.phase0 C3.phase1 C3.phase1 = refl
c3AllThreeFlavourConservation Three.electron C3.phase0 C3.phase1 C3.phase2 = refl
c3AllThreeFlavourConservation Three.electron C3.phase0 C3.phase2 C3.phase0 = refl
c3AllThreeFlavourConservation Three.electron C3.phase0 C3.phase2 C3.phase1 = refl
c3AllThreeFlavourConservation Three.electron C3.phase0 C3.phase2 C3.phase2 = refl
c3AllThreeFlavourConservation Three.electron C3.phase1 C3.phase0 C3.phase0 = refl
c3AllThreeFlavourConservation Three.electron C3.phase1 C3.phase0 C3.phase1 = refl
c3AllThreeFlavourConservation Three.electron C3.phase1 C3.phase0 C3.phase2 = refl
c3AllThreeFlavourConservation Three.electron C3.phase1 C3.phase1 C3.phase0 = refl
c3AllThreeFlavourConservation Three.electron C3.phase1 C3.phase1 C3.phase1 = refl
c3AllThreeFlavourConservation Three.electron C3.phase1 C3.phase1 C3.phase2 = refl
c3AllThreeFlavourConservation Three.electron C3.phase1 C3.phase2 C3.phase0 = refl
c3AllThreeFlavourConservation Three.electron C3.phase1 C3.phase2 C3.phase1 = refl
c3AllThreeFlavourConservation Three.electron C3.phase1 C3.phase2 C3.phase2 = refl
c3AllThreeFlavourConservation Three.electron C3.phase2 C3.phase0 C3.phase0 = refl
c3AllThreeFlavourConservation Three.electron C3.phase2 C3.phase0 C3.phase1 = refl
c3AllThreeFlavourConservation Three.electron C3.phase2 C3.phase0 C3.phase2 = refl
c3AllThreeFlavourConservation Three.electron C3.phase2 C3.phase1 C3.phase0 = refl
c3AllThreeFlavourConservation Three.electron C3.phase2 C3.phase1 C3.phase1 = refl
c3AllThreeFlavourConservation Three.electron C3.phase2 C3.phase1 C3.phase2 = refl
c3AllThreeFlavourConservation Three.electron C3.phase2 C3.phase2 C3.phase0 = refl
c3AllThreeFlavourConservation Three.electron C3.phase2 C3.phase2 C3.phase1 = refl
c3AllThreeFlavourConservation Three.electron C3.phase2 C3.phase2 C3.phase2 = refl
c3AllThreeFlavourConservation Three.muon C3.phase0 C3.phase0 C3.phase0 = refl
c3AllThreeFlavourConservation Three.muon C3.phase0 C3.phase0 C3.phase1 = refl
c3AllThreeFlavourConservation Three.muon C3.phase0 C3.phase0 C3.phase2 = refl
c3AllThreeFlavourConservation Three.muon C3.phase0 C3.phase1 C3.phase0 = refl
c3AllThreeFlavourConservation Three.muon C3.phase0 C3.phase1 C3.phase1 = refl
c3AllThreeFlavourConservation Three.muon C3.phase0 C3.phase1 C3.phase2 = refl
c3AllThreeFlavourConservation Three.muon C3.phase0 C3.phase2 C3.phase0 = refl
c3AllThreeFlavourConservation Three.muon C3.phase0 C3.phase2 C3.phase1 = refl
c3AllThreeFlavourConservation Three.muon C3.phase0 C3.phase2 C3.phase2 = refl
c3AllThreeFlavourConservation Three.muon C3.phase1 C3.phase0 C3.phase0 = refl
c3AllThreeFlavourConservation Three.muon C3.phase1 C3.phase0 C3.phase1 = refl
c3AllThreeFlavourConservation Three.muon C3.phase1 C3.phase0 C3.phase2 = refl
c3AllThreeFlavourConservation Three.muon C3.phase1 C3.phase1 C3.phase0 = refl
c3AllThreeFlavourConservation Three.muon C3.phase1 C3.phase1 C3.phase1 = refl
c3AllThreeFlavourConservation Three.muon C3.phase1 C3.phase1 C3.phase2 = refl
c3AllThreeFlavourConservation Three.muon C3.phase1 C3.phase2 C3.phase0 = refl
c3AllThreeFlavourConservation Three.muon C3.phase1 C3.phase2 C3.phase1 = refl
c3AllThreeFlavourConservation Three.muon C3.phase1 C3.phase2 C3.phase2 = refl
c3AllThreeFlavourConservation Three.muon C3.phase2 C3.phase0 C3.phase0 = refl
c3AllThreeFlavourConservation Three.muon C3.phase2 C3.phase0 C3.phase1 = refl
c3AllThreeFlavourConservation Three.muon C3.phase2 C3.phase0 C3.phase2 = refl
c3AllThreeFlavourConservation Three.muon C3.phase2 C3.phase1 C3.phase0 = refl
c3AllThreeFlavourConservation Three.muon C3.phase2 C3.phase1 C3.phase1 = refl
c3AllThreeFlavourConservation Three.muon C3.phase2 C3.phase1 C3.phase2 = refl
c3AllThreeFlavourConservation Three.muon C3.phase2 C3.phase2 C3.phase0 = refl
c3AllThreeFlavourConservation Three.muon C3.phase2 C3.phase2 C3.phase1 = refl
c3AllThreeFlavourConservation Three.muon C3.phase2 C3.phase2 C3.phase2 = refl
c3AllThreeFlavourConservation Three.tau C3.phase0 C3.phase0 C3.phase0 = refl
c3AllThreeFlavourConservation Three.tau C3.phase0 C3.phase0 C3.phase1 = refl
c3AllThreeFlavourConservation Three.tau C3.phase0 C3.phase0 C3.phase2 = refl
c3AllThreeFlavourConservation Three.tau C3.phase0 C3.phase1 C3.phase0 = refl
c3AllThreeFlavourConservation Three.tau C3.phase0 C3.phase1 C3.phase1 = refl
c3AllThreeFlavourConservation Three.tau C3.phase0 C3.phase1 C3.phase2 = refl
c3AllThreeFlavourConservation Three.tau C3.phase0 C3.phase2 C3.phase0 = refl
c3AllThreeFlavourConservation Three.tau C3.phase0 C3.phase2 C3.phase1 = refl
c3AllThreeFlavourConservation Three.tau C3.phase0 C3.phase2 C3.phase2 = refl
c3AllThreeFlavourConservation Three.tau C3.phase1 C3.phase0 C3.phase0 = refl
c3AllThreeFlavourConservation Three.tau C3.phase1 C3.phase0 C3.phase1 = refl
c3AllThreeFlavourConservation Three.tau C3.phase1 C3.phase0 C3.phase2 = refl
c3AllThreeFlavourConservation Three.tau C3.phase1 C3.phase1 C3.phase0 = refl
c3AllThreeFlavourConservation Three.tau C3.phase1 C3.phase1 C3.phase1 = refl
c3AllThreeFlavourConservation Three.tau C3.phase1 C3.phase1 C3.phase2 = refl
c3AllThreeFlavourConservation Three.tau C3.phase1 C3.phase2 C3.phase0 = refl
c3AllThreeFlavourConservation Three.tau C3.phase1 C3.phase2 C3.phase1 = refl
c3AllThreeFlavourConservation Three.tau C3.phase1 C3.phase2 C3.phase2 = refl
c3AllThreeFlavourConservation Three.tau C3.phase2 C3.phase0 C3.phase0 = refl
c3AllThreeFlavourConservation Three.tau C3.phase2 C3.phase0 C3.phase1 = refl
c3AllThreeFlavourConservation Three.tau C3.phase2 C3.phase0 C3.phase2 = refl
c3AllThreeFlavourConservation Three.tau C3.phase2 C3.phase1 C3.phase0 = refl
c3AllThreeFlavourConservation Three.tau C3.phase2 C3.phase1 C3.phase1 = refl
c3AllThreeFlavourConservation Three.tau C3.phase2 C3.phase1 C3.phase2 = refl
c3AllThreeFlavourConservation Three.tau C3.phase2 C3.phase2 C3.phase0 = refl
c3AllThreeFlavourConservation Three.tau C3.phase2 C3.phase2 C3.phase1 = refl
c3AllThreeFlavourConservation Three.tau C3.phase2 C3.phase2 C3.phase2 = refl

------------------------------------------------------------------------
-- Nontrivial coherent interference with the GENUINE C3 character triple:
-- 1 + zeta + zeta^2 = 0.
-- P(e->e)=9/81=1/9, P(e->mu)=P(e->tau)=36/81=4/9.
-- Under exchange zeta <-> zeta^2 probabilities are unchanged
-- for this real (CP-even) toy mixer.
------------------------------------------------------------------------

c3ElectronSurvival :
  c3ProbabilityNumerator Three.electron Three.electron
    C3.phase0 C3.phase1 C3.phase2 ≡ + 9
c3ElectronSurvival = refl

c3ElectronToMuon :
  c3ProbabilityNumerator Three.electron Three.muon
    C3.phase0 C3.phase1 C3.phase2 ≡ + 36
c3ElectronToMuon = refl

c3ElectronToTau :
  c3ProbabilityNumerator Three.electron Three.tau
    C3.phase0 C3.phase1 C3.phase2 ≡ + 36
c3ElectronToTau = refl

c3ConjugateElectronToMuon :
  c3ProbabilityNumerator Three.electron Three.muon
    C3.phase0 C3.phase2 C3.phase1 ≡ + 36
c3ConjugateElectronToMuon = refl

c3ConjugateElectronToTau :
  c3ProbabilityNumerator Three.electron Three.tau
    C3.phase0 C3.phase2 C3.phase1 ≡ + 36
c3ConjugateElectronToTau = refl

c3InterferenceSum :
  c3TotalProbabilityNumerator Three.electron
    C3.phase0 C3.phase1 C3.phase2 ≡ + 81
c3InterferenceSum = refl

------------------------------------------------------------------------
-- Canonical Fourier C3 raw matrix: F_ab in {1,zeta,zeta^2}.
-- F^dagger F = 3 I already belongs to existing exact C3 Fourier
-- owners. Normalised U = F / sqrt(3) gives all |U_ab|^2 = 1/3.
-- Thus an unbroken identification U_PMNS := F_3 is in serious
-- conflict with the reactor measurement sin^2(theta13)≈0.0225.
-- C3 characters alone do NOT specify the charged-lepton and neutrino
-- diagonalising bases, their misalignment, or symmetry breaking.
------------------------------------------------------------------------

fourierEntry : Three.Flavour → Three.MassBasis → E.EisensteinWave
fourierEntry Three.electron Three.mass1 = E.rootOne
fourierEntry Three.electron Three.mass2 = E.rootOne
fourierEntry Three.electron Three.mass3 = E.rootOne
fourierEntry Three.muon Three.mass1 = E.rootOne
fourierEntry Three.muon Three.mass2 = E.rootOmega
fourierEntry Three.muon Three.mass3 = E.rootOmegaSquared
fourierEntry Three.tau Three.mass1 = E.rootOne
fourierEntry Three.tau Three.mass2 = E.rootOmegaSquared
fourierEntry Three.tau Three.mass3 = E.rootOmega

fourierAllEntryNormsOne :
  (a : Three.Flavour) (i : Three.MassBasis) →
  E.normE (fourierEntry a i) ≡ + 1
fourierAllEntryNormsOne Three.electron Three.mass1 = refl
fourierAllEntryNormsOne Three.electron Three.mass2 = refl
fourierAllEntryNormsOne Three.electron Three.mass3 = refl
fourierAllEntryNormsOne Three.muon Three.mass1 = refl
fourierAllEntryNormsOne Three.muon Three.mass2 = refl
fourierAllEntryNormsOne Three.muon Three.mass3 = refl
fourierAllEntryNormsOne Three.tau Three.mass1 = refl
fourierAllEntryNormsOne Three.tau Three.mass2 = refl
fourierAllEntryNormsOne Three.tau Three.mass3 = refl

fourierReactorEntryNumerator :
  E.normE (fourierEntry Three.electron Three.mass3) ≡ + 1
fourierReactorEntryNumerator = refl

rationalToyReactorWeight :
  Three.weight Three.electron Three.mass3 ≡ + 2
rationalToyReactorWeight = refl

-- Empirical screen s13² < 3/100 (~0.03) from NuFIT 6.1:
-- Fourier: 1/3 > 3/100, as 100 > 9.
-- Rational toy: 4/9 > 3/100, as 400 > 27.
-- These exact arithmetic facts are NOT fitted confidence intervals.
fourierFailsLooseReactorScreen :
  (100 ≤ᵇ 9) ≡ false
fourierFailsLooseReactorScreen = refl

rationalToyFailsLooseReactorScreen :
  (400 ≤ᵇ 27) ≡ false
rationalToyFailsLooseReactorScreen = refl

-- Correct *phase* reuse does not suffice to select the physical
-- mixing matrix. Model discrimination requires sector-specific mass
-- matrices, residual symmetry, breaking, diagonalization and fit.

data PhysicalPMNSIdentification : Set where

physicalPMNSIdentificationNotConstructed :
  PhysicalPMNSIdentification → ⊥
physicalPMNSIdentificationNotConstructed ()
