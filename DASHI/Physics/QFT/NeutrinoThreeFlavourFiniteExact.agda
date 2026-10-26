module DASHI.Physics.QFT.NeutrinoThreeFlavourFiniteExact where

-- Exact THREE-flavour interference control.
-- This is a rational orthogonal mixer with a discrete C4 mass-phase
-- carrier.  It is NOT the empirical complex PMNS matrix, and contains
-- neither fitted neutrino masses nor an IceCube likelihood.
-- Source mathematical convention: A(beta,alpha) =
--   sum_i U(beta,i) phase(i) U(alpha,i).
-- U = (1/3) [[1,2,2],[2,1,-2],[2,-2,1]].
-- Raw amplitude numerators are therefore divided by 9.
-- Squared-probability numerators sum to 81, not to 1.
-- The 192 exhaustive Agda clauses below check every source flavour
-- and every independently selected triple of four possible mass phases.
-- The C4 quarter rotations are a controlled toy discretization, not a
-- fitted propagation law or proof of C3/369 physical mass generation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; -_; _+_; _*_)
import DASHI.Physics.QFT.NeutrinoIceCubeMaxCutExact as Earlier

data Flavour : Set where
  electron muon tau : Flavour

data MassBasis : Set where
  mass1 mass2 mass3 : MassBasis

open Earlier using (Phase4; phase0; phase90; phase180; phase270)

weight : Flavour → MassBasis → ℤ
weight electron mass1 = + 1
weight electron mass2 = + 2
weight electron mass3 = + 2
weight muon mass1 = + 2
weight muon mass2 = + 1
weight muon mass3 = - (+ 2)
weight tau mass1 = + 2
weight tau mass2 = - (+ 2)
weight tau mass3 = + 1

gram : Flavour → Flavour → ℤ
gram a b =
  (weight a mass1 * weight b mass1) +
  ((weight a mass2 * weight b mass2) +
   (weight a mass3 * weight b mass3))

normRow : (a : Flavour) → gram a a ≡ (+ 9)
normRow electron = refl
normRow muon = refl
normRow tau = refl

-- Explicit six off-diagonal Gram entries (no axioms or assumed metrics).

gramElectronMuon : gram electron muon ≡ (+ 0)
gramElectronMuon = refl
gramElectronTau : gram electron tau ≡ (+ 0)
gramElectronTau = refl
gramMuonTau : gram muon tau ≡ (+ 0)
gramMuonTau = refl

phaseReal : Phase4 → ℤ
phaseReal phase0 = + 1
phaseReal phase90 = + 0
phaseReal phase180 = - (+ 1)
phaseReal phase270 = + 0

phaseImag : Phase4 → ℤ
phaseImag phase0 = + 0
phaseImag phase90 = + 1
phaseImag phase180 = + 0
phaseImag phase270 = - (+ 1)

amplitudeReal : Flavour → Flavour → Phase4 → Phase4 → Phase4 → ℤ
amplitudeReal a b p q r =
  (weight a mass1 * weight b mass1 * phaseReal p) +
  ((weight a mass2 * weight b mass2 * phaseReal q) +
   (weight a mass3 * weight b mass3 * phaseReal r))

amplitudeImag : Flavour → Flavour → Phase4 → Phase4 → Phase4 → ℤ
amplitudeImag a b p q r =
  (weight a mass1 * weight b mass1 * phaseImag p) +
  ((weight a mass2 * weight b mass2 * phaseImag q) +
   (weight a mass3 * weight b mass3 * phaseImag r))

normSquared : ℤ → ℤ → ℤ
normSquared re im = re * re + im * im

appearanceNumerator : Flavour → Flavour → Phase4 → Phase4 → Phase4 → ℤ
appearanceNumerator a b p q r =
  normSquared (amplitudeReal a b p q r) (amplitudeImag a b p q r)

totalNumerator : Flavour → Phase4 → Phase4 → Phase4 → ℤ
totalNumerator a p q r =
  appearanceNumerator a electron p q r +
  (appearanceNumerator a muon p q r +
   appearanceNumerator a tau p q r)

-- This numeric equality is the constructive instance of three-flavour
-- conservation: sum_beta P(alpha->beta) = 81/81 = 1.
-- Proof by normalization of all 3*4^3 closed calculations.
threeFlavourConservation :
  (a : Flavour) (p q r : Phase4) →
  totalNumerator a p q r ≡ (+ 81)
threeFlavourConservation electron phase0 phase0 phase0 = refl
threeFlavourConservation electron phase0 phase0 phase90 = refl
threeFlavourConservation electron phase0 phase0 phase180 = refl
threeFlavourConservation electron phase0 phase0 phase270 = refl
threeFlavourConservation electron phase0 phase90 phase0 = refl
threeFlavourConservation electron phase0 phase90 phase90 = refl
threeFlavourConservation electron phase0 phase90 phase180 = refl
threeFlavourConservation electron phase0 phase90 phase270 = refl
threeFlavourConservation electron phase0 phase180 phase0 = refl
threeFlavourConservation electron phase0 phase180 phase90 = refl
threeFlavourConservation electron phase0 phase180 phase180 = refl
threeFlavourConservation electron phase0 phase180 phase270 = refl
threeFlavourConservation electron phase0 phase270 phase0 = refl
threeFlavourConservation electron phase0 phase270 phase90 = refl
threeFlavourConservation electron phase0 phase270 phase180 = refl
threeFlavourConservation electron phase0 phase270 phase270 = refl
threeFlavourConservation electron phase90 phase0 phase0 = refl
threeFlavourConservation electron phase90 phase0 phase90 = refl
threeFlavourConservation electron phase90 phase0 phase180 = refl
threeFlavourConservation electron phase90 phase0 phase270 = refl
threeFlavourConservation electron phase90 phase90 phase0 = refl
threeFlavourConservation electron phase90 phase90 phase90 = refl
threeFlavourConservation electron phase90 phase90 phase180 = refl
threeFlavourConservation electron phase90 phase90 phase270 = refl
threeFlavourConservation electron phase90 phase180 phase0 = refl
threeFlavourConservation electron phase90 phase180 phase90 = refl
threeFlavourConservation electron phase90 phase180 phase180 = refl
threeFlavourConservation electron phase90 phase180 phase270 = refl
threeFlavourConservation electron phase90 phase270 phase0 = refl
threeFlavourConservation electron phase90 phase270 phase90 = refl
threeFlavourConservation electron phase90 phase270 phase180 = refl
threeFlavourConservation electron phase90 phase270 phase270 = refl
threeFlavourConservation electron phase180 phase0 phase0 = refl
threeFlavourConservation electron phase180 phase0 phase90 = refl
threeFlavourConservation electron phase180 phase0 phase180 = refl
threeFlavourConservation electron phase180 phase0 phase270 = refl
threeFlavourConservation electron phase180 phase90 phase0 = refl
threeFlavourConservation electron phase180 phase90 phase90 = refl
threeFlavourConservation electron phase180 phase90 phase180 = refl
threeFlavourConservation electron phase180 phase90 phase270 = refl
threeFlavourConservation electron phase180 phase180 phase0 = refl
threeFlavourConservation electron phase180 phase180 phase90 = refl
threeFlavourConservation electron phase180 phase180 phase180 = refl
threeFlavourConservation electron phase180 phase180 phase270 = refl
threeFlavourConservation electron phase180 phase270 phase0 = refl
threeFlavourConservation electron phase180 phase270 phase90 = refl
threeFlavourConservation electron phase180 phase270 phase180 = refl
threeFlavourConservation electron phase180 phase270 phase270 = refl
threeFlavourConservation electron phase270 phase0 phase0 = refl
threeFlavourConservation electron phase270 phase0 phase90 = refl
threeFlavourConservation electron phase270 phase0 phase180 = refl
threeFlavourConservation electron phase270 phase0 phase270 = refl
threeFlavourConservation electron phase270 phase90 phase0 = refl
threeFlavourConservation electron phase270 phase90 phase90 = refl
threeFlavourConservation electron phase270 phase90 phase180 = refl
threeFlavourConservation electron phase270 phase90 phase270 = refl
threeFlavourConservation electron phase270 phase180 phase0 = refl
threeFlavourConservation electron phase270 phase180 phase90 = refl
threeFlavourConservation electron phase270 phase180 phase180 = refl
threeFlavourConservation electron phase270 phase180 phase270 = refl
threeFlavourConservation electron phase270 phase270 phase0 = refl
threeFlavourConservation electron phase270 phase270 phase90 = refl
threeFlavourConservation electron phase270 phase270 phase180 = refl
threeFlavourConservation electron phase270 phase270 phase270 = refl
threeFlavourConservation muon phase0 phase0 phase0 = refl
threeFlavourConservation muon phase0 phase0 phase90 = refl
threeFlavourConservation muon phase0 phase0 phase180 = refl
threeFlavourConservation muon phase0 phase0 phase270 = refl
threeFlavourConservation muon phase0 phase90 phase0 = refl
threeFlavourConservation muon phase0 phase90 phase90 = refl
threeFlavourConservation muon phase0 phase90 phase180 = refl
threeFlavourConservation muon phase0 phase90 phase270 = refl
threeFlavourConservation muon phase0 phase180 phase0 = refl
threeFlavourConservation muon phase0 phase180 phase90 = refl
threeFlavourConservation muon phase0 phase180 phase180 = refl
threeFlavourConservation muon phase0 phase180 phase270 = refl
threeFlavourConservation muon phase0 phase270 phase0 = refl
threeFlavourConservation muon phase0 phase270 phase90 = refl
threeFlavourConservation muon phase0 phase270 phase180 = refl
threeFlavourConservation muon phase0 phase270 phase270 = refl
threeFlavourConservation muon phase90 phase0 phase0 = refl
threeFlavourConservation muon phase90 phase0 phase90 = refl
threeFlavourConservation muon phase90 phase0 phase180 = refl
threeFlavourConservation muon phase90 phase0 phase270 = refl
threeFlavourConservation muon phase90 phase90 phase0 = refl
threeFlavourConservation muon phase90 phase90 phase90 = refl
threeFlavourConservation muon phase90 phase90 phase180 = refl
threeFlavourConservation muon phase90 phase90 phase270 = refl
threeFlavourConservation muon phase90 phase180 phase0 = refl
threeFlavourConservation muon phase90 phase180 phase90 = refl
threeFlavourConservation muon phase90 phase180 phase180 = refl
threeFlavourConservation muon phase90 phase180 phase270 = refl
threeFlavourConservation muon phase90 phase270 phase0 = refl
threeFlavourConservation muon phase90 phase270 phase90 = refl
threeFlavourConservation muon phase90 phase270 phase180 = refl
threeFlavourConservation muon phase90 phase270 phase270 = refl
threeFlavourConservation muon phase180 phase0 phase0 = refl
threeFlavourConservation muon phase180 phase0 phase90 = refl
threeFlavourConservation muon phase180 phase0 phase180 = refl
threeFlavourConservation muon phase180 phase0 phase270 = refl
threeFlavourConservation muon phase180 phase90 phase0 = refl
threeFlavourConservation muon phase180 phase90 phase90 = refl
threeFlavourConservation muon phase180 phase90 phase180 = refl
threeFlavourConservation muon phase180 phase90 phase270 = refl
threeFlavourConservation muon phase180 phase180 phase0 = refl
threeFlavourConservation muon phase180 phase180 phase90 = refl
threeFlavourConservation muon phase180 phase180 phase180 = refl
threeFlavourConservation muon phase180 phase180 phase270 = refl
threeFlavourConservation muon phase180 phase270 phase0 = refl
threeFlavourConservation muon phase180 phase270 phase90 = refl
threeFlavourConservation muon phase180 phase270 phase180 = refl
threeFlavourConservation muon phase180 phase270 phase270 = refl
threeFlavourConservation muon phase270 phase0 phase0 = refl
threeFlavourConservation muon phase270 phase0 phase90 = refl
threeFlavourConservation muon phase270 phase0 phase180 = refl
threeFlavourConservation muon phase270 phase0 phase270 = refl
threeFlavourConservation muon phase270 phase90 phase0 = refl
threeFlavourConservation muon phase270 phase90 phase90 = refl
threeFlavourConservation muon phase270 phase90 phase180 = refl
threeFlavourConservation muon phase270 phase90 phase270 = refl
threeFlavourConservation muon phase270 phase180 phase0 = refl
threeFlavourConservation muon phase270 phase180 phase90 = refl
threeFlavourConservation muon phase270 phase180 phase180 = refl
threeFlavourConservation muon phase270 phase180 phase270 = refl
threeFlavourConservation muon phase270 phase270 phase0 = refl
threeFlavourConservation muon phase270 phase270 phase90 = refl
threeFlavourConservation muon phase270 phase270 phase180 = refl
threeFlavourConservation muon phase270 phase270 phase270 = refl
threeFlavourConservation tau phase0 phase0 phase0 = refl
threeFlavourConservation tau phase0 phase0 phase90 = refl
threeFlavourConservation tau phase0 phase0 phase180 = refl
threeFlavourConservation tau phase0 phase0 phase270 = refl
threeFlavourConservation tau phase0 phase90 phase0 = refl
threeFlavourConservation tau phase0 phase90 phase90 = refl
threeFlavourConservation tau phase0 phase90 phase180 = refl
threeFlavourConservation tau phase0 phase90 phase270 = refl
threeFlavourConservation tau phase0 phase180 phase0 = refl
threeFlavourConservation tau phase0 phase180 phase90 = refl
threeFlavourConservation tau phase0 phase180 phase180 = refl
threeFlavourConservation tau phase0 phase180 phase270 = refl
threeFlavourConservation tau phase0 phase270 phase0 = refl
threeFlavourConservation tau phase0 phase270 phase90 = refl
threeFlavourConservation tau phase0 phase270 phase180 = refl
threeFlavourConservation tau phase0 phase270 phase270 = refl
threeFlavourConservation tau phase90 phase0 phase0 = refl
threeFlavourConservation tau phase90 phase0 phase90 = refl
threeFlavourConservation tau phase90 phase0 phase180 = refl
threeFlavourConservation tau phase90 phase0 phase270 = refl
threeFlavourConservation tau phase90 phase90 phase0 = refl
threeFlavourConservation tau phase90 phase90 phase90 = refl
threeFlavourConservation tau phase90 phase90 phase180 = refl
threeFlavourConservation tau phase90 phase90 phase270 = refl
threeFlavourConservation tau phase90 phase180 phase0 = refl
threeFlavourConservation tau phase90 phase180 phase90 = refl
threeFlavourConservation tau phase90 phase180 phase180 = refl
threeFlavourConservation tau phase90 phase180 phase270 = refl
threeFlavourConservation tau phase90 phase270 phase0 = refl
threeFlavourConservation tau phase90 phase270 phase90 = refl
threeFlavourConservation tau phase90 phase270 phase180 = refl
threeFlavourConservation tau phase90 phase270 phase270 = refl
threeFlavourConservation tau phase180 phase0 phase0 = refl
threeFlavourConservation tau phase180 phase0 phase90 = refl
threeFlavourConservation tau phase180 phase0 phase180 = refl
threeFlavourConservation tau phase180 phase0 phase270 = refl
threeFlavourConservation tau phase180 phase90 phase0 = refl
threeFlavourConservation tau phase180 phase90 phase90 = refl
threeFlavourConservation tau phase180 phase90 phase180 = refl
threeFlavourConservation tau phase180 phase90 phase270 = refl
threeFlavourConservation tau phase180 phase180 phase0 = refl
threeFlavourConservation tau phase180 phase180 phase90 = refl
threeFlavourConservation tau phase180 phase180 phase180 = refl
threeFlavourConservation tau phase180 phase180 phase270 = refl
threeFlavourConservation tau phase180 phase270 phase0 = refl
threeFlavourConservation tau phase180 phase270 phase90 = refl
threeFlavourConservation tau phase180 phase270 phase180 = refl
threeFlavourConservation tau phase180 phase270 phase270 = refl
threeFlavourConservation tau phase270 phase0 phase0 = refl
threeFlavourConservation tau phase270 phase0 phase90 = refl
threeFlavourConservation tau phase270 phase0 phase180 = refl
threeFlavourConservation tau phase270 phase0 phase270 = refl
threeFlavourConservation tau phase270 phase90 phase0 = refl
threeFlavourConservation tau phase270 phase90 phase90 = refl
threeFlavourConservation tau phase270 phase90 phase180 = refl
threeFlavourConservation tau phase270 phase90 phase270 = refl
threeFlavourConservation tau phase270 phase180 phase0 = refl
threeFlavourConservation tau phase270 phase180 phase90 = refl
threeFlavourConservation tau phase270 phase180 phase180 = refl
threeFlavourConservation tau phase270 phase180 phase270 = refl
threeFlavourConservation tau phase270 phase270 phase0 = refl
threeFlavourConservation tau phase270 phase270 phase90 = refl
threeFlavourConservation tau phase270 phase270 phase180 = refl
threeFlavourConservation tau phase270 phase270 phase270 = refl

-- Nontrivial cross-flavour interference, in numerator/81 form:
-- a=electron; mass phases (1,i,-i) -> P(e->mu)=40/81,
-- P(e->tau)=40/81, P(e->e)=1/81.
nontrivialAppearanceMuon :
  appearanceNumerator electron muon phase0 phase90 phase270 ≡ (+ 40)
nontrivialAppearanceMuon = refl

nontrivialAppearanceTau :
  appearanceNumerator electron tau phase0 phase90 phase270 ≡ (+ 40)
nontrivialAppearanceTau = refl

nontrivialSurvival :
  appearanceNumerator electron electron phase0 phase90 phase270 ≡ (+ 1)
nontrivialSurvival = refl

zeroDistanceNoFlavourChange :
  appearanceNumerator electron muon phase0 phase0 phase0 ≡ (+ 0)
zeroDistanceNoFlavourChange = refl

allEqualPhasesPreserveElectron :
  appearanceNumerator electron electron phase90 phase90 phase90 ≡ (+ 81)
allEqualPhasesPreserveElectron = refl
