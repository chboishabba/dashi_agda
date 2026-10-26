module DASHI.Physics.QFT.NeutrinoExistingCPAstroConjugationNoGoExact where

------------------------------------------------------------------------
-- EXACT CP-CONJUGATION DEGENERACY OF ASTROPHYSICAL FLAVOUR RATIOS.
--
-- Existing maths: C3CyclotomicAmplitudeAlgebraExact includes
-- normConjugationInvariant, and NeutrinoExistingCPSectorLeptonBridgeExact
-- supplies a nonzero-CP three-flavour complex mixing matrix.
-- Original physics: standard decohered three-neutrino vacuum formula
--   Pbar_ab = Σ_i |U_ai|²|U_bi|²,
-- and Jarlskog 1985 CP rephasing-invariant criteria.
-- Observational root: IceCube Collaboration PRL 137 (2026) 081002,
-- DOI 10.1103/vntd-m133, astrophysical Earth flavour composition.
--
-- New statement: for ANY chosen source ratios, Pbar(U)=Pbar(conj U).
-- Thus in the standard phase-averaged vacuum model the +120deg vs
-- -120deg CP alternatives have identical arrival flavour fractions,
-- despite opposite, nonzero Jarlskog invariants.  IceCube flavour
-- composition alone therefore cannot determine the CP-odd sign;
-- other energy-dependent observables or assumptions are necessary.
-- No detector likelihood, matter transport or event reanalysis claimed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; -_)

import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as Q3
import DASHI.Physics.QFT.NeutrinoThreeFlavourFiniteExact as N
import DASHI.Physics.QFT.NeutrinoExistingCPSectorLeptonBridgeExact as CP

born : N.Flavour → N.MassBasis → ℚ
born a i = Q3.norm (CP.pmns a i)

conjugateBorn : N.Flavour → N.MassBasis → ℚ
conjugateBorn a i =
  Q3.norm (Q3.conjugate (CP.pmns a i))

bornCPConjugationInvariant :
  (a : N.Flavour) (i : N.MassBasis) →
  conjugateBorn a i ≡ born a i
bornCPConjugationInvariant a i =
  Q3.normConjugationInvariant (CP.pmns a i)

phaseAveraged : N.Flavour → N.Flavour → ℚ
phaseAveraged a b =
  (born a N.mass1 * born b N.mass1)
  + ((born a N.mass2 * born b N.mass2)
  +  (born a N.mass3 * born b N.mass3))

phaseAveragedConjugated : N.Flavour → N.Flavour → ℚ
phaseAveragedConjugated a b =
  (conjugateBorn a N.mass1 * conjugateBorn b N.mass1)
  + ((conjugateBorn a N.mass2 * conjugateBorn b N.mass2)
  +  (conjugateBorn a N.mass3 * conjugateBorn b N.mass3))

phaseAverageCannotDetermineCPSign :
  (a b : N.Flavour) →
  phaseAveragedConjugated a b ≡ phaseAveraged a b
phaseAverageCannotDetermineCPSign a b
  rewrite bornCPConjugationInvariant a N.mass1
        | bornCPConjugationInvariant b N.mass1
        | bornCPConjugationInvariant a N.mass2
        | bornCPConjugationInvariant b N.mass2
        | bornCPConjugationInvariant a N.mass3
        | bornCPConjugationInvariant b N.mass3 = refl

record SourceMixture : Set where
  constructor sourceMixture
  field
    electronWeight muonWeight tauWeight : ℚ
open SourceMixture public

earthFlux : SourceMixture → N.Flavour → ℚ
earthFlux s b =
  electronWeight s * phaseAveraged N.electron b
  + (muonWeight s * phaseAveraged N.muon b
  +  tauWeight s * phaseAveraged N.tau b)

earthFluxConjugated : SourceMixture → N.Flavour → ℚ
earthFluxConjugated s b =
  electronWeight s * phaseAveragedConjugated N.electron b
  + (muonWeight s * phaseAveragedConjugated N.muon b
  +  tauWeight s * phaseAveragedConjugated N.tau b)

anySourceMixtureSameUnderCPConjugation :
  (s : SourceMixture) (b : N.Flavour) →
  earthFluxConjugated s b ≡ earthFlux s b
anySourceMixtureSameUnderCPConjugation s b
  rewrite phaseAverageCannotDetermineCPSign N.electron b
        | phaseAverageCannotDetermineCPSign N.muon b
        | phaseAverageCannotDetermineCPSign N.tau b = refl

-- CP-odd phase itself is NOT zero and does change under conjugation;
-- the phase-averaged *intensities* are insensitive to its sign.
quartetOddCoefficientStillNonzero :
  Q3.zetaCoeff CP.quartet ≡ CP.cpOddCoefficient
quartetOddCoefficientStillNonzero = CP.quartetZetaCoefficientExact

quartetOddCoefficientFlipsOnConjugation :
  Q3.zetaCoeff (Q3.conjugate CP.quartet)
    ≡ - CP.cpOddCoefficient
quartetOddCoefficientFlipsOnConjugation =
  CP.quartetCPConjugateZetaCoefficientExact
