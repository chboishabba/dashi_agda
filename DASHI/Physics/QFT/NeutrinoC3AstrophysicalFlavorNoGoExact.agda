module DASHI.Physics.QFT.NeutrinoC3AstrophysicalFlavorNoGoExact where

------------------------------------------------------------------------
-- ASTROPHYSICAL FLAVOUR SOURCE IDENTIFIABILITY
--
-- ORIGINAL OBSERVATIONAL SOURCE
-- IceCube Collaboration, R. Abbasi et al.,
-- "Characterization of the Three-Flavor Composition of Cosmic Neutrinos
-- with IceCube", Physical Review Letters 137 (2026) 081002.
-- DOI: 10.1103/vntd-m133; 18 August 2026.
-- 11.4 years of data; best-fit Earth fractions ~(.30,.37,.33).
--
-- ORIGINAL MATH / PHENOMENOLOGY SOURCES
-- Standard phase-averaged vacuum neutrino oscillations:
-- Pbar(a,b) = sum_i |U_ai|² |U_bi|².
-- Three-point DFT orthogonality: Terras (1999), Serre (1977);
-- C3 flavour model prior art: Altarelli/Feruglio (2005, 2006, 2010).
--
-- EXISTING DASHI OWNERS
-- C3CyclotomicAmplitudeAlgebraExact, C3CubeCyclotomicFourierExact,
-- NeutrinoC3CyclotomicPriorArtBridgeExact, NeutrinoThreeFlavourFiniteExact.
--
-- New mathematical contribution: exact finite Pbar computation and a
-- sharp source-mixture-identifiability no-go for naive U=F3/sqrt(3).
-- All fractions are represented as integer numerators with a separate
-- common denominator.  No estimated parameters, physical PMNS matrix,
-- IceCube likelihood or source inference is constructed.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _+_) renaming (_+_ to _+ℕ_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; _+_; _*_)
open import Data.Empty using (⊥)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.RelationalTernaryPhaseGeometry as E
import DASHI.Physics.QFT.NeutrinoThreeFlavourFiniteExact as Three
import DASHI.Physics.QFT.NeutrinoC3CyclotomicPriorArtBridgeExact as C3

------------------------------------------------------------------------
-- Flat 3x3 DFT: each raw complex matrix element has norm 1, and the
-- physical U = F/sqrt(3) implies Born probability 1/3 per entry.
-- Its phase-averaged propagation has numerator 3, denominator 9:
--                      Pbar_F = J/3.
------------------------------------------------------------------------

fourierBornNumerator :
  Three.Flavour → Three.MassBasis → ℤ
fourierBornNumerator a i = E.normE (C3.fourierEntry a i)

fourierDecoheredNumerator :
  Three.Flavour → Three.Flavour → ℤ
fourierDecoheredNumerator a b =
  fourierBornNumerator a Three.mass1 *
  fourierBornNumerator b Three.mass1 +
  (fourierBornNumerator a Three.mass2 *
   fourierBornNumerator b Three.mass2 +
   fourierBornNumerator a Three.mass3 *
   fourierBornNumerator b Three.mass3)

fourierEveryAveragedEntryIsThree :
  (a b : Three.Flavour) →
  fourierDecoheredNumerator a b ≡ + 3
fourierEveryAveragedEntryIsThree Three.electron Three.electron = refl
fourierEveryAveragedEntryIsThree Three.electron Three.muon = refl
fourierEveryAveragedEntryIsThree Three.electron Three.tau = refl
fourierEveryAveragedEntryIsThree Three.muon Three.electron = refl
fourierEveryAveragedEntryIsThree Three.muon Three.muon = refl
fourierEveryAveragedEntryIsThree Three.muon Three.tau = refl
fourierEveryAveragedEntryIsThree Three.tau Three.electron = refl
fourierEveryAveragedEntryIsThree Three.tau Three.muon = refl
fourierEveryAveragedEntryIsThree Three.tau Three.tau = refl

------------------------------------------------------------------------
-- Existing M/3 rational orthogonal mixer: Born numerators are
-- [1,4,4]/9 and permutations.  The *averaged* transition numerator
-- has diagonal 33 and off-diagonal 24, denominator 81.
-- That retains only 1/9 of the source-mixture contrast:
--                 Pbar_M = (8 J + 3 I)/27.
------------------------------------------------------------------------

toyBornNumerator :
  Three.Flavour → Three.MassBasis → ℤ
toyBornNumerator a i = Three.weight a i * Three.weight a i

toyDecoheredNumerator :
  Three.Flavour → Three.Flavour → ℤ
toyDecoheredNumerator a b =
  toyBornNumerator a Three.mass1 * toyBornNumerator b Three.mass1 +
  (toyBornNumerator a Three.mass2 * toyBornNumerator b Three.mass2 +
   toyBornNumerator a Three.mass3 * toyBornNumerator b Three.mass3)

toyDecoElectronElectron :
  toyDecoheredNumerator Three.electron Three.electron ≡ + 33
toyDecoElectronElectron = refl

toyDecoElectronMuon :
  toyDecoheredNumerator Three.electron Three.muon ≡ + 24
toyDecoElectronMuon = refl

toyDecoElectronTau :
  toyDecoheredNumerator Three.electron Three.tau ≡ + 24
toyDecoElectronTau = refl

toyDecoMuonMuon :
  toyDecoheredNumerator Three.muon Three.muon ≡ + 33
toyDecoMuonMuon = refl

toyDecoMuonTau :
  toyDecoheredNumerator Three.muon Three.tau ≡ + 24
toyDecoMuonTau = refl

toyDecoTauTau :
  toyDecoheredNumerator Three.tau Three.tau ≡ + 33
toyDecoTauTau = refl

------------------------------------------------------------------------
-- Pion-decay source (1:2:0) and pure neutron-decay source (1:0:0).
-- Their source ratios differ; under flat Fourier, the arrival ratios
-- are the SAME, proving failure of source-mixture identifiability.
------------------------------------------------------------------------

record SourceCounts : Set where
  constructor sourceCounts
  field
    electronCount muonCount tauCount : Nat

open SourceCounts public

sourceCount : SourceCounts → Three.Flavour → ℤ
sourceCount s Three.electron = + (electronCount s)
sourceCount s Three.muon = + (muonCount s)
sourceCount s Three.tau = + (tauCount s)

totalCount : SourceCounts → Nat
totalCount s = (electronCount s +ℕ muonCount s) +ℕ tauCount s

pionSource : SourceCounts
pionSource = sourceCounts 1 2 0

neutronSource : SourceCounts
neutronSource = sourceCounts 1 0 0

fourierEarthNumerator : SourceCounts → Three.Flavour → ℤ
fourierEarthNumerator s b =
  sourceCount s Three.electron *
  fourierDecoheredNumerator Three.electron b +
  (sourceCount s Three.muon *
   fourierDecoheredNumerator Three.muon b +
   sourceCount s Three.tau *
   fourierDecoheredNumerator Three.tau b)

toyEarthNumerator : SourceCounts → Three.Flavour → ℤ
toyEarthNumerator s b =
  sourceCount s Three.electron *
  toyDecoheredNumerator Three.electron b +
  (sourceCount s Three.muon *
   toyDecoheredNumerator Three.muon b +
   sourceCount s Three.tau *
   toyDecoheredNumerator Three.tau b)

-- Observed physical proportions are numerator/(9*totalCount) for F3
-- and numerator/(81*totalCount) for the M/3 toy.
fourierPionEarthElectron :
  fourierEarthNumerator pionSource Three.electron ≡ + 9
fourierPionEarthElectron = refl

fourierPionEarthMuon :
  fourierEarthNumerator pionSource Three.muon ≡ + 9
fourierPionEarthMuon = refl

fourierPionEarthTau :
  fourierEarthNumerator pionSource Three.tau ≡ + 9
fourierPionEarthTau = refl

fourierNeutronEarthElectron :
  fourierEarthNumerator neutronSource Three.electron ≡ + 3
fourierNeutronEarthElectron = refl

fourierNeutronEarthMuon :
  fourierEarthNumerator neutronSource Three.muon ≡ + 3
fourierNeutronEarthMuon = refl

fourierNeutronEarthTau :
  fourierEarthNumerator neutronSource Three.tau ≡ + 3
fourierNeutronEarthTau = refl

-- For both source mixtures the normalized Earth fractions equal 1/3;
-- 9/27 = 3/9 (all target channels).
fourierSourceContrastWasErased :
  (b : Three.Flavour) →
  fourierEarthNumerator pionSource b ≡
    (+ 3) * fourierEarthNumerator neutronSource b
fourierSourceContrastWasErased Three.electron = refl
fourierSourceContrastWasErased Three.muon = refl
fourierSourceContrastWasErased Three.tau = refl

-- For the rational toy M/3, numerator/(81*totalCount):
-- pion -> (81,90,72)/243 = (9,10,8)/27
-- neutron -> (33,24,24)/81 = (11,8,8)/27

toyPionEarthElectron :
  toyEarthNumerator pionSource Three.electron ≡ + 81
toyPionEarthElectron = refl

toyPionEarthMuon :
  toyEarthNumerator pionSource Three.muon ≡ + 90
toyPionEarthMuon = refl

toyPionEarthTau :
  toyEarthNumerator pionSource Three.tau ≡ + 72
toyPionEarthTau = refl

toyNeutronEarthElectron :
  toyEarthNumerator neutronSource Three.electron ≡ + 33
toyNeutronEarthElectron = refl

toyNeutronEarthMuon :
  toyEarthNumerator neutronSource Three.muon ≡ + 24
toyNeutronEarthMuon = refl

toyNeutronEarthTau :
  toyEarthNumerator neutronSource Three.tau ≡ + 24
toyNeutronEarthTau = refl

-- Source-contrast comparison is exact but the toy is already ruled
-- out as a literal PMNS matrix by its reactor |U_e3|² = 4/9.

data IceCubeSourceInferencePromotion : Set where

noIceCubeSourceInferenceFromFiniteAlgebra :
  IceCubeSourceInferencePromotion → ⊥
noIceCubeSourceInferenceFromFiniteAlgebra ()

originalIceCubePublication : String
originalIceCubePublication =
  "IceCube Collaboration, Abbasi et al., Physical Review Letters 137, 081002 (2026), DOI 10.1103/vntd-m133"

empiricalInferenceBoundary : String
empiricalInferenceBoundary =
  "Source-conditioned track/cascade/double-cascade likelihood with astrophysical spectrum, backgrounds, response matrices and nuisance profiling is still missing."
