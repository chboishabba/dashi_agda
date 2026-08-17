module DASHI.Physics.Closure.NSTriadKNComAnnularDominantHatLocalizedRowRound66Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- ROUND 66 / B1 CORRECT-INDEX LOCALIZATION
--
-- Round64 welded dominant common hats to the literal LOW-PASS commutator row.
-- Round65 established that the six-three / Schur operator index is the ANNULAR
-- index and constructed the literal annular Gram masses.  This file closes the
-- remaining indexing seam: the exact annular coefficient A_s(tau) and the
-- resonance-derived dominant common hat are now carried by the SAME
-- `PhysicalTriadIncidence`.
--
-- Hence the authoritative B1 input is no longer
--
--   localized low-pass row + separate annular Gram row,
--
-- but one literal dominant-hat-localized ANNULAR row.  Projection to triads and
-- projection to annular coefficients are both definitional/list-inductive
-- equalities on the exact physicalOutputFiber.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; []; _∷_; map)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Triad
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComCanonicalAnnularOutputFibreRound63Exact as Annular
import DASHI.Physics.Closure.NSTriadKNResonantDominantCommonHatRound63Exact as Hat
import DASHI.Physics.Closure.NSTriadKNResonantDominantLowLegSplitRound66Exact as Split

record AnnularDominantHatLocalizedComEntry
    {r}
    (F : C3.RealField r)
    (shell : Nat)
    (E : C3.IntegerEmbedding F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    : Set where
  field
    triad : Triad.PhysicalTriadIncidence
    dominantCommonHat : Hat.ResonantDominantCommonHat triad
    dominantLowSplit : Split.DominantLowLegSplit triad
    coefficient : C3.Complex F
    coefficientMeaning :
      coefficient ≡ Annular.annularTriadCoefficient F shell E velocity triad

open AnnularDominantHatLocalizedComEntry public

localizeAnnularComEntry :
  ∀ {r} (F : C3.RealField r)
    (shell : Nat)
    (E : C3.IntegerEmbedding F)
    (velocity : Z3.FourierMode → C3.Complex3 F) →
  (tau : Triad.PhysicalTriadIncidence) →
  AnnularDominantHatLocalizedComEntry F shell E velocity
localizeAnnularComEntry F shell E velocity tau = record
  { triad = tau
  ; dominantCommonHat = Hat.resonantDominantCommonHat tau
  ; dominantLowSplit = Split.resonantDominantLowLegSplit tau
  ; coefficient = Annular.annularTriadCoefficient F shell E velocity tau
  ; coefficientMeaning = refl
  }

annularDominantHatLocalizedOutputRow :
  ∀ {r} (F : C3.RealField r)
    (shell enumerationCutoff : Nat)
    (E : C3.IntegerEmbedding F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (output : Z3.FourierMode) →
  List (AnnularDominantHatLocalizedComEntry F shell E velocity)
annularDominantHatLocalizedOutputRow F shell N E velocity output =
  map (localizeAnnularComEntry F shell E velocity)
    (Output.physicalOutputFiber N output)

mapLocalizedTriadsExact :
  ∀ {r} (F : C3.RealField r)
    (shell : Nat)
    (E : C3.IntegerEmbedding F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (triads : List Triad.PhysicalTriadIncidence) →
  map triad (map (localizeAnnularComEntry F shell E velocity) triads)
  ≡ triads
mapLocalizedTriadsExact F shell E velocity [] = refl
mapLocalizedTriadsExact F shell E velocity (tau ∷ rest)
  rewrite mapLocalizedTriadsExact F shell E velocity rest = refl

localizedAnnularRowTriadsArePhysicalOutputFiber :
  ∀ {r} (F : C3.RealField r)
    (shell enumerationCutoff : Nat)
    (E : C3.IntegerEmbedding F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (output : Z3.FourierMode) →
  map triad
    (annularDominantHatLocalizedOutputRow
      F shell enumerationCutoff E velocity output)
  ≡ Output.physicalOutputFiber enumerationCutoff output
localizedAnnularRowTriadsArePhysicalOutputFiber
    F shell enumerationCutoff E velocity output =
  mapLocalizedTriadsExact F shell E velocity
    (Output.physicalOutputFiber enumerationCutoff output)

mapLocalizedCoefficientsExact :
  ∀ {r} (F : C3.RealField r)
    (shell : Nat)
    (E : C3.IntegerEmbedding F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (triads : List Triad.PhysicalTriadIncidence) →
  map coefficient (map (localizeAnnularComEntry F shell E velocity) triads)
  ≡ map (Annular.annularTriadCoefficient F shell E velocity) triads
mapLocalizedCoefficientsExact F shell E velocity [] = refl
mapLocalizedCoefficientsExact F shell E velocity (tau ∷ rest)
  rewrite mapLocalizedCoefficientsExact F shell E velocity rest = refl

localizedAnnularRowCoefficientsAreLiteralAnnularOutputFibre :
  ∀ {r} (F : C3.RealField r)
    (shell enumerationCutoff : Nat)
    (E : C3.IntegerEmbedding F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (output : Z3.FourierMode) →
  map coefficient
    (annularDominantHatLocalizedOutputRow
      F shell enumerationCutoff E velocity output)
  ≡ Annular.annularOutputFibreCoefficients
      F shell enumerationCutoff E velocity output
localizedAnnularRowCoefficientsAreLiteralAnnularOutputFibre
    F shell enumerationCutoff E velocity output =
  mapLocalizedCoefficientsExact F shell E velocity
    (Output.physicalOutputFiber enumerationCutoff output)

round66LiteralAnnularComRowCarriesDominantHatAndLowLeg : Bool
round66LiteralAnnularComRowCarriesDominantHatAndLowLeg = true

round66LiteralAnnularComRowCarriesDominantHatAndLowLegIsTrue :
  round66LiteralAnnularComRowCarriesDominantHatAndLowLeg ≡ true
round66LiteralAnnularComRowCarriesDominantHatAndLowLegIsTrue = refl
