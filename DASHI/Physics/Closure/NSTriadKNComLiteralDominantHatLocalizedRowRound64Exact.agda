module DASHI.Physics.Closure.NSTriadKNComLiteralDominantHatLocalizedRowRound64Exact where

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
-- ROUND 64 / B1 SUPPORT-REALISATION ADVANCE
--
-- Round62 identified the ACTUAL odd-P/Q physical-output-fibre coefficient row
-- with the literal centered low-projector commutator row.  Round63 separately
-- proved that EVERY resonant physical triad has a constructed common dyadic hat
-- carried by its two dominant comparable legs.
--
-- This file performs the missing same-index weld.  Every coefficient of the
-- literal physical Com row is packaged together with the common hat of the
-- EXACT SAME `PhysicalTriadIncidence`; no shell re-enumeration, endpoint-annulus
-- substitution, or existential support premise remains.
--
-- Two projection theorems are exact:
--
--   map triad      localizedRow = physicalOutputFiber
--   map coefficient localizedRow = literalProjectorCommutatorOutputFibreCoefficients
--
-- Thus the B1 normalization/Gram theorem may now start from a literal row whose
-- support localization is already constructed coefficient-by-coefficient.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; []; _∷_; map)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Triad
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComLiteralOddPQOutputFibreCommutatorRound62Exact as Literal
import DASHI.Physics.Closure.NSTriadKNResonantDominantCommonHatRound63Exact as Hat

record DominantHatLocalizedComEntry
    {r}
    (model : LP.PeriodicHardShellFourierPDE {r})
    (projectorCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model))
    : Set where
  field
    triad : Triad.PhysicalTriadIncidence
    commonHat : Hat.ResonantDominantCommonHat triad
    coefficient : C3.Complex (LP.realField model)
    coefficientMeaning :
      coefficient
      ≡ Literal.literalProjectorCommutatorTriadCoefficient
          model projectorCutoff E velocity triad

open DominantHatLocalizedComEntry public

localizeLiteralComEntry :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    (projectorCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model)) →
  Triad.PhysicalTriadIncidence →
  DominantHatLocalizedComEntry model projectorCutoff E velocity
localizeLiteralComEntry model projectorCutoff E velocity tau = record
  { triad = tau
  ; commonHat = Hat.resonantDominantCommonHat tau
  ; coefficient =
      Literal.literalProjectorCommutatorTriadCoefficient
        model projectorCutoff E velocity tau
  ; coefficientMeaning = refl
  }

literalDominantHatLocalizedOutputRow :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    (projectorCutoff enumerationCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model))
    (output : Z3.FourierMode) →
  List (DominantHatLocalizedComEntry model projectorCutoff E velocity)
literalDominantHatLocalizedOutputRow
    model projectorCutoff enumerationCutoff E velocity output =
  map
    (localizeLiteralComEntry model projectorCutoff E velocity)
    (Output.physicalOutputFiber enumerationCutoff output)

mapLocalizedTriadsExact :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    (projectorCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model))
    (triads : List Triad.PhysicalTriadIncidence) →
  map triad
    (map (localizeLiteralComEntry model projectorCutoff E velocity) triads)
  ≡ triads
mapLocalizedTriadsExact model projectorCutoff E velocity [] = refl
mapLocalizedTriadsExact model projectorCutoff E velocity (tau ∷ rest)
  rewrite mapLocalizedTriadsExact model projectorCutoff E velocity rest = refl

localizedOutputRowTriadsArePhysicalOutputFiber :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    (projectorCutoff enumerationCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model))
    (output : Z3.FourierMode) →
  map triad
    (literalDominantHatLocalizedOutputRow
      model projectorCutoff enumerationCutoff E velocity output)
  ≡ Output.physicalOutputFiber enumerationCutoff output
localizedOutputRowTriadsArePhysicalOutputFiber
    model projectorCutoff enumerationCutoff E velocity output =
  mapLocalizedTriadsExact
    model projectorCutoff E velocity
    (Output.physicalOutputFiber enumerationCutoff output)

mapLocalizedCoefficientsExact :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    (projectorCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model))
    (triads : List Triad.PhysicalTriadIncidence) →
  map coefficient
    (map (localizeLiteralComEntry model projectorCutoff E velocity) triads)
  ≡ map
      (Literal.literalProjectorCommutatorTriadCoefficient
        model projectorCutoff E velocity)
      triads
mapLocalizedCoefficientsExact model projectorCutoff E velocity [] = refl
mapLocalizedCoefficientsExact model projectorCutoff E velocity (tau ∷ rest)
  rewrite mapLocalizedCoefficientsExact model projectorCutoff E velocity rest = refl

localizedOutputRowCoefficientsAreLiteralCommutator :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    (projectorCutoff enumerationCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model))
    (output : Z3.FourierMode) →
  map coefficient
    (literalDominantHatLocalizedOutputRow
      model projectorCutoff enumerationCutoff E velocity output)
  ≡ Literal.literalProjectorCommutatorOutputFibreCoefficients
      model projectorCutoff enumerationCutoff E velocity output
localizedOutputRowCoefficientsAreLiteralCommutator
    model projectorCutoff enumerationCutoff E velocity output =
  mapLocalizedCoefficientsExact
    model projectorCutoff E velocity
    (Output.physicalOutputFiber enumerationCutoff output)

round64LiteralComRowCarriesConstructedDominantHatPerCoefficient : Bool
round64LiteralComRowCarriesConstructedDominantHatPerCoefficient = true

round64LiteralComRowCarriesConstructedDominantHatPerCoefficientIsTrue :
  round64LiteralComRowCarriesConstructedDominantHatPerCoefficient ≡ true
round64LiteralComRowCarriesConstructedDominantHatPerCoefficientIsTrue = refl
