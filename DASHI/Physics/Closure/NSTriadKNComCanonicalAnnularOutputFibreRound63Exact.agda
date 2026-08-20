module DASHI.Physics.Closure.NSTriadKNComCanonicalAnnularOutputFibreRound63Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND 63 / B0 OUTPUT-FIBRE LIFT
--
-- Lift the coefficientwise telescoping identity through the exact same
-- `physicalOutputFiber` used by the literal odd-P/Q lane.  For every triad in
-- that list, the difference between successive centered low-pass commutator
-- coefficients is exactly the annular coefficient.  Mapping preserves the
-- list order and cardinality, so no re-enumeration or majorant is inserted.
--
-- This constructs the hatted/annular collision vector that Round62 proved must
-- exist before common-hat support can be discussed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.List.Base using (List; []; _∷_; map)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Triad
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComLiteralOutputFibreKernelRound57Exact as Fibre
import DASHI.Physics.Closure.NSTriadKNComCanonicalAnnularCommutatorRound63Exact as Annular

lowTriadCoefficient :
  ∀ {r} (F : C3.RealField r)
    (cutoff : Nat)
    (E : C3.IntegerEmbedding F)
    (velocity : Z3.FourierMode → C3.Complex3 F) →
  Triad.PhysicalTriadIncidence → C3.Complex F
lowTriadCoefficient F cutoff E velocity tau =
  Annular.canonicalLowCommutatorCoefficient
    F cutoff E velocity (Fibre.triadTransportEntry tau)

annularTriadCoefficient :
  ∀ {r} (F : C3.RealField r)
    (shell : Nat)
    (E : C3.IntegerEmbedding F)
    (velocity : Z3.FourierMode → C3.Complex3 F) →
  Triad.PhysicalTriadIncidence → C3.Complex F
annularTriadCoefficient F shell E velocity tau =
  Annular.canonicalAnnularCommutatorCoefficient
    F shell E velocity (Fibre.triadTransportEntry tau)

successiveDifferenceTriadCoefficient :
  ∀ {r} (F : C3.RealField r)
    (cutoff : Nat)
    (E : C3.IntegerEmbedding F)
    (velocity : Z3.FourierMode → C3.Complex3 F) →
  Triad.PhysicalTriadIncidence → C3.Complex F
successiveDifferenceTriadCoefficient F cutoff E velocity tau =
  C3.complexSubtract
    (lowTriadCoefficient F (suc cutoff) E velocity tau)
    (lowTriadCoefficient F cutoff E velocity tau)

pointwiseSuccessiveDifferenceIsAnnular :
  ∀ {r} (F : C3.RealField r)
    (cutoff : Nat)
    (E : C3.IntegerEmbedding F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (tau : Triad.PhysicalTriadIncidence) →
  successiveDifferenceTriadCoefficient F cutoff E velocity tau
  ≡ annularTriadCoefficient F (suc cutoff) E velocity tau
pointwiseSuccessiveDifferenceIsAnnular F cutoff E velocity tau =
  Annular.successiveLowCommutatorDifferenceIsAnnular
    F cutoff E velocity (Fibre.triadTransportEntry tau)

mapSuccessiveDifferenceIsAnnular :
  ∀ {r} (F : C3.RealField r)
    (cutoff : Nat)
    (E : C3.IntegerEmbedding F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (triads : List Triad.PhysicalTriadIncidence) →
  map (successiveDifferenceTriadCoefficient F cutoff E velocity) triads
  ≡ map (annularTriadCoefficient F (suc cutoff) E velocity) triads
mapSuccessiveDifferenceIsAnnular F cutoff E velocity [] = refl
mapSuccessiveDifferenceIsAnnular F cutoff E velocity (tau ∷ rest)
  rewrite pointwiseSuccessiveDifferenceIsAnnular F cutoff E velocity tau
        | mapSuccessiveDifferenceIsAnnular F cutoff E velocity rest = refl

annularOutputFibreCoefficients :
  ∀ {r} (F : C3.RealField r)
    (shell enumerationCutoff : Nat)
    (E : C3.IntegerEmbedding F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (output : Z3.FourierMode) →
  List (C3.Complex F)
annularOutputFibreCoefficients F shell enumerationCutoff E velocity output =
  map (annularTriadCoefficient F shell E velocity)
    (Output.physicalOutputFiber enumerationCutoff output)

successiveLowOutputFibreDifferenceIsAnnularOutputFibre :
  ∀ {r} (F : C3.RealField r)
    (cutoff enumerationCutoff : Nat)
    (E : C3.IntegerEmbedding F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (output : Z3.FourierMode) →
  map (successiveDifferenceTriadCoefficient F cutoff E velocity)
    (Output.physicalOutputFiber enumerationCutoff output)
  ≡ annularOutputFibreCoefficients
      F (suc cutoff) enumerationCutoff E velocity output
successiveLowOutputFibreDifferenceIsAnnularOutputFibre
    F cutoff enumerationCutoff E velocity output =
  mapSuccessiveDifferenceIsAnnular F cutoff E velocity
    (Output.physicalOutputFiber enumerationCutoff output)

round63AnnularizedCollisionVectorConstructedOnPhysicalOutputFibre : Bool
round63AnnularizedCollisionVectorConstructedOnPhysicalOutputFibre = true

round63AnnularizedCollisionVectorConstructedOnPhysicalOutputFibreIsTrue :
  round63AnnularizedCollisionVectorConstructedOnPhysicalOutputFibre ≡ true
round63AnnularizedCollisionVectorConstructedOnPhysicalOutputFibreIsTrue = refl
