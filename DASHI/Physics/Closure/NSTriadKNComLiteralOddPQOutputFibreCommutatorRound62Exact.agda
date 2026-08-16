module DASHI.Physics.Closure.NSTriadKNComLiteralOddPQOutputFibreCommutatorRound62Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- DOI: 10.1007/BF02099744.
--
-- Author: Piero D'Ancona.
-- Title: "A Short Proof of Commutator Estimates".
-- DOI: 10.1007/s00041-018-9612-8.
-- Correction DOI: 10.1007/s00041-019-09724-7.
--
-- ROUND 62 CONTRIBUTION
--
-- Lift the exact entrywise projector-commutator theorem through the ACTUAL
-- `physicalOutputFiber` consumed by the literal Com/Schur lane.
--
-- For every output k and finite enumeration cutoff N the Round57 collision
-- vector
--
--   map oddPQ (physicalOutputFiber N k)
--
-- is exactly the vector obtained by mapping
--
--   (chi_P(output)-chi_P(input)) T_{output,input}
--
-- over the same incidence list.  No permutation, re-enumeration, absolute
-- value, rational surrogate, or Schur majorant occurs in the proof.
--
-- Therefore the remaining B bridge begins AFTER this point: estimate/factorize
-- this literal centered collision vector into the Round49/54 squared-output
-- Schur row coefficient and prove the same/adjacent six-three bounds.
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
import DASHI.Physics.Closure.NSTriadKNComLiteralOutputFibreKernelRound57Exact as Fibre
import DASHI.Physics.Closure.NSTriadKNComLiteralOddPQKernelRound57Exact as Odd
import DASHI.Physics.Closure.NSTriadKNComLiteralOddPQCommutatorIdentityRound62Exact as Commutator

literalProjectorCommutatorTriadCoefficient :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    (projectorCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model)) →
  Triad.PhysicalTriadIncidence → C3.Complex (LP.realField model)
literalProjectorCommutatorTriadCoefficient
    model projectorCutoff E velocity tau =
  Commutator.literalProjectorCommutatorCoefficient
    model projectorCutoff E velocity (Fibre.triadTransportEntry tau)

literalProjectorCommutatorOutputFibreCoefficients :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    (projectorCutoff enumerationCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model))
    (output : Z3.FourierMode) →
  List (C3.Complex (LP.realField model))
literalProjectorCommutatorOutputFibreCoefficients
    model projectorCutoff enumerationCutoff E velocity output =
  map
    (literalProjectorCommutatorTriadCoefficient
      model projectorCutoff E velocity)
    (Output.physicalOutputFiber enumerationCutoff output)

pointwiseOddPQIsCommutator :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    (projectorCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model))
    (tau : Triad.PhysicalTriadIncidence) →
  Odd.literalOddPQTriadCoefficient model projectorCutoff E velocity tau
  ≡ literalProjectorCommutatorTriadCoefficient
      model projectorCutoff E velocity tau
pointwiseOddPQIsCommutator model projectorCutoff E velocity tau =
  Commutator.literalOddPQIsProjectorCommutatorCoefficient
    model projectorCutoff E velocity (Fibre.triadTransportEntry tau)

mapPointwiseOddPQIsCommutator :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    (projectorCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model))
    (triads : List Triad.PhysicalTriadIncidence) →
  map (Odd.literalOddPQTriadCoefficient model projectorCutoff E velocity) triads
  ≡ map
      (literalProjectorCommutatorTriadCoefficient
        model projectorCutoff E velocity)
      triads
mapPointwiseOddPQIsCommutator model projectorCutoff E velocity [] = refl
mapPointwiseOddPQIsCommutator model projectorCutoff E velocity (tau ∷ rest)
  rewrite pointwiseOddPQIsCommutator model projectorCutoff E velocity tau
        | mapPointwiseOddPQIsCommutator
            model projectorCutoff E velocity rest = refl

literalOddPQOutputFibreIsProjectorCommutatorOutputFibre :
  ∀ {r} (model : LP.PeriodicHardShellFourierPDE {r})
    (projectorCutoff enumerationCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model))
    (output : Z3.FourierMode) →
  Odd.literalOddPQOutputFibreCoefficients
    model projectorCutoff enumerationCutoff E velocity output
  ≡ literalProjectorCommutatorOutputFibreCoefficients
      model projectorCutoff enumerationCutoff E velocity output
literalOddPQOutputFibreIsProjectorCommutatorOutputFibre
    model projectorCutoff enumerationCutoff E velocity output =
  mapPointwiseOddPQIsCommutator
    model projectorCutoff E velocity
    (Output.physicalOutputFiber enumerationCutoff output)

literalOddPQOutputFibreCommutatorIdentityClosed : Bool
literalOddPQOutputFibreCommutatorIdentityClosed = true

literalOddPQOutputFibreCommutatorIdentityClosedIsTrue :
  literalOddPQOutputFibreCommutatorIdentityClosed ≡ true
literalOddPQOutputFibreCommutatorIdentityClosedIsTrue = refl
