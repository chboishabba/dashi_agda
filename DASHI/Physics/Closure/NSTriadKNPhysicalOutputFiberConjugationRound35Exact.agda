module DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiberConjugationRound35Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Prove the exact finite reindexing relation required after the local
-- nonlinear reality calculation.  Conjugating every retained incidence sends
-- the literal output fibre at k into the literal output fibre at -k; applying
-- conjugation again returns the same lattice p/q/k labels.  Thus the two
-- output fibres are in bijection at the physical-incidence level.
--
-- This module deliberately proves the membership/bijection theorem first.  It
-- does not silently identify the two lists positionwise: the concrete cutoff
-- enumeration has an order, while Fourier reality only supplies a finite
-- permutation.  Turning this bijection into the corresponding finite-sum
-- permutation is the remaining combinatorial step for summed nonlinear
-- reality.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalSymmetryEnumerationClosure as EnumerationClosure
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output

filterOutputMemberOriginal :
  ∀ {output items τ} →
  τ Cube.∈ Output.filterOutput output items →
  τ Cube.∈ items
filterOutputMemberOriginal {items = []} ()
filterOutputMemberOriginal {output} {items = head ∷ tail} {τ} member
  with Output.modeEqual (Physical.k head) output
... | true with member
...   | Cube.here equality = Cube.here equality
...   | Cube.there rest =
      Cube.there (filterOutputMemberOriginal rest)
... | false = Cube.there (filterOutputMemberOriginal member)

physicalOutputFiberMemberEnumeration :
  ∀ {cutoff output τ} →
  τ Cube.∈ Output.physicalOutputFiber cutoff output →
  τ Cube.∈ Physical.physicalTriadEnumeration cutoff
physicalOutputFiberMemberEnumeration = filterOutputMemberOriginal

conjugateOutputEquality :
  ∀ {output} (τ : Physical.PhysicalTriadIncidence) →
  Physical.k τ ≡ output →
  Physical.k (Symmetry.conjugateTriad τ) ≡ Z3.negateMode output
conjugateOutputEquality τ outputEquality =
  trans
    (Symmetry.conjugateTriadK τ)
    (cong Z3.negateMode outputEquality)

conjugateFiberMember :
  ∀ {cutoff output τ} →
  τ Cube.∈ Output.physicalOutputFiber cutoff output →
  Symmetry.conjugateTriad τ
    Cube.∈ Output.physicalOutputFiber cutoff (Z3.negateMode output)
conjugateFiberMember {cutoff} {output} {τ} member =
  Output.physicalOutputFiberComplete
    (EnumerationClosure.listedConjugateHasRepresentative listed)
    (conjugateOutputEquality τ
      (Output.physicalOutputFiberSound member))
  where
  listed : τ Cube.∈ Physical.physicalTriadEnumeration cutoff
  listed = physicalOutputFiberMemberEnumeration member

record SameIncidenceLabels
    (left right : Physical.PhysicalTriadIncidence) : Set where
  constructor same-incidence-labels
  field
    sameP : Physical.p left ≡ Physical.p right
    sameQ : Physical.q left ≡ Physical.q right
    sameK : Physical.k left ≡ Physical.k right

open SameIncidenceLabels public

doubleConjugateLabels :
  (τ : Physical.PhysicalTriadIncidence) →
  SameIncidenceLabels
    (Symmetry.conjugateTriad (Symmetry.conjugateTriad τ)) τ
doubleConjugateLabels τ = same-incidence-labels
  (Symmetry.sameP (Symmetry.conjugateTriadInvolutiveOnLattice τ))
  (Symmetry.sameQ (Symmetry.conjugateTriadInvolutiveOnLattice τ))
  (Symmetry.sameK (Symmetry.conjugateTriadInvolutiveOnLattice τ))

record OutputFiberConjugationBijection
    (cutoff : Nat) (output : Z3.FourierMode) : Set where
  field
    forward :
      ∀ {τ} →
      τ Cube.∈ Output.physicalOutputFiber cutoff output →
      Symmetry.conjugateTriad τ
        Cube.∈ Output.physicalOutputFiber cutoff (Z3.negateMode output)

    backward :
      ∀ {σ} →
      σ Cube.∈ Output.physicalOutputFiber cutoff (Z3.negateMode output) →
      Symmetry.conjugateTriad σ
        Cube.∈ Output.physicalOutputFiber cutoff output

    forwardBackwardLabels :
      ∀ τ → SameIncidenceLabels
        (Symmetry.conjugateTriad (Symmetry.conjugateTriad τ)) τ

open OutputFiberConjugationBijection public

physicalOutputFiberConjugationBijection :
  (cutoff : Nat) (output : Z3.FourierMode) →
  OutputFiberConjugationBijection cutoff output
physicalOutputFiberConjugationBijection cutoff output = record
  { forward = conjugateFiberMember
  ; backward = λ {σ} member →
      let
        first :
          Symmetry.conjugateTriad σ
            Cube.∈ Output.physicalOutputFiber cutoff
              (Z3.negateMode (Z3.negateMode output))
        first = conjugateFiberMember member
      in
      subst
        (λ selectedOutput →
          Symmetry.conjugateTriad σ
            Cube.∈ Output.physicalOutputFiber cutoff selectedOutput)
        (Symmetry.negateModeInvolutive output)
        first
  ; forwardBackwardLabels = doubleConjugateLabels
  }

physicalOutputFiberConjugationBijectionClosed : Bool
physicalOutputFiberConjugationBijectionClosed = true

outputFiberConjugationListPermutationConstructed : Bool
outputFiberConjugationListPermutationConstructed = false

physicalOutputFiberConjugationBijectionClosedIsTrue :
  physicalOutputFiberConjugationBijectionClosed ≡ true
physicalOutputFiberConjugationBijectionClosedIsTrue = refl

outputFiberConjugationListPermutationConstructedIsFalse :
  outputFiberConjugationListPermutationConstructed ≡ false
outputFiberConjugationListPermutationConstructedIsFalse = refl
