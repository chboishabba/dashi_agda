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
-- nonlinear reality calculation.  The physical enumeration is deliberately
-- proof-bearing: completeness returns a listed representative with the same
-- p/q/k labels, not propositional equality of incidence records with possibly
-- different resonance proofs.  Round 35 respects that design.
--
-- For every literal output-fibre member at k we construct a member of the
-- output fibre at -k whose p/q/k labels are exactly the conjugates of the
-- source labels.  Repeating the construction in the reverse direction gives
-- the inverse labelled relation.  This is the correct carrier bijection for
-- finite-sum reindexing because `projectedOrderedTerm` depends only on p,q,k
-- and the velocity at p,q.
--
-- The module does not silently identify the two lists positionwise.  Turning
-- this labelled representative bijection into the corresponding finite-list
-- permutation is the remaining combinatorial step for summed nonlinear
-- reality.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Primitive using (Set)
open import Data.Product using (Σ; _,_; _×_)
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

record SameIncidenceLabels
    (left right : Physical.PhysicalTriadIncidence) : Set where
  constructor same-incidence-labels
  field
    sameP : Physical.p left ≡ Physical.p right
    sameQ : Physical.q left ≡ Physical.q right
    sameK : Physical.k left ≡ Physical.k right

open SameIncidenceLabels public

labelsFromEnumerationHit :
  ∀ {cutoff τ} →
  (hit : Physical.PhysicalTriadEnumerationHit cutoff τ) →
  SameIncidenceLabels (Physical.representative hit) τ
labelsFromEnumerationHit hit = same-incidence-labels
  (Physical.sameP hit)
  (Physical.sameQ hit)
  (Physical.sameK hit)

conjugateOutputEquality :
  ∀ {output} (τ : Physical.PhysicalTriadIncidence) →
  Physical.k τ ≡ output →
  Physical.k (Symmetry.conjugateTriad τ) ≡ Z3.negateMode output
conjugateOutputEquality τ outputEquality =
  trans
    (Symmetry.conjugateTriadK τ)
    (cong Z3.negateMode outputEquality)

record ConjugateRepresentative
    (cutoff : Nat) (output : Z3.FourierMode)
    (source : Physical.PhysicalTriadIncidence) : Set where
  field
    representative : Physical.PhysicalTriadIncidence
    representativeMember :
      representative Cube.∈
        Output.physicalOutputFiber cutoff (Z3.negateMode output)
    labelsConjugate :
      SameIncidenceLabels representative (Symmetry.conjugateTriad source)

open ConjugateRepresentative public

conjugateFiberRepresentative :
  ∀ {cutoff output source} →
  source Cube.∈ Output.physicalOutputFiber cutoff output →
  ConjugateRepresentative cutoff output source
conjugateFiberRepresentative {cutoff} {output} {source} member = record
  { representative = Physical.representative hit
  ; representativeMember =
      Output.physicalOutputFiberComplete
        (Physical.representativeListed hit)
        (trans
          (Physical.sameK hit)
          (conjugateOutputEquality source
            (Output.physicalOutputFiberSound member)))
  ; labelsConjugate = labelsFromEnumerationHit hit
  }
  where
  listed : source Cube.∈ Physical.physicalTriadEnumeration cutoff
  listed = physicalOutputFiberMemberEnumeration member

  hit : Physical.PhysicalTriadEnumerationHit
      cutoff (Symmetry.conjugateTriad source)
  hit = EnumerationClosure.listedConjugateHasRepresentative listed

reverseConjugateFiberRepresentative :
  ∀ {cutoff output source} →
  source Cube.∈
    Output.physicalOutputFiber cutoff (Z3.negateMode output) →
  Σ Physical.PhysicalTriadIncidence
    (λ representative →
      (representative Cube.∈ Output.physicalOutputFiber cutoff output)
      × SameIncidenceLabels representative (Symmetry.conjugateTriad source))
reverseConjugateFiberRepresentative {cutoff} {output} {source} member =
  let
    forward = conjugateFiberRepresentative member

    targetMember :
      representative forward Cube.∈ Output.physicalOutputFiber cutoff output
    targetMember =
      subst
        (λ selectedOutput →
          representative forward Cube.∈
            Output.physicalOutputFiber cutoff selectedOutput)
        (Symmetry.negateModeInvolutive output)
        (representativeMember forward)
  in
  representative forward , targetMember , labelsConjugate forward

record OutputFiberLabelledConjugationBijection
    (cutoff : Nat) (output : Z3.FourierMode) : Set where
  field
    forward :
      ∀ {source} →
      source Cube.∈ Output.physicalOutputFiber cutoff output →
      ConjugateRepresentative cutoff output source

    backward :
      ∀ {source} →
      source Cube.∈
        Output.physicalOutputFiber cutoff (Z3.negateMode output) →
      Σ Physical.PhysicalTriadIncidence
        (λ representative →
          (representative Cube.∈ Output.physicalOutputFiber cutoff output)
          × SameIncidenceLabels representative
              (Symmetry.conjugateTriad source))

open OutputFiberLabelledConjugationBijection public

physicalOutputFiberLabelledConjugationBijection :
  (cutoff : Nat) (output : Z3.FourierMode) →
  OutputFiberLabelledConjugationBijection cutoff output
physicalOutputFiberLabelledConjugationBijection cutoff output = record
  { forward = conjugateFiberRepresentative
  ; backward = reverseConjugateFiberRepresentative
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
