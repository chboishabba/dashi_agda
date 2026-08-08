module DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSumRound25Exact where

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
-- DASHI CONTRIBUTION
--
-- The prior finite accounting theorem partitioned values only after a caller
-- had supplied abstract tags.  Round 25 now obtains those tags from the actual
-- physical Z^3 output fibre.  For every rational interaction functional, the
-- literal resonant convolution sum is proved exactly equal to its LH, HL, CC
-- and HH-to-low class sums; adding the differentiated commutator gives the
-- exact five-source identity with no unnamed remainder.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNLuoFiniteBonyFourClassAccountingExact as Four
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as Support

triadValueSum :
  (Physical.PhysicalTriadIncidence → ℚ) →
  List Physical.PhysicalTriadIncidence → ℚ
triadValueSum value [] = 0ℚ
triadValueSum value (τ ∷ rest) =
  value τ + triadValueSum value rest

interactionClassOf :
  Support.TriadicSourceClass → Four.InteractionClass
interactionClassOf Support.LH = Four.lowHighClass
interactionClassOf Support.HL = Four.highLowClass
interactionClassOf Support.HH = Four.highHighToLowClass
interactionClassOf Support.CC = Four.comparableClass

tagClassifiedTriad :
  (Physical.PhysicalTriadIncidence → ℚ) →
  Support.ClassifiedPhysicalTriad → Four.TaggedInteraction
tagClassifiedTriad value classified =
  Four.tagged-interaction
    (interactionClassOf (Support.sourceClass classified))
    (value (Support.incidence classified))

tagClassifiedTriads :
  (Physical.PhysicalTriadIncidence → ℚ) →
  List Support.ClassifiedPhysicalTriad →
  List Four.TaggedInteraction
tagClassifiedTriads value [] = []
tagClassifiedTriads value (τ ∷ rest) =
  tagClassifiedTriad value τ ∷ tagClassifiedTriads value rest

classifiedHeadValuePreserved :
  (value : Physical.PhysicalTriadIncidence → ℚ) →
  (τ : Physical.PhysicalTriadIncidence) →
  Four.interactionValue
    (tagClassifiedTriad value (Support.classifyOnePhysicalTriad τ))
  ≡ value τ
classifiedHeadValuePreserved value τ
  with Support.classifyPhysicalTriad τ
... | source , certificate = refl

physicalClassificationPreservesTotal :
  (value : Physical.PhysicalTriadIncidence → ℚ) →
  (triads : List Physical.PhysicalTriadIncidence) →
  Four.allInteractionSum
    (tagClassifiedTriads value (Support.classifyPhysicalTriads triads))
  ≡ triadValueSum value triads
physicalClassificationPreservesTotal value [] = refl
physicalClassificationPreservesTotal value (τ ∷ rest)
  rewrite classifiedHeadValuePreserved value τ
        | physicalClassificationPreservesTotal value rest = refl

physicalTaggedOutputFiber :
  Nat → Z3.FourierMode →
  (Physical.PhysicalTriadIncidence → ℚ) →
  List Four.TaggedInteraction
physicalTaggedOutputFiber cutoff output value =
  tagClassifiedTriads value
    (Support.classifiedPhysicalOutputFiber cutoff output)

physicalOutputInteractionSum :
  Nat → Z3.FourierMode →
  (Physical.PhysicalTriadIncidence → ℚ) → ℚ
physicalOutputInteractionSum cutoff output value =
  triadValueSum value (Output.physicalOutputFiber cutoff output)

physicalTaggedOutputSumAgrees :
  (cutoff : Nat) →
  (output : Z3.FourierMode) →
  (value : Physical.PhysicalTriadIncidence → ℚ) →
  Four.allInteractionSum
    (physicalTaggedOutputFiber cutoff output value)
  ≡ physicalOutputInteractionSum cutoff output value
physicalTaggedOutputSumAgrees cutoff output value =
  physicalClassificationPreservesTotal value
    (Output.physicalOutputFiber cutoff output)

physicalFourClassPartitionExact :
  (cutoff : Nat) →
  (output : Z3.FourierMode) →
  (value : Physical.PhysicalTriadIncidence → ℚ) →
  physicalOutputInteractionSum cutoff output value
  ≡
  Four.lowHighSum (physicalTaggedOutputFiber cutoff output value)
  + Four.highLowSum (physicalTaggedOutputFiber cutoff output value)
  + Four.comparableSum (physicalTaggedOutputFiber cutoff output value)
  + Four.highHighToLowSum (physicalTaggedOutputFiber cutoff output value)
physicalFourClassPartitionExact cutoff output value =
  trans
    (let agreement = physicalTaggedOutputSumAgrees cutoff output value
     in Relation.Binary.PropositionalEquality.sym agreement)
    (Four.fourClassPartitionExact
      (physicalTaggedOutputFiber cutoff output value))
  where
  import Relation.Binary.PropositionalEquality

fiveSourceTotal :
  (cutoff : Nat) →
  (output : Z3.FourierMode) →
  (value : Physical.PhysicalTriadIncidence → ℚ) →
  ℚ → ℚ
fiveSourceTotal cutoff output value commutatorValue =
  physicalOutputInteractionSum cutoff output value + commutatorValue

physicalFiveSourcePartitionExact :
  (cutoff : Nat) →
  (output : Z3.FourierMode) →
  (value : Physical.PhysicalTriadIncidence → ℚ) →
  (commutatorValue : ℚ) →
  fiveSourceTotal cutoff output value commutatorValue
  ≡
  Four.highHighToLowSum (physicalTaggedOutputFiber cutoff output value)
  + Four.lowHighSum (physicalTaggedOutputFiber cutoff output value)
  + Four.highLowSum (physicalTaggedOutputFiber cutoff output value)
  + Four.comparableSum (physicalTaggedOutputFiber cutoff output value)
  + commutatorValue
physicalFiveSourcePartitionExact cutoff output value commutatorValue
  rewrite physicalFourClassPartitionExact cutoff output value =
  solve
    ( Four.lowHighSum (physicalTaggedOutputFiber cutoff output value)
    ∷ Four.highLowSum (physicalTaggedOutputFiber cutoff output value)
    ∷ Four.comparableSum (physicalTaggedOutputFiber cutoff output value)
    ∷ Four.highHighToLowSum (physicalTaggedOutputFiber cutoff output value)
    ∷ commutatorValue
    ∷ [])
