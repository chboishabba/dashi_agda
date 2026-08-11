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
-- physical Z^3 output fibre.  For every rational triadic functional and every
-- mode-indexed commutator functional, the literal five-source fibre is
-- evaluated cell by cell and proved exactly equal to its HH, LH, HL, CC and
-- Com contributions.  The commutator value is therefore derived from the
-- appended differentiatedCommutator cell, not inserted as a free scalar.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (sym; trans)

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
    (sym (physicalTaggedOutputSumAgrees cutoff output value))
    (Four.fourClassPartitionExact
      (physicalTaggedOutputFiber cutoff output value))

------------------------------------------------------------------------
-- Evaluate the actual five-source fibre.  The differentiated commutator cell
-- is interpreted by a mode-indexed functional at its stored output mode.
------------------------------------------------------------------------

fiveSourceValue :
  (Physical.PhysicalTriadIncidence → ℚ) →
  (Z3.FourierMode → ℚ) →
  Support.FiveSourceCell → ℚ
fiveSourceValue triadValue commutator
  (Support.triadicSource classified) =
  triadValue (Support.incidence classified)
fiveSourceValue triadValue commutator
  (Support.differentiatedCommutator output) =
  commutator output

fiveSourceValueSum :
  (Physical.PhysicalTriadIncidence → ℚ) →
  (Z3.FourierMode → ℚ) →
  List Support.FiveSourceCell → ℚ
fiveSourceValueSum triadValue commutator [] = 0ℚ
fiveSourceValueSum triadValue commutator (cell ∷ rest) =
  fiveSourceValue triadValue commutator cell
  + fiveSourceValueSum triadValue commutator rest

fiveSourceValueSumAppend :
  (triadValue : Physical.PhysicalTriadIncidence → ℚ) →
  (commutator : Z3.FourierMode → ℚ) →
  (left right : List Support.FiveSourceCell) →
  fiveSourceValueSum triadValue commutator
    (Support.appendFiveSources left right)
  ≡
  fiveSourceValueSum triadValue commutator left
  + fiveSourceValueSum triadValue commutator right
fiveSourceValueSumAppend triadValue commutator [] right =
  solve (fiveSourceValueSum triadValue commutator right ∷ [])
fiveSourceValueSumAppend triadValue commutator (cell ∷ rest) right
  rewrite fiveSourceValueSumAppend triadValue commutator rest right =
  solve
    ( fiveSourceValue triadValue commutator cell
    ∷ fiveSourceValueSum triadValue commutator rest
    ∷ fiveSourceValueSum triadValue commutator right
    ∷ [])

triadicFiveSourceValuesAgreeWithTaggedSum :
  (triadValue : Physical.PhysicalTriadIncidence → ℚ) →
  (commutator : Z3.FourierMode → ℚ) →
  (classified : List Support.ClassifiedPhysicalTriad) →
  fiveSourceValueSum triadValue commutator
    (Support.mapTriadicSources classified)
  ≡ Four.allInteractionSum (tagClassifiedTriads triadValue classified)
triadicFiveSourceValuesAgreeWithTaggedSum triadValue commutator [] = refl
triadicFiveSourceValuesAgreeWithTaggedSum
  triadValue commutator (classified ∷ rest)
  rewrite triadicFiveSourceValuesAgreeWithTaggedSum
    triadValue commutator rest = refl

commutatorTailEvaluatesAtOutput :
  (triadValue : Physical.PhysicalTriadIncidence → ℚ) →
  (commutator : Z3.FourierMode → ℚ) →
  (output : Z3.FourierMode) →
  fiveSourceValueSum triadValue commutator
    (Support.differentiatedCommutator output ∷ [])
  ≡ commutator output
commutatorTailEvaluatesAtOutput triadValue commutator output =
  solve (commutator output ∷ [])

fiveSourceTotal :
  Nat → Z3.FourierMode →
  (Physical.PhysicalTriadIncidence → ℚ) →
  (Z3.FourierMode → ℚ) → ℚ
fiveSourceTotal cutoff output triadValue commutator =
  fiveSourceValueSum triadValue commutator
    (Support.fiveSourceOutputFiber cutoff output)

fiveSourceTotalExpands :
  (cutoff : Nat) →
  (output : Z3.FourierMode) →
  (triadValue : Physical.PhysicalTriadIncidence → ℚ) →
  (commutator : Z3.FourierMode → ℚ) →
  fiveSourceTotal cutoff output triadValue commutator
  ≡ physicalOutputInteractionSum cutoff output triadValue
    + commutator output
fiveSourceTotalExpands cutoff output triadValue commutator
  rewrite fiveSourceValueSumAppend
            triadValue commutator
            (Support.mapTriadicSources
              (Support.classifiedPhysicalOutputFiber cutoff output))
            (Support.differentiatedCommutator output ∷ [])
        | triadicFiveSourceValuesAgreeWithTaggedSum
            triadValue commutator
            (Support.classifiedPhysicalOutputFiber cutoff output)
        | physicalTaggedOutputSumAgrees cutoff output triadValue
        | commutatorTailEvaluatesAtOutput
            triadValue commutator output = refl

physicalFiveSourcePartitionExact :
  (cutoff : Nat) →
  (output : Z3.FourierMode) →
  (triadValue : Physical.PhysicalTriadIncidence → ℚ) →
  (commutator : Z3.FourierMode → ℚ) →
  fiveSourceTotal cutoff output triadValue commutator
  ≡
  Four.highHighToLowSum
    (physicalTaggedOutputFiber cutoff output triadValue)
  + Four.lowHighSum
    (physicalTaggedOutputFiber cutoff output triadValue)
  + Four.highLowSum
    (physicalTaggedOutputFiber cutoff output triadValue)
  + Four.comparableSum
    (physicalTaggedOutputFiber cutoff output triadValue)
  + commutator output
physicalFiveSourcePartitionExact cutoff output triadValue commutator
  rewrite fiveSourceTotalExpands cutoff output triadValue commutator
        | physicalFourClassPartitionExact cutoff output triadValue =
  solve
    ( Four.lowHighSum (physicalTaggedOutputFiber cutoff output triadValue)
    ∷ Four.highLowSum (physicalTaggedOutputFiber cutoff output triadValue)
    ∷ Four.comparableSum (physicalTaggedOutputFiber cutoff output triadValue)
    ∷ Four.highHighToLowSum
        (physicalTaggedOutputFiber cutoff output triadValue)
    ∷ commutator output
    ∷ [])
