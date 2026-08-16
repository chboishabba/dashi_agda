module DASHI.Physics.Closure.NSTriadKNComLiteralBonyOutputFibrePartitionRound63Exact where

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
-- ROUND 63 B0 DIAGNOSTIC OUTPUT-FIBRE PARTITION
--
-- Partition the ACTUAL finite `physicalOutputFiber` consumed by the Round57
-- odd-P/Q kernel using the mature strict four-way physical Bony classifier:
--
--   LH, HL, HH->low, CC/comparable.
--
-- This partition is deliberately labelled DIAGNOSTIC.  It decomposes the
-- triadic summands from which the differentiated commutator is calculated, but
-- does NOT by itself reassign those summands from the fifth Com owner into the
-- four triadic owners.  Round25's physical five-source theorem keeps the four
-- triadic classes and the appended differentiated-commutator cell distinct.
-- Any owner transfer would therefore require an additional exact cancellation
-- or reallocation theorem.
--
-- Every original fibre incidence belongs to exactly one filtered list; every
-- filtered incidence is an original fibre incidence; and filtering leaves the
-- literal Round57 odd-P/Q coefficient unchanged.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (map)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNComLiteralOddPQKernelRound57Exact as Odd
import DASHI.Physics.Closure.NSTriadKNLiteralBonyInteractionRoutingRound63Exact as Routing

data BonyTag : Set where
  lhTag hlTag hhToLowTag comparableTag : BonyTag

bonyTagEqual : BonyTag → BonyTag → Bool
bonyTagEqual lhTag lhTag = true
bonyTagEqual lhTag _ = false
bonyTagEqual hlTag hlTag = true
bonyTagEqual hlTag _ = false
bonyTagEqual hhToLowTag hhToLowTag = true
bonyTagEqual hhToLowTag _ = false
bonyTagEqual comparableTag comparableTag = true
bonyTagEqual comparableTag _ = false

bonyTagEqualRefl : (tag : BonyTag) → bonyTagEqual tag tag ≡ true
bonyTagEqualRefl lhTag = refl
bonyTagEqualRefl hlTag = refl
bonyTagEqualRefl hhToLowTag = refl
bonyTagEqualRefl comparableTag = refl

bonyTagEqualSound : ∀ {left right} → bonyTagEqual left right ≡ true → left ≡ right
bonyTagEqualSound {lhTag} {lhTag} proof = refl
bonyTagEqualSound {lhTag} {hlTag} ()
bonyTagEqualSound {lhTag} {hhToLowTag} ()
bonyTagEqualSound {lhTag} {comparableTag} ()
bonyTagEqualSound {hlTag} {lhTag} ()
bonyTagEqualSound {hlTag} {hlTag} proof = refl
bonyTagEqualSound {hlTag} {hhToLowTag} ()
bonyTagEqualSound {hlTag} {comparableTag} ()
bonyTagEqualSound {hhToLowTag} {lhTag} ()
bonyTagEqualSound {hhToLowTag} {hlTag} ()
bonyTagEqualSound {hhToLowTag} {hhToLowTag} proof = refl
bonyTagEqualSound {hhToLowTag} {comparableTag} ()
bonyTagEqualSound {comparableTag} {lhTag} ()
bonyTagEqualSound {comparableTag} {hlTag} ()
bonyTagEqualSound {comparableTag} {hhToLowTag} ()
bonyTagEqualSound {comparableTag} {comparableTag} proof = refl

bonyTag : (tau : Physical.PhysicalTriadIncidence) → BonyTag
bonyTag tau with Routing.classifyLiteralBony tau
... | Routing.lowHigh certificate = lhTag
... | Routing.highLow certificate = hlTag
... | Routing.highHighToLow certificate = hhToLowTag
... | Routing.comparable certificate = comparableTag

filterBonyTag :
  BonyTag → List Physical.PhysicalTriadIncidence →
  List Physical.PhysicalTriadIncidence
filterBonyTag tag [] = []
filterBonyTag tag (tau ∷ rest) with bonyTagEqual tag (bonyTag tau)
... | true = tau ∷ filterBonyTag tag rest
... | false = filterBonyTag tag rest

bonyOutputFibre :
  BonyTag → Nat → Z3.FourierMode → List Physical.PhysicalTriadIncidence
bonyOutputFibre tag enumerationCutoff output =
  filterBonyTag tag (Output.physicalOutputFiber enumerationCutoff output)

lhOutputFibre hlOutputFibre hhToLowOutputFibre comparableOutputFibre :
  Nat → Z3.FourierMode → List Physical.PhysicalTriadIncidence
lhOutputFibre = bonyOutputFibre lhTag
hlOutputFibre = bonyOutputFibre hlTag
hhToLowOutputFibre = bonyOutputFibre hhToLowTag
comparableOutputFibre = bonyOutputFibre comparableTag

filterTagMemberOriginal :
  ∀ {tag tau items} →
  tau Cube.∈ filterBonyTag tag items →
  tau Cube.∈ items
filterTagMemberOriginal {items = []} ()
filterTagMemberOriginal {tag} {tau} {items = head ∷ tail} member
  with bonyTagEqual tag (bonyTag head)
... | true with member
...   | Cube.here equality = Cube.here equality
...   | Cube.there rest = Cube.there (filterTagMemberOriginal rest)
... | false = Cube.there (filterTagMemberOriginal member)

filterTagMemberSound :
  ∀ {tag tau items} →
  tau Cube.∈ filterBonyTag tag items →
  bonyTag tau ≡ tag
filterTagMemberSound {items = []} ()
filterTagMemberSound {tag} {tau} {items = head ∷ tail} member
  with bonyTagEqual tag (bonyTag head) in tagProof
... | true with member
...   | Cube.here refl = sym (bonyTagEqualSound tagProof)
...   | Cube.there rest = filterTagMemberSound rest
... | false = filterTagMemberSound member

filterTagMemberComplete :
  ∀ {tag tau items} →
  tau Cube.∈ items →
  bonyTag tau ≡ tag →
  tau Cube.∈ filterBonyTag tag items
filterTagMemberComplete {items = []} () tagEquality
filterTagMemberComplete {tag} {tau} {items = head ∷ tail}
    (Cube.here refl) tagEquality
  with bonyTagEqual tag (bonyTag head) in selected
... | true = Cube.here refl
... | false =
  falseImpossible
    (trans
      (sym
        (trans
          (cong (bonyTagEqual tag) tagEquality)
          (bonyTagEqualRefl tag)))
      selected)
  where
  falseImpossible : true ≡ false →
    head Cube.∈ filterBonyTag tag (head ∷ tail)
  falseImpossible ()
filterTagMemberComplete {tag} {tau} {items = head ∷ tail}
    (Cube.there member) tagEquality
  with bonyTagEqual tag (bonyTag head)
... | true = Cube.there (filterTagMemberComplete member tagEquality)
... | false = filterTagMemberComplete member tagEquality

bonyOutputFibreMemberOriginal :
  ∀ {tag enumerationCutoff output tau} →
  tau Cube.∈ bonyOutputFibre tag enumerationCutoff output →
  tau Cube.∈ Output.physicalOutputFiber enumerationCutoff output
bonyOutputFibreMemberOriginal = filterTagMemberOriginal

bonyOutputFibreMemberHasTag :
  ∀ {tag enumerationCutoff output tau} →
  tau Cube.∈ bonyOutputFibre tag enumerationCutoff output →
  bonyTag tau ≡ tag
bonyOutputFibreMemberHasTag = filterTagMemberSound

originalOutputFibreMemberRouted :
  ∀ {enumerationCutoff output tau} →
  tau Cube.∈ Output.physicalOutputFiber enumerationCutoff output →
  (tau Cube.∈ lhOutputFibre enumerationCutoff output)
  ⊎ ((tau Cube.∈ hlOutputFibre enumerationCutoff output)
  ⊎ ((tau Cube.∈ hhToLowOutputFibre enumerationCutoff output)
  ⊎  (tau Cube.∈ comparableOutputFibre enumerationCutoff output)))
originalOutputFibreMemberRouted {tau = tau} member with bonyTag tau
... | lhTag = inj₁ (filterTagMemberComplete member refl)
... | hlTag = inj₂ (inj₁ (filterTagMemberComplete member refl))
... | hhToLowTag = inj₂ (inj₂ (inj₁ (filterTagMemberComplete member refl)))
... | comparableTag = inj₂ (inj₂ (inj₂ (filterTagMemberComplete member refl)))

memberCannotHaveTwoDistinctTags :
  ∀ {left right enumerationCutoff output tau} →
  tau Cube.∈ bonyOutputFibre left enumerationCutoff output →
  tau Cube.∈ bonyOutputFibre right enumerationCutoff output →
  left ≡ right
memberCannotHaveTwoDistinctTags leftMember rightMember =
  trans
    (sym (bonyOutputFibreMemberHasTag leftMember))
    (bonyOutputFibreMemberHasTag rightMember)

routedOddPQCoefficients :
  ∀ {r} (tag : BonyTag)
    (model : LP.PeriodicHardShellFourierPDE {r})
    (projectorCutoff enumerationCutoff : Nat)
    (E : C3.IntegerEmbedding (LP.realField model))
    (velocity : Z3.FourierMode → C3.Complex3 (LP.realField model))
    (output : Z3.FourierMode) →
  List (C3.Complex (LP.realField model))
routedOddPQCoefficients tag model projectorCutoff enumerationCutoff E velocity output =
  map
    (Odd.literalOddPQTriadCoefficient model projectorCutoff E velocity)
    (bonyOutputFibre tag enumerationCutoff output)

literalOddPQOutputFibreDiagnosticPartitioned : Bool
literalOddPQOutputFibreDiagnosticPartitioned = true

partitionDoesNotByItselfReassignComOwner : Bool
partitionDoesNotByItselfReassignComOwner = true

literalOddPQOutputFibreDiagnosticPartitionedIsTrue :
  literalOddPQOutputFibreDiagnosticPartitioned ≡ true
literalOddPQOutputFibreDiagnosticPartitionedIsTrue = refl

partitionDoesNotByItselfReassignComOwnerIsTrue :
  partitionDoesNotByItselfReassignComOwner ≡ true
partitionDoesNotByItselfReassignComOwnerIsTrue = refl
