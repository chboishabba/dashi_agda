module DASHI.Wikimedia.IbrahimMonsterFiveOrbitD4N3BCharacterAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimMonsterFiveOrbitD4IrrepDecompositionKernelExact as Kernel
import DASHI.Wikimedia.IbrahimMonster3BActualLinearMultiplicityAcquisitionExact as N3B

------------------------------------------------------------------------
-- FIVE-ORBIT D4 -> ACTUAL N(3B) CHARACTER ACQUISITION FRONTIER
--
-- The phase-preserving ternary-27 reduction has now reached a theorem-shaped
-- D4 quotient representation with character
--
--   chi_D4 = (5,5,1,3,3)
--
-- and source-written irreducible content
--
--   3 A1 + B1 + B2,
--
-- with A2 = E = 0.
--
-- Independently, the actual Monster N(3B) acquisition lane has source-paid
-- occurrence of the 17496 and 113724 constituents and has localized the first
-- unpaid action-level seam to Selected3BNormalizerMonsterActionWeld.
--
-- This owner does NOT identify the D4 quotient action with a subgroup action
-- inside N(3B).  It only localizes the next comparison: first obtain the actual
-- selected normalizer-to-Monster action weld; then exhibit a D4 subgroup/action
-- restriction whose character on the five-orbit quotient can be compared with
-- the source-written D4 character above.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Exact source anchors.
------------------------------------------------------------------------

kernelBoundary : Kernel.FiveOrbitD4IrrepKernelBoundary
kernelBoundary = Kernel.currentFiveOrbitD4IrrepKernelBoundary

n3bFrontier : N3B.ActualLinearMultiplicityAcquisitionFrontier
n3bFrontier = N3B.currentActualLinearMultiplicityAcquisitionFrontier

kernelA1MultiplicityIsThree : Kernel.a1Multiplicity ≡ 3
kernelA1MultiplicityIsThree = Kernel.a1MultiplicityIsThree

kernelA2MultiplicityIsZero : Kernel.a2Multiplicity ≡ 0
kernelA2MultiplicityIsZero = Kernel.a2MultiplicityIsZero

kernelB1MultiplicityIsOne : Kernel.b1Multiplicity ≡ 1
kernelB1MultiplicityIsOne = Kernel.b1MultiplicityIsOne

kernelB2MultiplicityIsOne : Kernel.b2Multiplicity ≡ 1
kernelB2MultiplicityIsOne = Kernel.b2MultiplicityIsOne

kernelEMultiplicityIsZero : Kernel.eMultiplicity ≡ 0
kernelEMultiplicityIsZero = Kernel.eMultiplicityIsZero

n3b17496OccurrencePaid :
  N3B.degree17496OccurrencePaid n3bFrontier ≡ true
n3b17496OccurrencePaid = refl

n3b113724OccurrencePaid :
  N3B.degree113724OccurrencePaid n3bFrontier ≡ true
n3b113724OccurrencePaid = refl

------------------------------------------------------------------------
-- WrongType / promotion firewalls.
------------------------------------------------------------------------

data EqualD4MultiplicityCreatesNormalizerEmbedding : Set where
data N3BOccurrenceCreatesD4CharacterIdentity : Set where
data D4CharacterCreatesMonster42dAction : Set where
data OEISCreatesD4N3BActionBridge : Set where

equalD4MultiplicityDoesNotCreateNormalizerEmbedding :
  EqualD4MultiplicityCreatesNormalizerEmbedding → ⊥
equalD4MultiplicityDoesNotCreateNormalizerEmbedding ()

n3bOccurrenceDoesNotCreateD4CharacterIdentity :
  N3BOccurrenceCreatesD4CharacterIdentity → ⊥
n3bOccurrenceDoesNotCreateD4CharacterIdentity ()

d4CharacterDoesNotCreateMonster42dAction :
  D4CharacterCreatesMonster42dAction → ⊥
d4CharacterDoesNotCreateMonster42dAction ()

oeisDoesNotCreateD4N3BActionBridge :
  OEISCreatesD4N3BActionBridge → ⊥
oeisDoesNotCreateD4N3BActionBridge ()

------------------------------------------------------------------------
-- Acquisition boundary.
------------------------------------------------------------------------

record FiveOrbitD4N3BAcquisitionBoundary : Set where
  constructor five-orbit-d4-n3b-acquisition-boundary
  field
    phasePreservingTernary27ReductionPaid : Bool
    kernelD4PermutationCharacterSourceWritten : Bool
    kernelD4QuotientDecompositionSourceWritten : Bool
    quotientDecompositionThreeA1B1B2Retained : Bool
    actualN3BRestrictionOccurrencesPaid : Bool
    selected3BNormalizerMonsterActionWeldInterfaceLocated : Bool
    selected3BNormalizerMonsterActionWeldPaid : Bool
    d4SubgroupEmbeddingIntoSelectedNormalizerPaid : Bool
    d4QuotientCharacterRestrictionSameObjectPaid : Bool
    d4QuotientEqualsN3BCharacter : Bool
    monster42dActionPaid : Bool
    oeisCreatesActionBridge : Bool
    nextResidual : String
open FiveOrbitD4N3BAcquisitionBoundary public

currentFiveOrbitD4N3BAcquisitionBoundary : FiveOrbitD4N3BAcquisitionBoundary
currentFiveOrbitD4N3BAcquisitionBoundary =
  five-orbit-d4-n3b-acquisition-boundary
    true true true true true true
    false false false false false false
    "First inhabit the existing Selected3BNormalizerMonsterActionWeld: supply the actual normalizerToMonster embedding and action intertwining on the selected 196883 State. Then acquire an explicit D4 subgroup/action map into that SAME selected normalizer action and prove that the induced five-orbit restriction character is the kernel-source character (5,5,1,3,3), equivalently 3*A1+B1+B2. Only after that comparison should the D4 quotient be used against the 42d/N(3B) bridge frontier. Degree occurrence, matching dimensions, OEIS coordinates, and the numeral five do not create the subgroup embedding, same-object character, or Monster action."
