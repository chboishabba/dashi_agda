module DASHI.ComputerScience.TinyISAClosedProgramCodebookFibreExact where

open import DASHI.Core.Prelude

import DASHI.Foundations.Base369Nat as B369
import DASHI.ComputerScience.TinyRadixNeutralRegisterMachineExact as Machine
import DASHI.ComputerScience.FixedNineBitFramed27WordStorageExact as WordStorage
import DASHI.ComputerScience.EuclidGCDRegisterMachineExact as Euclid
import DASHI.ComputerScience.ModularExponentiationRegisterMachineExact as Pow
import DASHI.ComputerScience.ClassicalOrderFindingRegisterMachineExact as Order

------------------------------------------------------------------------
-- CLOSED-PROGRAM CODEBOOK FIBRE
--
-- Program storage contains only finite numeric indices.  A typed decoder
-- context supplies the actual Instruction values.  In particular, proof data
-- such as the NonZero modulus witness inside MULMOD stays in the decoder
-- context/receipt rather than being pretended to be raw bits or trits.
------------------------------------------------------------------------

record ClosedProgramCodebook : Set where
  constructor closedProgramCodebook
  field
    semanticProgram : Machine.Program
    storedIndices : List Nat
    decodeStoredIndices : List Nat → Machine.Program
    decodeExact : decodeStoredIndices storedIndices ≡ semanticProgram

open ClosedProgramCodebook public

decodeByProgram : Machine.Program → List Nat → Machine.Program
decodeByProgram program [] = []
decodeByProgram program (i ∷ is) =
  Machine.fetchInstruction program i ∷ decodeByProgram program is

indices6 : List Nat
indices6 = 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []

indices8 : List Nat
indices8 = 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ []

------------------------------------------------------------------------
-- Euclid program codebook.
------------------------------------------------------------------------

euclidCodebook : ClosedProgramCodebook
euclidCodebook = closedProgramCodebook
  Euclid.euclidProgram
  indices8
  (decodeByProgram Euclid.euclidProgram)
  refl

euclidBinaryProgramStorage : List WordStorage.BinaryWord9
euclidBinaryProgramStorage = WordStorage.encodeBinaryMemory indices8

euclidTernaryProgramStorage : List WordStorage.Ternary27Word3
euclidTernaryProgramStorage = WordStorage.encodeTernary27Memory indices8

euclidBinaryIndicesRecoverExactly :
  WordStorage.decodeBinaryMemory euclidBinaryProgramStorage ≡ indices8
euclidBinaryIndicesRecoverExactly = refl

euclidTernaryIndicesRecoverExactly :
  WordStorage.decodeTernary27Memory euclidTernaryProgramStorage ≡ indices8
euclidTernaryIndicesRecoverExactly = refl

euclidBinaryProgramRecoversExactly :
  decodeByProgram Euclid.euclidProgram
    (WordStorage.decodeBinaryMemory euclidBinaryProgramStorage)
  ≡ Euclid.euclidProgram
euclidBinaryProgramRecoversExactly = refl

euclidTernaryProgramRecoversExactly :
  decodeByProgram Euclid.euclidProgram
    (WordStorage.decodeTernary27Memory euclidTernaryProgramStorage)
  ≡ Euclid.euclidProgram
euclidTernaryProgramRecoversExactly = refl

------------------------------------------------------------------------
-- Modular exponentiation codebooks.
--
-- The stored surface is the same [0..5] for N=15 and N=21.  The decoder
-- context differs because MULMOD carries a different modulus and NonZero
-- witness.  This is intentional: program-index surface != decoded semantics.
------------------------------------------------------------------------

pow15Program : Machine.Program
pow15Program = Pow.powModProgram 15 B369.nonZero

pow21Program : Machine.Program
pow21Program = Pow.powModProgram 21 B369.nonZero

pow15Codebook : ClosedProgramCodebook
pow15Codebook = closedProgramCodebook
  pow15Program indices6 (decodeByProgram pow15Program) refl

pow21Codebook : ClosedProgramCodebook
pow21Codebook = closedProgramCodebook
  pow21Program indices6 (decodeByProgram pow21Program) refl

powBinaryProgramStorage : List WordStorage.BinaryWord9
powBinaryProgramStorage = WordStorage.encodeBinaryMemory indices6

powTernaryProgramStorage : List WordStorage.Ternary27Word3
powTernaryProgramStorage = WordStorage.encodeTernary27Memory indices6

powBinaryIndicesRecoverExactly :
  WordStorage.decodeBinaryMemory powBinaryProgramStorage ≡ indices6
powBinaryIndicesRecoverExactly = refl

powTernaryIndicesRecoverExactly :
  WordStorage.decodeTernary27Memory powTernaryProgramStorage ≡ indices6
powTernaryIndicesRecoverExactly = refl

pow15BinaryProgramRecoversExactly :
  decodeByProgram pow15Program
    (WordStorage.decodeBinaryMemory powBinaryProgramStorage)
  ≡ pow15Program
pow15BinaryProgramRecoversExactly = refl

pow21TernaryProgramRecoversExactly :
  decodeByProgram pow21Program
    (WordStorage.decodeTernary27Memory powTernaryProgramStorage)
  ≡ pow21Program
pow21TernaryProgramRecoversExactly = refl

------------------------------------------------------------------------
-- Classical order-finding codebooks.
------------------------------------------------------------------------

order15Program : Machine.Program
order15Program = Order.orderProgram 15 B369.nonZero

order21Program : Machine.Program
order21Program = Order.orderProgram 21 B369.nonZero

order15Codebook : ClosedProgramCodebook
order15Codebook = closedProgramCodebook
  order15Program indices6 (decodeByProgram order15Program) refl

order21Codebook : ClosedProgramCodebook
order21Codebook = closedProgramCodebook
  order21Program indices6 (decodeByProgram order21Program) refl

orderBinaryProgramStorage : List WordStorage.BinaryWord9
orderBinaryProgramStorage = WordStorage.encodeBinaryMemory indices6

orderTernaryProgramStorage : List WordStorage.Ternary27Word3
orderTernaryProgramStorage = WordStorage.encodeTernary27Memory indices6

order15BinaryProgramRecoversExactly :
  decodeByProgram order15Program
    (WordStorage.decodeBinaryMemory orderBinaryProgramStorage)
  ≡ order15Program
order15BinaryProgramRecoversExactly = refl

order21TernaryProgramRecoversExactly :
  decodeByProgram order21Program
    (WordStorage.decodeTernary27Memory orderTernaryProgramStorage)
  ≡ order21Program
order21TernaryProgramRecoversExactly = refl

------------------------------------------------------------------------
-- Logical representation costs.
------------------------------------------------------------------------

euclidBinaryProgramCellCost : Nat
euclidBinaryProgramCellCost = 8 * WordStorage.binaryCellsPerWord

euclidTernaryProgramCellCost : Nat
euclidTernaryProgramCellCost = 8 * WordStorage.ternary27CellsPerWord

sixInstructionBinaryProgramCellCost : Nat
sixInstructionBinaryProgramCellCost = 6 * WordStorage.binaryCellsPerWord

sixInstructionTernaryProgramCellCost : Nat
sixInstructionTernaryProgramCellCost = 6 * WordStorage.ternary27CellsPerWord

euclidBinaryProgramCellCostIs72 : euclidBinaryProgramCellCost ≡ 72
euclidBinaryProgramCellCostIs72 = refl

euclidTernaryProgramCellCostIs24 : euclidTernaryProgramCellCost ≡ 24
euclidTernaryProgramCellCostIs24 = refl

sixInstructionBinaryProgramCellCostIs54 :
  sixInstructionBinaryProgramCellCost ≡ 54
sixInstructionBinaryProgramCellCostIs54 = refl

sixInstructionTernaryProgramCellCostIs18 :
  sixInstructionTernaryProgramCellCost ≡ 18
sixInstructionTernaryProgramCellCostIs18 = refl

record ClosedProgramCodebookBoundary : Set where
  constructor closedProgramCodebookBoundary
  field
    storedProgramIndicesRoundTripBinary : Bool
    storedProgramIndicesRoundTripTernary : Bool
    typedInstructionsRecoveredByDecoderContext : Bool
    proofObjectsStoredAsRawBits : Bool
    sameIndicesCanUseDifferentTypedDecoderContexts : Bool
    sameIndexSurfaceImpliesSameDecodedProgram : Bool
    fewerLogicalCellsImpliesLowerPhysicalCost : Bool

canonicalClosedProgramCodebookBoundary : ClosedProgramCodebookBoundary
canonicalClosedProgramCodebookBoundary = closedProgramCodebookBoundary
  true true true false true false false
