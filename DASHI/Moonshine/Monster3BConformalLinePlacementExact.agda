module DASHI.Moonshine.Monster3BConformalLinePlacementExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Igor Frenkel, James Lepowsky and Arne Meurman,
-- "Vertex Operator Algebras and the Monster", Pure and Applied Mathematics
-- 134, Academic Press, 1988. ISBN 0-12-267065-5; no DOI assigned.
--
-- John H. Conway and Simon P. Norton,
-- "Monstrous Moonshine", Bulletin of the London Mathematical Society 11
-- (1979), 308--339. DOI: 10.1112/blms/11.3.308.
--
-- DASHI CONTRIBUTION
--
-- Make the 54 -> 53 transition representation-shaped rather than merely
-- modular arithmetic.  The conformal line contributes one copy of the
-- distinguished invariant eigenspace and no copy of either nontrivial C3
-- eigenspace:
--
--   (65664,65610,65610)
--     = (1,0,0) + (65663,65610,65610).
--
-- The arithmetic is checked here.  The fact that VOA automorphisms fix the
-- conformal vector is classified as a standard imported VOA fact, not as a
-- newly proved Monster-representation theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (_+_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Moonshine.Monster3BCyclicFourierDyadicBridgeExact as Fourier

addMultiplicity :
  Fourier.ThreePhaseMultiplicity →
  Fourier.ThreePhaseMultiplicity →
  Fourier.ThreePhaseMultiplicity
addMultiplicity left right =
  Fourier.threePhaseMultiplicity
    (Fourier.invariant left + Fourier.invariant right)
    (Fourier.zeta left + Fourier.zeta right)
    (Fourier.zetaSquared left + Fourier.zetaSquared right)

conformalLineMultiplicity : Fourier.ThreePhaseMultiplicity
conformalLineMultiplicity = Fourier.threePhaseMultiplicity 1 0 0

moonshineWeightTwoSplitsConformalPlusMonster :
  addMultiplicity conformalLineMultiplicity Fourier.monsterW3B
  ≡ Fourier.moonshineWeightTwo3B
moonshineWeightTwoSplitsConformalPlusMonster = refl

conformalLineInvariantMultiplicity :
  Fourier.invariant conformalLineMultiplicity ≡ 1
conformalLineInvariantMultiplicity = refl

conformalLineZetaMultiplicity :
  Fourier.zeta conformalLineMultiplicity ≡ 0
conformalLineZetaMultiplicity = refl

conformalLineZetaSquaredMultiplicity :
  Fourier.zetaSquared conformalLineMultiplicity ≡ 0
conformalLineZetaSquaredMultiplicity = refl

weightTwoInvariantMinusConformalIsMonsterInvariant :
  1 + Fourier.invariant Fourier.monsterW3B
  ≡ Fourier.invariant Fourier.moonshineWeightTwo3B
weightTwoInvariantMinusConformalIsMonsterInvariant = refl

weightTwoZetaUnchanged :
  Fourier.zeta Fourier.monsterW3B
  ≡ Fourier.zeta Fourier.moonshineWeightTwo3B
weightTwoZetaUnchanged = refl

weightTwoZetaSquaredUnchanged :
  Fourier.zetaSquared Fourier.monsterW3B
  ≡ Fourier.zetaSquared Fourier.moonshineWeightTwo3B
weightTwoZetaSquaredUnchanged = refl

weightTwoDefectDropsByOne : 53 + 1 ≡ 54
weightTwoDefectDropsByOne = refl

conformalLinePlacementArithmeticLevel : ProofLevel
conformalLinePlacementArithmeticLevel = machineChecked

conformalLineFixedByMonsterLevel : ProofLevel
conformalLineFixedByMonsterLevel = standardImported

record ConformalPlacementBoundary : Set where
  constructor conformalPlacementBoundary
  field
    arithmeticPlacementChecked : Bool
    arithmeticPlacementCheckedIsTrue :
      arithmeticPlacementChecked ≡ true

    conformalLinePlacedInNontrivialSector : Bool
    conformalLinePlacedInNontrivialSectorIsFalse :
      conformalLinePlacedInNontrivialSector ≡ false

    standardVOAFactImportedAsNewMonsterTheorem : Bool
    standardVOAFactImportedAsNewMonsterTheoremIsFalse :
      standardVOAFactImportedAsNewMonsterTheorem ≡ false

canonicalConformalPlacementBoundary : ConformalPlacementBoundary
canonicalConformalPlacementBoundary =
  conformalPlacementBoundary true refl false refl false refl
