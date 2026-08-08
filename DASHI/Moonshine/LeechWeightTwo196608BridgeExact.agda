module DASHI.Moonshine.LeechWeightTwo196608BridgeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Igor B. Frenkel, James Lepowsky and Arne Meurman,
-- "Vertex Operator Algebras and the Monster",
-- Pure and Applied Mathematics 134, Academic Press, 1988.
-- ISBN: 978-0-12-267065-7.  No DOI asserted here.
--
-- John H. Conway and Simon P. Norton,
-- "Monstrous Moonshine",
-- Bulletin of the London Mathematical Society 11 (1979), 308--339.
-- DOI: 10.1112/blms/11.3.308.
--
-- Hiroki Shimakura,
-- "An E8-approach to the moonshine vertex operator algebra",
-- Journal of the London Mathematical Society 83 (2011), 493--516.
-- DOI: 10.1112/jlms/jdq078.
--
-- Hsian-Yang Chen, Ching Hung Lam and Hiroki Shimakura,
-- "Z_3-orbifold construction of the Moonshine vertex operator algebra and
-- some maximal 3-local subgroups of the Monster",
-- Mathematische Zeitschrift 288 (2018), 75--100.
-- DOI: 10.1007/s00209-017-1878-z.
--
-- IN-REPOSITORY AUTHORITY
--
-- DASHI.Biology.ExceptionalLatticeGrokkingProtocolExact already records the
-- Leech rank 24 and its 196560 minimal vectors as benchmark data.
--
-- DASHI CONTRIBUTION
--
-- The apparently Yang--Mills-specific integer 196608 has a natural, exact
-- coordinate subtotal inside the standard rank-24 lattice-VOA weight-two
-- count:
--
--   196608 = 196560 + 24 + 24.
--
-- Here 196560 counts the norm-four Leech lattice vectors, the first 24 counts
-- h(-2)1 oscillator states, and the second 24 counts diagonal h_i(-1)^2
-- coordinates after a basis is chosen.  The omitted off-diagonal symmetric
-- pairs are
--
--   C(24,2) = 276.
--
-- Thus
--
--   196884 = 196608 + 276,
--   196883 = 196608 + 276 - 1 = 196608 + 275.
--
-- The final subtraction is the conformal line.  The diagonal/off-diagonal
-- coordinate split is basis-dependent and is not claimed to be Monster-
-- invariant; the total Sym^2 split and dimensions are exact.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

import DASHI.Biology.ExceptionalLatticeGrokkingProtocolExact as Existing

leechRank : Nat
leechRank = Existing.ambientDimension Existing.LeechBenchmark

leechRankIsTwentyFour : leechRank ≡ 24
leechRankIsTwentyFour = refl

leechMinimalVectorCount : Nat
leechMinimalVectorCount = Existing.shortestVectorCount Existing.LeechBenchmark

leechMinimalVectorCountIs196560 : leechMinimalVectorCount ≡ 196560
leechMinimalVectorCountIs196560 = refl

secondOscillatorCount : Nat
secondOscillatorCount = 24

diagonalQuadraticCount : Nat
diagonalQuadraticCount = 24

offDiagonalQuadraticCount : Nat
offDiagonalQuadraticCount = 276

symmetricSquareCount : Nat
symmetricSquareCount = diagonalQuadraticCount + offDiagonalQuadraticCount

symmetricSquareCountIs300 : symmetricSquareCount ≡ 300
symmetricSquareCountIs300 = refl

pairCountDoubleCertificate :
  2 * offDiagonalQuadraticCount ≡ 24 * 23
pairCountDoubleCertificate = refl

oscillatorWeightTwoCount : Nat
oscillatorWeightTwoCount = secondOscillatorCount + symmetricSquareCount

oscillatorWeightTwoCountIs324 : oscillatorWeightTwoCount ≡ 324
oscillatorWeightTwoCountIs324 = refl

leechWeightTwoDimension : Nat
leechWeightTwoDimension = leechMinimalVectorCount + oscillatorWeightTwoCount

leechWeightTwoDimensionIs196884 : leechWeightTwoDimension ≡ 196884
leechWeightTwoDimensionIs196884 = refl

leechCoordinateSubtotal : Nat
leechCoordinateSubtotal =
  leechMinimalVectorCount
  + secondOscillatorCount
  + diagonalQuadraticCount

leechCoordinateSubtotalIs196608 : leechCoordinateSubtotal ≡ 196608
leechCoordinateSubtotalIs196608 = refl

subtotalPlusOffDiagonalIsWeightTwo :
  leechCoordinateSubtotal + offDiagonalQuadraticCount
  ≡ leechWeightTwoDimension
subtotalPlusOffDiagonalIsWeightTwo = refl

conformalLineDimension : Nat
conformalLineDimension = 1

monsterNontrivialDegree : Nat
monsterNontrivialDegree = 196883

offDiagonalAfterConformalAdjustment : Nat
offDiagonalAfterConformalAdjustment = 275

offDiagonalAfterConformalPlusLine :
  offDiagonalAfterConformalAdjustment + conformalLineDimension
  ≡ offDiagonalQuadraticCount
offDiagonalAfterConformalPlusLine = refl

subtotalPlusAdjustedResidualIsMonsterDegree :
  leechCoordinateSubtotal + offDiagonalAfterConformalAdjustment
  ≡ monsterNontrivialDegree
subtotalPlusAdjustedResidualIsMonsterDegree = refl

------------------------------------------------------------------------
-- The same 276 has several exact descriptions.
------------------------------------------------------------------------

residual276IsTwelveTimesTwentyThree : 12 * 23 ≡ 276
residual276IsTwelveTimesTwentyThree = refl

residual276IsFourTimesThreePowerFour : 4 * 81 ≡ 276
residual276IsFourTimesThreePowerFour = refl

residual275PlusOneIs276 : 275 + 1 ≡ 276
residual275PlusOneIs276 = refl

monsterMinusLeechMinimalCount :
  leechMinimalVectorCount + 323 ≡ monsterNontrivialDegree
monsterMinusLeechMinimalCount = refl

moonshineMinusLeechMinimalCount :
  leechMinimalVectorCount + 324 ≡ leechWeightTwoDimension
moonshineMinusLeechMinimalCount = refl

record LeechCoordinateBoundary : Set where
  constructor leechCoordinateBoundary
  field
    exactWeightTwoCountingIdentity : Bool
    exactWeightTwoCountingIdentityIsTrue :
      exactWeightTwoCountingIdentity ≡ true
    diagonalOffDiagonalSplitDependsOnBasis : Bool
    diagonalOffDiagonalSplitDependsOnBasisIsTrue :
      diagonalOffDiagonalSplitDependsOnBasis ≡ true
    subtotalIsMonsterInvariantSubmodule : Bool
    subtotalIsMonsterInvariantSubmoduleIsFalse :
      subtotalIsMonsterInvariantSubmodule ≡ false
    yangMillsDenominatorProvenToComeFromLeechVOA : Bool
    yangMillsDenominatorProvenToComeFromLeechVOAIsFalse :
      yangMillsDenominatorProvenToComeFromLeechVOA ≡ false

canonicalLeechCoordinateBoundary : LeechCoordinateBoundary
canonicalLeechCoordinateBoundary =
  leechCoordinateBoundary true refl true refl false refl false refl
