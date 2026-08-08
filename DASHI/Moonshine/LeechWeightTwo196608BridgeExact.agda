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
-- The integer 196608 is an exact coordinate subtotal inside the rank-24
-- lattice-VOA weight-two count:
--
--   196608 = 196560 + 24 + 24.
--
-- Here 196560 counts norm-four Leech vectors, the first 24 counts h(-2)1,
-- and the second 24 counts diagonal h_i(-1)^2 coordinates after choosing a
-- basis.  The off-diagonal symmetric pairs number C(24,2)=276, so
--
--   196884 = 196608 + 276.
--
-- The conformal vector lies in the diagonal symmetric-square sector, not in
-- the off-diagonal 276-sector.  Therefore the geometrically correct quotient
-- bookkeeping is
--
--   196883 = (196608 - 1) + 276
--          = 196560 + 24 + 23 + 276.
--
-- The numerically equivalent identity 196883=196608+275 is retained only as
-- arithmetic; it is not promoted to an off-diagonal 275-dimensional subspace.
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

------------------------------------------------------------------------
-- Conformal-line quotient in the correct diagonal sector.
------------------------------------------------------------------------

conformalLineDimension : Nat
conformalLineDimension = 1

diagonalTraceFreeCount : Nat
diagonalTraceFreeCount = 23

diagonalTraceFreePlusConformal :
  diagonalTraceFreeCount + conformalLineDimension ≡ diagonalQuadraticCount
diagonalTraceFreePlusConformal = refl

traceFreeSymmetricSquareCount : Nat
traceFreeSymmetricSquareCount =
  diagonalTraceFreeCount + offDiagonalQuadraticCount

traceFreeSymmetricSquareCountIs299 :
  traceFreeSymmetricSquareCount ≡ 299
traceFreeSymmetricSquareCountIs299 = refl

monsterOscillatorQuotientCount : Nat
monsterOscillatorQuotientCount =
  secondOscillatorCount + traceFreeSymmetricSquareCount

monsterOscillatorQuotientCountIs323 :
  monsterOscillatorQuotientCount ≡ 323
monsterOscillatorQuotientCountIs323 = refl

coordinateSubtotalAfterConformalQuotient : Nat
coordinateSubtotalAfterConformalQuotient =
  leechMinimalVectorCount
  + secondOscillatorCount
  + diagonalTraceFreeCount

coordinateSubtotalAfterConformalQuotientIs196607 :
  coordinateSubtotalAfterConformalQuotient ≡ 196607
coordinateSubtotalAfterConformalQuotientIs196607 = refl

monsterNontrivialDegree : Nat
monsterNontrivialDegree = 196883

quotientedSubtotalPlusOffDiagonalIsMonsterDegree :
  coordinateSubtotalAfterConformalQuotient + offDiagonalQuadraticCount
  ≡ monsterNontrivialDegree
quotientedSubtotalPlusOffDiagonalIsMonsterDegree = refl

leechMinimalPlusMonsterOscillatorsIsMonsterDegree :
  leechMinimalVectorCount + monsterOscillatorQuotientCount
  ≡ monsterNontrivialDegree
leechMinimalPlusMonsterOscillatorsIsMonsterDegree = refl

------------------------------------------------------------------------
-- Numerically useful, but not a claimed subspace decomposition.
------------------------------------------------------------------------

numericalResidualBeyond196608 : Nat
numericalResidualBeyond196608 = 275

subtotalPlusNumericalResidualIsMonsterDegree :
  leechCoordinateSubtotal + numericalResidualBeyond196608
  ≡ monsterNontrivialDegree
subtotalPlusNumericalResidualIsMonsterDegree = refl

numericalResidualPlusConformalLineIs276 :
  numericalResidualBeyond196608 + conformalLineDimension
  ≡ offDiagonalQuadraticCount
numericalResidualPlusConformalLineIs276 = refl

residual276IsTwelveTimesTwentyThree : 12 * 23 ≡ 276
residual276IsTwelveTimesTwentyThree = refl

residual276IsFourTimesThreePowerFour : 4 * 81 ≡ 276
residual276IsFourTimesThreePowerFour = refl

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
    conformalLinePlacedInDiagonalSector : Bool
    conformalLinePlacedInDiagonalSectorIsTrue :
      conformalLinePlacedInDiagonalSector ≡ true
    diagonalOffDiagonalSplitDependsOnBasis : Bool
    diagonalOffDiagonalSplitDependsOnBasisIsTrue :
      diagonalOffDiagonalSplitDependsOnBasis ≡ true
    numerical275IsCanonicalSubspace : Bool
    numerical275IsCanonicalSubspaceIsFalse :
      numerical275IsCanonicalSubspace ≡ false
    subtotalIsMonsterInvariantSubmodule : Bool
    subtotalIsMonsterInvariantSubmoduleIsFalse :
      subtotalIsMonsterInvariantSubmodule ≡ false
    yangMillsDenominatorProvenToComeFromLeechVOA : Bool
    yangMillsDenominatorProvenToComeFromLeechVOAIsFalse :
      yangMillsDenominatorProvenToComeFromLeechVOA ≡ false

canonicalLeechCoordinateBoundary : LeechCoordinateBoundary
canonicalLeechCoordinateBoundary =
  leechCoordinateBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
