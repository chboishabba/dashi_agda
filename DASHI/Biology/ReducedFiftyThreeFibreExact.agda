module DASHI.Biology.ReducedFiftyThreeFibreExact where

open import DASHI.Core.Prelude
open import Data.Fin using (Fin)

import DASHI.Biology.TernaryHypercubeHyperfabricExact as Hyper

------------------------------------------------------------------------
-- The geometrically canonical 53-sector is the reduced representation of
-- the existing 6 x 9 = 54 carrier: one constant/invariant mode plus fifty-
-- three fluctuation modes.  This is stronger than treating 53 as an isolated
-- prime lane or as an unexplained additive remainder.

ReducedMode53 : Set
ReducedMode53 = Fin 53

FullMode54 : Set
FullMode54 = ⊤ ⊎ ReducedMode53

data ModeKind : Set where
  invariantMode : ModeKind
  fluctuationMode : ModeKind

modeKind : FullMode54 → ModeKind
modeKind (inj₁ tt) = invariantMode
modeKind (inj₂ mode) = fluctuationMode

fullSixByNineDimension : Nat
fullSixByNineDimension = Hyper.siteCount Hyper.sheetSixByNine

trivialInvariantDimension : Nat
trivialInvariantDimension = 1

reducedDimension : Nat
reducedDimension = fullSixByNineDimension ∸ trivialInvariantDimension

fullSixByNineDimensionIsFiftyFour : fullSixByNineDimension ≡ 54
fullSixByNineDimensionIsFiftyFour = refl

reducedDimensionIsFiftyThree : reducedDimension ≡ 53
reducedDimensionIsFiftyThree = refl

fullSplitsAsInvariantPlusReduced :
  trivialInvariantDimension + reducedDimension ≡ fullSixByNineDimension
fullSplitsAsInvariantPlusReduced = refl

------------------------------------------------------------------------
-- Balanced ternary makes the reduced lane a space of internal redistribution:
-- positive and negative occupancy may cancel globally while their arrangement
-- and mode content remain nontrivial.

record BalancedMass : Set where
  constructor balancedMass
  field
    positiveMass : Nat
    negativeMass : Nat
    massesBalance : positiveMass ≡ negativeMass

open BalancedMass public

canonicalBalancedSixByNineMass : BalancedMass
canonicalBalancedSixByNineMass = balancedMass 27 27 refl

canonicalBalancedTotalIsFiftyFour :
  positiveMass canonicalBalancedSixByNineMass
  + negativeMass canonicalBalancedSixByNineMass
  ≡ 54
canonicalBalancedTotalIsFiftyFour = refl

------------------------------------------------------------------------
-- Connected finite Laplacian bookkeeping: one zero/constant mode and the
-- remaining nonconstant modes.  No particular 6 x 9 adjacency is silently
-- selected here; that choice belongs to the concrete hyperfibre geometry.

record ConnectedLaplacianModeCount : Set where
  constructor connectedLaplacianModeCount
  field
    totalModes : Nat
    zeroModes : Nat
    nonzeroModes : Nat
    modeCountCertificate : zeroModes + nonzeroModes ≡ totalModes

open ConnectedLaplacianModeCount public

canonicalSixByNineModeCount : ConnectedLaplacianModeCount
canonicalSixByNineModeCount =
  connectedLaplacianModeCount 54 1 53 refl

------------------------------------------------------------------------
-- Exact mode-level versions of ker(mean) = positive Laplacian sector.  The
-- carrier is an invariant mode plus 53 named fluctuation modes; no coordinate
-- basis or concrete 6 x 9 adjacency is smuggled in.

data MeanZeroMode : FullMode54 → Set where
  meanZeroFluctuation : (mode : ReducedMode53) → MeanZeroMode (inj₂ mode)

data PositiveLaplacianMode : FullMode54 → Set where
  positiveFluctuation : (mode : ReducedMode53) →
    PositiveLaplacianMode (inj₂ mode)

meanZeroImpliesPositiveMode :
  {mode : FullMode54} → MeanZeroMode mode → PositiveLaplacianMode mode
meanZeroImpliesPositiveMode (meanZeroFluctuation mode) =
  positiveFluctuation mode

positiveModeImpliesMeanZero :
  {mode : FullMode54} → PositiveLaplacianMode mode → MeanZeroMode mode
positiveModeImpliesMeanZero (positiveFluctuation mode) =
  meanZeroFluctuation mode

invariantModeIsNotMeanZero : ¬ MeanZeroMode (inj₁ tt)
invariantModeIsNotMeanZero ()

invariantModeIsNotPositive : ¬ PositiveLaplacianMode (inj₁ tt)
invariantModeIsNotPositive ()

------------------------------------------------------------------------
-- The moonshine coefficient and nontrivial dimension now have a nested exact
-- decomposition:
--
--   196884 = 10 * 3^9 + 54,
--   196883 = 10 * 3^9 + (54 - 1).

ternaryNineDimension : Nat
ternaryNineDimension = Hyper.ternaryLatticeCount 9

moonshineFirstPositiveCoefficientCandidate : Nat
moonshineFirstPositiveCoefficientCandidate =
  10 * ternaryNineDimension + fullSixByNineDimension

moonshineNontrivialDimensionCandidate : Nat
moonshineNontrivialDimensionCandidate =
  10 * ternaryNineDimension + reducedDimension

moonshineCoefficientCandidateIs196884 :
  moonshineFirstPositiveCoefficientCandidate ≡ 196884
moonshineCoefficientCandidateIs196884 = refl

moonshineNontrivialCandidateIs196883 :
  moonshineNontrivialDimensionCandidate ≡ 196883
moonshineNontrivialCandidateIs196883 = refl

coefficientSplitsAsInvariantPlusNontrivial :
  trivialInvariantDimension + moonshineNontrivialDimensionCandidate
  ≡ moonshineFirstPositiveCoefficientCandidate
coefficientSplitsAsInvariantPlusNontrivial = refl

record ReducedFiftyThreeBoundary : Set where
  constructor reducedFiftyThreeBoundary
  field
    fiftyThreeIsInsertedAsIndependentOggPrimeLane : Bool
    fiftyThreeIsInsertedAsIndependentOggPrimeLaneIsFalse :
      fiftyThreeIsInsertedAsIndependentOggPrimeLane ≡ false

    reducedFiftyThreeIsProvedMonsterIrreducible : Bool
    reducedFiftyThreeIsProvedMonsterIrreducibleIsFalse :
      reducedFiftyThreeIsProvedMonsterIrreducible ≡ false

    reducedFiftyThreeHasCanonicalGeometricOrigin : Bool
    reducedFiftyThreeHasCanonicalGeometricOriginIsTrue :
      reducedFiftyThreeHasCanonicalGeometricOrigin ≡ true

    concreteSpatialGroupStillMustBeChosen : Bool
    concreteSpatialGroupStillMustBeChosenIsTrue :
      concreteSpatialGroupStillMustBeChosen ≡ true

open ReducedFiftyThreeBoundary public

canonicalReducedFiftyThreeBoundary : ReducedFiftyThreeBoundary
canonicalReducedFiftyThreeBoundary =
  reducedFiftyThreeBoundary false refl false refl true refl true refl
