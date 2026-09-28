module DASHI.Moonshine.OggSSPP2BadPrimeLevelStructureBoundaryExact where

------------------------------------------------------------------------
-- p=2 BAD-PRIME LEVEL-4 MODULI BOUNDARY
--
-- EXTERNAL SOURCE CONTEXT
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Annals of Mathematics Studies 108,
-- Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
--
-- The Katz--Mazur framework treats level structures, finite flat group schemes,
-- and reductions mod p as moduli problems; at primes dividing the level one
-- must not silently replace the finite flat group scheme by an etale point set.
--
-- Modern confirmation of the supersingular p-power torsion shape:
-- p^n-torsion of a supersingular elliptic curve in characteristic p is a finite
-- commutative group scheme of order p^(2n), with non-etale/infinitesimal
-- structure.  This is source context, not a theorem reconstructed here.
--
-- DASHI CONSEQUENCE
--
-- At p=2 and level 4:
--
--   group-scheme order E[4] = 2^4 = 16
--
-- whereas the current residual target has ten connected components.
--
-- Therefore the exact 1+1+8 balanced-ternary target normal form cannot be
-- identified with "the sixteen E[4] points" by cardinality.  The missing
-- arithmetic bridge must be a marked quotient/moduli construction carrying
-- finite-flat/Drinfeld/Katz--Mazur provenance.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Moonshine.OggSSPP2BalancedTernaryPuncturedPlaneExact as Balanced
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Bad-prime level-4 size calibration.
------------------------------------------------------------------------

p2Prime : Nat
p2Prime = 2

levelFour : Nat
levelFour = 4

supersingularLevelFourGroupSchemeOrder : Nat
supersingularLevelFourGroupSchemeOrder = 16

supersingularLevelFourGroupSchemeOrderIsTwoPowerFour :
  supersingularLevelFourGroupSchemeOrder
  ≡ 2 * 2 * 2 * 2
supersingularLevelFourGroupSchemeOrderIsTwoPowerFour = refl

balancedResidualTargetCount : Nat
balancedResidualTargetCount = Balanced.duplicatedCentreStateCount

balancedResidualTargetCountIsTen :
  balancedResidualTargetCount ≡ 10
balancedResidualTargetCountIsTen = refl

sixteenDoesNotEqualTen :
  supersingularLevelFourGroupSchemeOrder
  ≡ balancedResidualTargetCount ->
  ⊥
sixteenDoesNotEqualTen ()

------------------------------------------------------------------------
-- 2. Typed modelling alternatives.
------------------------------------------------------------------------

data LevelFourArithmeticModel : Set where
  naiveGeometricPointSet :
    LevelFourArithmeticModel

  finiteFlatGroupScheme :
    LevelFourArithmeticModel

  drinfeldKatzMazurLevelStructure :
    LevelFourArithmeticModel

data NaivePointSetCardinalityCreatesResidualRecognition : Set where
data GroupSchemeOrderCreatesResidualRecognition : Set where

naivePointSetCardinalityDoesNotCreateResidualRecognition :
  NaivePointSetCardinalityCreatesResidualRecognition -> ⊥
naivePointSetCardinalityDoesNotCreateResidualRecognition ()

groupSchemeOrderDoesNotCreateResidualRecognition :
  GroupSchemeOrderCreatesResidualRecognition -> ⊥
groupSchemeOrderDoesNotCreateResidualRecognition ()

------------------------------------------------------------------------
-- 3. Arithmetic acquisition contract.
--
-- A future source may choose its concrete moduli presentation, but it must
-- expose the marked quotient map and its action/orbit/stabilizer semantics.
------------------------------------------------------------------------

record P2LevelFourMarkedModuliSource : Set₁ where
  field
    FineModuliState : Set
    MarkedResidualState : Set

    sourceModel : LevelFourArithmeticModel

    sourceUsesBadPrimeLevelStructureSemantics : Bool
    sourceUsesBadPrimeLevelStructureSemanticsIsTrue :
      sourceUsesBadPrimeLevelStructureSemantics ≡ true

    markedQuotient :
      FineModuliState ->
      MarkedResidualState

    targetComparisonMap :
      MarkedResidualState ->
      Balanced.DuplicatedCentreNineSheet

    arithmeticProvenanceReference : String

open P2LevelFourMarkedModuliSource public

data ReceiptLevelCMLabelConstructsMarkedModuliSource : Set where

receiptLevelCMLabelDoesNotConstructMarkedModuliSource :
  ReceiptLevelCMLabelConstructsMarkedModuliSource -> ⊥
receiptLevelCMLabelDoesNotConstructMarkedModuliSource ()

------------------------------------------------------------------------
-- 4. Boundary.
------------------------------------------------------------------------

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryNewExtension

record P2BadPrimeLevelStructureBoundary : Set where
  constructor p2-bad-prime-level-structure-boundary
  field
    levelFourAtPrimeTwoIsBadPrimeSituation : Bool
    finiteFlatGroupSchemeSemanticsRequiredForArithmeticSource : Bool
    naiveEtalePointSetModelSufficient : Bool
    levelFourGroupSchemeOrderSixteenRecorded : Bool
    balancedResidualTargetCountTenRecorded : Bool
    sixteenEqualsTen : Bool
    balancedOneOneEightIdentifiedWithFullE4ByCount : Bool
    markedModuliQuotientStillRequired : Bool

canonicalP2BadPrimeLevelStructureBoundary :
  P2BadPrimeLevelStructureBoundary
canonicalP2BadPrimeLevelStructureBoundary =
  p2-bad-prime-level-structure-boundary
    true true false true true false false true
