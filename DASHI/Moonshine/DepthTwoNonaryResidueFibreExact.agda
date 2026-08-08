module DASHI.Moonshine.DepthTwoNonaryResidueFibreExact where

open import DASHI.Core.Prelude

import DASHI.Biology.ReducedFiftyThreeFibreExact as Reduced
import DASHI.Biology.SelfIndexingHyperfabricTetrationExact as Tetration
import DASHI.Biology.TernaryHypercubeHyperfabricExact as Hyper
import DASHI.Foundations.StageSymmetryCarrierTowerExact as Sym

------------------------------------------------------------------------
-- Sources and bounded source roles:
--
-- J. H. Conway and S. P. Norton, Monstrous Moonshine,
-- Bulletin of the London Mathematical Society 11 (1979), 308-339,
-- DOI 10.1112/blms/11.3.308.
--
-- Richard E. Borcherds, Monstrous Moonshine and Monstrous Lie
-- Superalgebras, Inventiones Mathematicae 109 (1992), 405-444,
-- DOI 10.1007/BF01232032.
--
-- The module checks arithmetic and finite carriers only.  It does not infer a
-- canonical Monster-module decomposition from quotient-and-remainder data.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Exact ternary and quotient/remainder identities.
------------------------------------------------------------------------

moonshineCoefficientTernaryExpansion :
  3 ^ 11 + 3 ^ 9 + 2 * (3 ^ 3) ≡ 196884
moonshineCoefficientTernaryExpansion = refl

coefficientIsExactNineClosure : 21876 * 9 ≡ 196884
coefficientIsExactNineClosure = refl

coefficientIsExactTwentySevenClosure : 7292 * 27 ≡ 196884
coefficientIsExactTwentySevenClosure = refl

coefficientDepthTwoNonaryResidue : 2430 * 81 + 54 ≡ 196884
coefficientDepthTwoNonaryResidue = refl

reducedIsMinusOneModuloNine : 21875 * 9 + 8 ≡ 196883
reducedIsMinusOneModuloNine = refl

reducedIsMinusOneModuloTwentySeven : 7291 * 27 + 26 ≡ 196883
reducedIsMinusOneModuloTwentySeven = refl

reducedDepthTwoNonaryResidue : 2430 * 81 + 53 ≡ 196883
reducedDepthTwoNonaryResidue = refl

terminalFiftyFourIsSixTimesNine : 6 * 9 ≡ 54
terminalFiftyFourIsSixTimesNine = refl

terminalFiftyFourIsTwoTimesTwentySeven : 2 * 27 ≡ 54
terminalFiftyFourIsTwoTimesTwentySeven = refl

terminalReducedPlusDistinguished : 53 + 1 ≡ 54
terminalReducedPlusDistinguished = refl

------------------------------------------------------------------------
-- The global -1 seam and terminal-fibre -1 seam use the same 81-block bulk.
-- This is the division-free commuting-square certificate.
------------------------------------------------------------------------

record DepthTwoCommutingSquare : Set where
  constructor depthTwoCommutingSquare
  field
    bulkBlockCount blockWidth fullResidue reducedResidue : Nat
    fullValue reducedValue : Nat
    fullDecomposition :
      bulkBlockCount * blockWidth + fullResidue ≡ fullValue
    reducedDecomposition :
      bulkBlockCount * blockWidth + reducedResidue ≡ reducedValue
    residueMinusOne : reducedResidue + 1 ≡ fullResidue
    valueMinusOne : reducedValue + 1 ≡ fullValue

open DepthTwoCommutingSquare public

canonicalDepthTwoCommutingSquare : DepthTwoCommutingSquare
canonicalDepthTwoCommutingSquare =
  depthTwoCommutingSquare
    2430 81 54 53 196884 196883
    refl refl refl refl

sameBulkBlockCount :
  bulkBlockCount canonicalDepthTwoCommutingSquare ≡ 2430
sameBulkBlockCount = refl

fullResidueIsFiftyFour :
  fullResidue canonicalDepthTwoCommutingSquare ≡ 54
fullResidueIsFiftyFour = refl

reducedResidueIsFiftyThree :
  reducedResidue canonicalDepthTwoCommutingSquare ≡ 53
reducedResidueIsFiftyThree = refl

------------------------------------------------------------------------
-- Structured terminal carrier candidate F_54 = F_6 x F_9.
------------------------------------------------------------------------

TerminalFibre54 : Set
TerminalFibre54 = Sym.HexadicCarrier × Sym.NonaryCarrier

terminalHexadicCount : Nat
terminalHexadicCount = Sym.hexadicCardinality

terminalNonaryCount : Nat
terminalNonaryCount = Sym.nonaryCardinality

terminalProductCount : Nat
terminalProductCount = terminalHexadicCount * terminalNonaryCount

terminalProductCountIsFiftyFour : terminalProductCount ≡ 54
terminalProductCountIsFiftyFour = refl

canonicalTerminalPoint : TerminalFibre54
canonicalTerminalPoint =
  Sym.hexadicCarrier Sym.positive Sym.direct ,
  Sym.nonaryCarrier Sym.positive Sym.positive

------------------------------------------------------------------------
-- Existing reduced carrier compatibility is currently dimensional.  A genuine
-- equivalence must identify the distinguished product point and construct a
-- bijection from its complement to ReducedMode53.
------------------------------------------------------------------------

record TerminalProductReducedEquivalence : Set₁ where
  constructor terminalProductReducedEquivalence
  field
    isDistinguished : TerminalFibre54 → Set
    distinguishedWitness : isDistinguished canonicalTerminalPoint
    encodeReduced :
      (point : TerminalFibre54) →
      ¬ isDistinguished point →
      Reduced.ReducedMode53
    decodeReduced : Reduced.ReducedMode53 → TerminalFibre54
    decodedIsNotDistinguished :
      (mode : Reduced.ReducedMode53) →
      ¬ isDistinguished (decodeReduced mode)
    encodeDecode :
      (mode : Reduced.ReducedMode53) →
      encodeReduced
        (decodeReduced mode)
        (decodedIsNotDistinguished mode)
      ≡ mode

------------------------------------------------------------------------
-- Product depth and literal self-indexed tetration are distinct.
--
--   9 x 9 = 81,
--   level-two self-indexing = 9^9.
------------------------------------------------------------------------

depthTwoNonaryProduct : 9 * 9 ≡ 81
depthTwoNonaryProduct = refl

literalNineTetrationLevelTwo :
  Tetration.selfIndexedSiteCount 2 ≡ Hyper.powNat 9 9
literalNineTetrationLevelTwo =
  Tetration.selfIndexedLevelTwoHasNineToNineSites

record DepthTwoNonaryAuthorityBoundary : Set where
  constructor depthTwoNonaryAuthorityBoundary
  field
    exactTernaryExpansionConstructed : Bool
    exactTernaryExpansionConstructedIsTrue :
      exactTernaryExpansionConstructed ≡ true
    exactCommutingResidueSquareConstructed : Bool
    exactCommutingResidueSquareConstructedIsTrue :
      exactCommutingResidueSquareConstructed ≡ true
    terminalProductCarrierConstructed : Bool
    terminalProductCarrierConstructedIsTrue :
      terminalProductCarrierConstructed ≡ true
    terminalProductEquivalentToActualReducedCarrier : Bool
    terminalProductEquivalentToActualReducedCarrierIsFalse :
      terminalProductEquivalentToActualReducedCarrier ≡ false
    canonicalEightyOneBlockMonsterModuleDecomposition : Bool
    canonicalEightyOneBlockMonsterModuleDecompositionIsFalse :
      canonicalEightyOneBlockMonsterModuleDecomposition ≡ false
    modEightyOneIsIndependentEvidenceForSelectedChart : Bool
    modEightyOneIsIndependentEvidenceForSelectedChartIsFalse :
      modEightyOneIsIndependentEvidenceForSelectedChart ≡ false
    depthTwoProductIdentifiedWithLiteralNineTetration : Bool
    depthTwoProductIdentifiedWithLiteralNineTetrationIsFalse :
      depthTwoProductIdentifiedWithLiteralNineTetration ≡ false

canonicalDepthTwoNonaryAuthorityBoundary :
  DepthTwoNonaryAuthorityBoundary
canonicalDepthTwoNonaryAuthorityBoundary =
  depthTwoNonaryAuthorityBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
