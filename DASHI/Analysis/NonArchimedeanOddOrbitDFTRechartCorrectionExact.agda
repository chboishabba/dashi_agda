module DASHI.Analysis.NonArchimedeanOddOrbitDFTRechartCorrectionExact where

------------------------------------------------------------------------
-- ARITHMETIC ODD-ORBIT RECHART CORRECTION
--
-- `DFT.index_equiv` is a carrier equivalence obtained through Fin-cardinality
-- arithmetic.  The character dynamics require a stronger arithmetic chart:
--
--   (j , 0) |->  3^j
--   (j , 1) |-> -3^j
--
-- with j modulo 2^(n-2).  In that chart multiplication by 3 advances j and
-- preserves the orbit bit.  This is the chart on which the monomial operator
-- has the advertised two-cycle meaning.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

record ArithmeticOddOrbitChart : Set₁ where
  field
    OddResidue : Set
    OrbitPosition : Set
    OrbitBit : Set

    timesThree : OddResidue → OddResidue
    nextPosition : OrbitPosition → OrbitPosition

    decode : OrbitPosition → OrbitBit → OddResidue
    encodePosition : OddResidue → OrbitPosition
    encodeBit : OddResidue → OrbitBit

    decodeAfterEncode :
      (k : OddResidue) →
      decode (encodePosition k) (encodeBit k) ≡ k

    encodePositionAfterDecode :
      (j : OrbitPosition) (b : OrbitBit) →
      encodePosition (decode j b) ≡ j

    encodeBitAfterDecode :
      (j : OrbitPosition) (b : OrbitBit) →
      encodeBit (decode j b) ≡ b

    timesThreeAdvancesPosition :
      (j : OrbitPosition) (b : OrbitBit) →
      timesThree (decode j b) ≡ decode (nextPosition j) b

open ArithmeticOddOrbitChart public

record ArithmeticChartProducerReceipts : Set where
  constructor arithmeticChartProducerReceipts
  field
    orderThreeExactlyTwoPowNMinusTwo : Bool
    powersThreeInjectiveBeforePeriod : Bool
    positiveOrbitOdd : Bool
    negativeOrbitOdd : Bool
    positiveNegativeOrbitsDisjoint : Bool
    twoOrbitsCoverAllOddResidues : Bool

canonicalArithmeticChartProducerReceipts : ArithmeticChartProducerReceipts
canonicalArithmeticChartProducerReceipts =
  arithmeticChartProducerReceipts true true true true true true

record DFTRechartBoundary : Set where
  constructor dftRechartBoundary
  field
    sourceCardinalityIndexEquivOwned : Bool
    sourceCardinalityIndexEquivCarriesOrbitSemantics : Bool
    arithmeticOddOrbitChartIsRequiredForMonomialMeaning : Bool
    arbitraryProductEnumerationMayReplaceArithmeticOrbitChart : Bool

canonicalDFTRechartBoundary : DFTRechartBoundary
canonicalDFTRechartBoundary =
  dftRechartBoundary true false true false


data RechartObligation : Set where
  constructPositivePowerOrbit : RechartObligation
  constructNegativePowerOrbit : RechartObligation
  proveOrbitDisjointness : RechartObligation
  proveOrbitCover : RechartObligation
  packageArithmeticEquivalence : RechartObligation
  reuseCardinalityIndexEquivAsOrbitChart : RechartObligation


data RechartDisposition : Set where
  live : RechartDisposition
  downstream : RechartDisposition
  forbiddenShortcut : RechartDisposition

rechartDisposition : RechartObligation → RechartDisposition
rechartDisposition constructPositivePowerOrbit = live
rechartDisposition constructNegativePowerOrbit = live
rechartDisposition proveOrbitDisjointness = live
rechartDisposition proveOrbitCover = live
rechartDisposition packageArithmeticEquivalence = downstream
rechartDisposition reuseCardinalityIndexEquivAsOrbitChart = forbiddenShortcut

highestAlphaArithmeticRechartPath : List RechartObligation
highestAlphaArithmeticRechartPath =
  constructPositivePowerOrbit ∷
  constructNegativePowerOrbit ∷
  proveOrbitDisjointness ∷
  proveOrbitCover ∷
  packageArithmeticEquivalence ∷
  []

cardinalityChartCannotSubstitute :
  DFTRechartBoundary.arbitraryProductEnumerationMayReplaceArithmeticOrbitChart
    canonicalDFTRechartBoundary
  ≡ false
cardinalityChartCannotSubstitute = refl
