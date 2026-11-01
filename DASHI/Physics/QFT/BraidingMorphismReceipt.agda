module DASHI.Physics.QFT.BraidingMorphismReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.FinitePrimeLaneTensorFusionReceipts as Fusion
import DASHI.Physics.QFT.ArbitrarySectorExtensionReceipt as Extension

------------------------------------------------------------------------
-- Finite prime-lane braiding-morphism receipt.
--
-- This receipt records what the currently finite tensor-fusion data supports.
-- The p2/p3/p5 CM-character products are abelian, so the visible finite
-- braiding is the symmetric swap with bosonic statistics.  No (-1)^F sector,
-- anyonic Yang-Baxter solution, non-abelian braid group action, or arbitrary
-- DHR-sector extension is constructed here.

data FiniteBraidingLane : Set where
  braidingP2 :
    FiniteBraidingLane

  braidingP3 :
    FiniteBraidingLane

  braidingP5 :
    FiniteBraidingLane

data FiniteBraidingPair : Set where
  braidP2P2 :
    FiniteBraidingPair

  braidP2P3 :
    FiniteBraidingPair

  braidP2P5 :
    FiniteBraidingPair

  braidP3P2 :
    FiniteBraidingPair

  braidP3P3 :
    FiniteBraidingPair

  braidP3P5 :
    FiniteBraidingPair

  braidP5P2 :
    FiniteBraidingPair

  braidP5P3 :
    FiniteBraidingPair

  braidP5P5 :
    FiniteBraidingPair

data FiniteBraidingStatisticsKind : Set where
  bosonicTrivialSymmetricSwap :
    FiniteBraidingStatisticsKind

  fermionicMinusOneNotIntroduced :
    FiniteBraidingStatisticsKind

  anyonicYangBaxterNotConstructed :
    FiniteBraidingStatisticsKind

finitePairStatistics :
  FiniteBraidingPair →
  FiniteBraidingStatisticsKind
finitePairStatistics braidP2P2 =
  bosonicTrivialSymmetricSwap
finitePairStatistics braidP2P3 =
  bosonicTrivialSymmetricSwap
finitePairStatistics braidP2P5 =
  bosonicTrivialSymmetricSwap
finitePairStatistics braidP3P2 =
  bosonicTrivialSymmetricSwap
finitePairStatistics braidP3P3 =
  bosonicTrivialSymmetricSwap
finitePairStatistics braidP3P5 =
  bosonicTrivialSymmetricSwap
finitePairStatistics braidP5P2 =
  bosonicTrivialSymmetricSwap
finitePairStatistics braidP5P3 =
  bosonicTrivialSymmetricSwap
finitePairStatistics braidP5P5 =
  bosonicTrivialSymmetricSwap

epsilonFormulaFiniteSymmetricSwap : String
epsilonFormulaFiniteSymmetricSwap =
  "epsilon(rho_i,rho_j) is the finite symmetric swap on the abelian CM-character external-product surface"

nonAbelianBraidingGapLabel : String
nonAbelianBraidingGapLabel =
  "Non-abelian emergence requires a non-trivial (-1)^F/statistics sector or Yang-Baxter solution beyond the finite abelian CM-character surface"

data BraidingMorphismPromotionFlag : Set where

braidingMorphismPromotionFlagImpossibleHere :
  BraidingMorphismPromotionFlag →
  ⊥
braidingMorphismPromotionFlagImpossibleHere ()

record BraidingMorphismReceipt : Setω where
  field
    tensorFusionP2P3 :
      Fusion.P2P3CharacterCountEnrichment

    arbitrarySectorExtensionReceipt :
      Extension.ArbitrarySectorExtensionReceipt

    finiteBraidingPairs :
      List FiniteBraidingPair

    finiteBraidingPairsAreCanonical :
      finiteBraidingPairs
      ≡
      braidP2P2
      ∷ braidP2P3
      ∷ braidP2P5
      ∷ braidP3P2
      ∷ braidP3P3
      ∷ braidP3P5
      ∷ braidP5P2
      ∷ braidP5P3
      ∷ braidP5P5
      ∷ []

    p2p3Statistics :
      FiniteBraidingStatisticsKind

    p2p3StatisticsIsBosonicSwap :
      p2p3Statistics ≡ bosonicTrivialSymmetricSwap

    p3p5Statistics :
      FiniteBraidingStatisticsKind

    p3p5StatisticsIsBosonicSwap :
      p3p5Statistics ≡ bosonicTrivialSymmetricSwap

    p2p5Statistics :
      FiniteBraidingStatisticsKind

    p2p5StatisticsIsBosonicSwap :
      p2p5Statistics ≡ bosonicTrivialSymmetricSwap

    epsilonFormula :
      String

    epsilonFormulaIsFiniteSymmetricSwap :
      epsilonFormula ≡ epsilonFormulaFiniteSymmetricSwap

    finitePrimeLaneBosonicSurfaceInhabited :
      Bool

    finitePrimeLaneBosonicSurfaceInhabitedIsTrue :
      finitePrimeLaneBosonicSurfaceInhabited ≡ true

    fermionicMinusOneSectorIntroduced :
      Bool

    fermionicMinusOneSectorIntroducedIsFalse :
      fermionicMinusOneSectorIntroduced ≡ false

    anyonicYangBaxterSolutionConstructed :
      Bool

    anyonicYangBaxterSolutionConstructedIsFalse :
      anyonicYangBaxterSolutionConstructed ≡ false

    nonAbelianBraidingIntertwinerConstructed :
      Bool

    nonAbelianBraidingIntertwinerConstructedIsFalse :
      nonAbelianBraidingIntertwinerConstructed ≡ false

    gDHREqualsGSMPromoted :
      Bool

    gDHREqualsGSMPromotedIsFalse :
      gDHREqualsGSMPromoted ≡ false

    promotionFlags :
      List BraidingMorphismPromotionFlag

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    nonAbelianBraidingGap :
      String

    nonAbelianBraidingGapIsCanonical :
      nonAbelianBraidingGap ≡ nonAbelianBraidingGapLabel

    receiptBoundary :
      List String

open BraidingMorphismReceipt public

canonicalBraidingMorphismReceipt :
  BraidingMorphismReceipt
canonicalBraidingMorphismReceipt =
  record
    { tensorFusionP2P3 =
        Fusion.p2p3CharacterCountEnrichment
    ; arbitrarySectorExtensionReceipt =
        Extension.canonicalArbitrarySectorExtensionReceipt
    ; finiteBraidingPairs =
        braidP2P2
        ∷ braidP2P3
        ∷ braidP2P5
        ∷ braidP3P2
        ∷ braidP3P3
        ∷ braidP3P5
        ∷ braidP5P2
        ∷ braidP5P3
        ∷ braidP5P5
        ∷ []
    ; finiteBraidingPairsAreCanonical =
        refl
    ; p2p3Statistics =
        bosonicTrivialSymmetricSwap
    ; p2p3StatisticsIsBosonicSwap =
        refl
    ; p3p5Statistics =
        bosonicTrivialSymmetricSwap
    ; p3p5StatisticsIsBosonicSwap =
        refl
    ; p2p5Statistics =
        bosonicTrivialSymmetricSwap
    ; p2p5StatisticsIsBosonicSwap =
        refl
    ; epsilonFormula =
        epsilonFormulaFiniteSymmetricSwap
    ; epsilonFormulaIsFiniteSymmetricSwap =
        refl
    ; finitePrimeLaneBosonicSurfaceInhabited =
        true
    ; finitePrimeLaneBosonicSurfaceInhabitedIsTrue =
        refl
    ; fermionicMinusOneSectorIntroduced =
        false
    ; fermionicMinusOneSectorIntroducedIsFalse =
        refl
    ; anyonicYangBaxterSolutionConstructed =
        false
    ; anyonicYangBaxterSolutionConstructedIsFalse =
        refl
    ; nonAbelianBraidingIntertwinerConstructed =
        false
    ; nonAbelianBraidingIntertwinerConstructedIsFalse =
        refl
    ; gDHREqualsGSMPromoted =
        false
    ; gDHREqualsGSMPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; nonAbelianBraidingGap =
        nonAbelianBraidingGapLabel
    ; nonAbelianBraidingGapIsCanonical =
        refl
    ; receiptBoundary =
        "The finite p2/p3/p5 CM-character tensor surface supports only the symmetric bosonic swap"
        ∷ "No fermionic (-1)^F statistics operator is introduced at this finite surface"
        ∷ "No anyonic Yang-Baxter solution or non-abelian braid action is constructed"
        ∷ "The non-abelian DHR/SM gap remains exactly the arbitrary-sector braiding/intertwiner problem"
        ∷ []
    }

finitePrimeLaneBraidingIsBosonicAtCurrentSurface :
  finitePrimeLaneBosonicSurfaceInhabited canonicalBraidingMorphismReceipt
  ≡
  true
finitePrimeLaneBraidingIsBosonicAtCurrentSurface =
  refl

finitePrimeLaneBraidingDoesNotConstructNonAbelianIntertwiners :
  nonAbelianBraidingIntertwinerConstructed canonicalBraidingMorphismReceipt
  ≡
  false
finitePrimeLaneBraidingDoesNotConstructNonAbelianIntertwiners =
  refl

finitePrimeLaneBraidingDoesNotPromoteGSM :
  gDHREqualsGSMPromoted canonicalBraidingMorphismReceipt
  ≡
  false
finitePrimeLaneBraidingDoesNotPromoteGSM =
  refl
