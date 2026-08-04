module DASHI.Physics.Closure.NSTriadKNLuoFiniteIndexedSourceSection4Exact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Connect the literal decidable split 2r<=q / not(2r<=q) to the finite
-- source-faithful Section-4 estimate.  The lower and upper J11 sample lists
-- are generated canonically from one indexed shell list.  Their folds are
-- proved to reconstruct the original J11 fold before the Jensen and
-- lower/upper estimates are applied.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (cong; subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoFiniteJensenSquareExact as Jensen
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicHalfSplitExact as Half
import DASHI.Physics.Closure.NSTriadKNLuoFiniteHalfShellPartitionExact as Partition
import DASHI.Physics.Closure.NSTriadKNLuoFiniteSourceFaithfulSection4Exact as Source

lowerValues :
  ∀ {outputShell} →
  List (Partition.LowerHalfSample outputShell) → List ℚ
lowerValues [] = []
lowerValues (wrapped ∷ rest) =
  Partition.amplitude (Partition.lowerSample wrapped) ∷ lowerValues rest

upperValues :
  ∀ {outputShell} →
  List (Partition.UpperHalfSample outputShell) → List ℚ
upperValues [] = []
upperValues (wrapped ∷ rest) =
  Partition.amplitude (Partition.upperSample wrapped) ∷ upperValues rest

lowerFoldAgreement :
  ∀ {outputShell}
    (samples : List (Partition.LowerHalfSample outputShell)) →
  Jensen.sumValues (lowerValues samples) ≡ Partition.sumLower samples
lowerFoldAgreement [] = refl
lowerFoldAgreement (wrapped ∷ rest)
  rewrite lowerFoldAgreement rest = refl

upperFoldAgreement :
  ∀ {outputShell}
    (samples : List (Partition.UpperHalfSample outputShell)) →
  Jensen.sumValues (upperValues samples) ≡ Partition.sumUpper samples
upperFoldAgreement [] = refl
upperFoldAgreement (wrapped ∷ rest)
  rewrite upperFoldAgreement rest = refl

record IndexedSourceSection4Data : Set where
  constructor indexed-source-section4
  field
    outputShell : Nat
    j11IndexedSamples : List Partition.IndexedShellValue
    j12Samples j2Samples : List ℚ

    j11LowerEnergy j11UpperEnergy j12Energy j2Energy : ℚ

    j11LowerSquaresBound :
      Jensen.sumSquares
        (lowerValues
          (Partition.lowerSamples
            (Partition.splitAtHalf outputShell j11IndexedSamples)))
      ≤ j11LowerEnergy

    j11UpperSquaresBound :
      Jensen.sumSquares
        (upperValues
          (Partition.upperSamples
            (Partition.splitAtHalf outputShell j11IndexedSamples)))
      ≤ j11UpperEnergy

    j12SquaresBound :
      Jensen.sumSquares j12Samples ≤ j12Energy

    j2SquaresBound :
      Jensen.sumSquares j2Samples ≤ j2Energy

open IndexedSourceSection4Data public

asSourceData :
  IndexedSourceSection4Data → Source.FiniteSourceFaithfulSection4Data
asSourceData data =
  Source.finite-source-section4
    (lowerValues
      (Partition.lowerSamples
        (Partition.splitAtHalf
          (outputShell data)
          (j11IndexedSamples data))))
    (upperValues
      (Partition.upperSamples
        (Partition.splitAtHalf
          (outputShell data)
          (j11IndexedSamples data))))
    (j12Samples data)
    (j2Samples data)
    (j11LowerEnergy data)
    (j11UpperEnergy data)
    (j12Energy data)
    (j2Energy data)
    (j11LowerSquaresBound data)
    (j11UpperSquaresBound data)
    (j12SquaresBound data)
    (j2SquaresBound data)

indexedJ11FoldMeaning :
  (data : IndexedSourceSection4Data) →
  Partition.sumOriginal (j11IndexedSamples data)
  ≡ Jensen.sumValues
      (Source.j11LowerSamples (asSourceData data))
    + Jensen.sumValues
      (Source.j11UpperSamples (asSourceData data))
indexedJ11FoldMeaning data =
  let
    split = Partition.splitAtHalf
      (outputShell data) (j11IndexedSamples data)
  in
  subst
    (λ lowerFold →
      Partition.sumOriginal (j11IndexedSamples data)
      ≡ lowerFold
        + Jensen.sumValues
            (upperValues (Partition.upperSamples split)))
    (symmetry (lowerFoldAgreement (Partition.lowerSamples split)))
    (subst
      (λ upperFold →
        Partition.sumOriginal (j11IndexedSamples data)
        ≡ Partition.sumLower (Partition.lowerSamples split) + upperFold)
      (symmetry (upperFoldAgreement (Partition.upperSamples split)))
      (Partition.halfSplitReconstructsFold
        (outputShell data) (j11IndexedSamples data)))
  where
  symmetry : ∀ {left right : ℚ} → left ≡ right → right ≡ left
  symmetry refl = refl

indexedJ11SourceBound :
  (data : IndexedSourceSection4Data) →
  L2.square (Partition.sumOriginal (j11IndexedSamples data))
  ≤ Half.two
      * ( Jensen.rationalLength
            (Source.j11LowerSamples (asSourceData data))
          * j11LowerEnergy data
        + Jensen.rationalLength
            (Source.j11UpperSamples (asSourceData data))
          * j11UpperEnergy data)
indexedJ11SourceBound data =
  subst
    (λ j11Value →
      L2.square j11Value
      ≤ Half.two
          * ( Jensen.rationalLength
                (Source.j11LowerSamples (asSourceData data))
              * j11LowerEnergy data
            + Jensen.rationalLength
                (Source.j11UpperSamples (asSourceData data))
              * j11UpperEnergy data))
    (symmetry (indexedJ11FoldMeaning data))
    (Source.j11SourceBound (asSourceData data))
  where
  symmetry : ∀ {left right : ℚ} → left ≡ right → right ≡ left
  symmetry refl = refl

finiteIndexedHalfSplitJ11Closed : Bool
finiteIndexedHalfSplitJ11Closed = true

finiteIndexedHalfSplitJ11ClosedIsTrue :
  finiteIndexedHalfSplitJ11Closed ≡ true
finiteIndexedHalfSplitJ11ClosedIsTrue = refl
