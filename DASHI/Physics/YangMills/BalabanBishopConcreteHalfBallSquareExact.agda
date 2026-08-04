module DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Zachary Murray, "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- Code continuation: Viktor Csimma, viktorcsimma/bishop, pinned by DASHI at
-- vendor/bishop commit 240e38c7f6938f20f865b1f956c5f084da48bd54.
--
-- PURPOSE
--
-- Instantiate the half-ball square estimate on the actual Bishop real carrier.
-- Equality is Bishop setoid equality rather than Agda propositional equality.
-- The square used by the coefficient-magnitude lane is |x|*|x|, which is
-- setoid-equal to x*x and is monotone directly from |x| <= 1/2.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as ℚ using
  (ℚᵘ; _/_; 0ℚᵘ; _*_)
import Data.Rational.Unnormalised.Properties as ℚP

import Real as BishopReal
import RealProperties as BishopProperties

open import DASHI.Physics.YangMills.CompactLieProofLevel

half quarter : ℚᵘ
half = + 1 / 2
quarter = + 1 / 4

bishopHalf bishopQuarter : BishopReal.ℝ
bishopHalf = BishopReal._⋆ half
bishopQuarter = BishopReal._⋆ quarter

bishopMagnitudeSquare : BishopReal.ℝ → BishopReal.ℝ
bishopMagnitudeSquare value =
  BishopReal._*_
    (BishopReal.∣_∣ value)
    (BishopReal.∣_∣ value)

bishopHalfNonnegative : BishopReal.NonNegative bishopHalf
bishopHalfNonnegative =
  BishopProperties.0≤x⇒nonNegx
    (BishopProperties.p≤q⇒p⋆≤q⋆
      0ℚᵘ
      half
      (ℚP.nonNegative⁻¹ half))

bishopAbsHalfEquivalentHalf :
  BishopReal._≃_ (BishopReal.∣_∣ bishopHalf) bishopHalf
bishopAbsHalfEquivalentHalf =
  BishopProperties.nonNegx⇒∣x∣≃x bishopHalfNonnegative

bishopHalfMagnitudeSquareEquivalentQuarter :
  BishopReal._≃_
    (bishopMagnitudeSquare bishopHalf)
    bishopQuarter
bishopHalfMagnitudeSquareEquivalentQuarter =
  BishopProperties.≃-trans
    (BishopProperties.*-cong
      bishopAbsHalfEquivalentHalf
      bishopAbsHalfEquivalentHalf)
    (BishopProperties.≃-trans
      (BishopProperties.≃-symm
        (BishopProperties.⋆-distrib-* half half))
      (BishopProperties.⋆-cong ℚP.≃-refl))

bishopHalfBallMagnitudeSquareBelowQuarter :
  (value : BishopReal.ℝ) →
  BishopReal._≤_ (BishopReal.∣_∣ value) bishopHalf →
  BishopReal._≤_ (bishopMagnitudeSquare value) bishopQuarter
bishopHalfBallMagnitudeSquareBelowQuarter value insideHalf =
  let absoluteValueBelowAbsoluteHalf =
        BishopProperties.≤-trans
          insideHalf
          (BishopProperties.x≤∣x∣ {x = bishopHalf})
      magnitudeSquareBelowHalfMagnitudeSquare =
        BishopProperties.*-mono-≤
          (BishopProperties.nonNeg∣x∣ value)
          (BishopProperties.nonNeg∣x∣ value)
          absoluteValueBelowAbsoluteHalf
          absoluteValueBelowAbsoluteHalf
  in BishopProperties.≤-respʳ-≃
       bishopHalfMagnitudeSquareEquivalentQuarter
       magnitudeSquareBelowHalfMagnitudeSquare

record ConcreteBishopHalfBallSquareCertificate
    (value : BishopReal.ℝ) : Set where
  field
    insideHalf :
      BishopReal._≤_ (BishopReal.∣_∣ value) bishopHalf

    squareBelowQuarter :
      BishopReal._≤_ (bishopMagnitudeSquare value) bishopQuarter

open ConcreteBishopHalfBallSquareCertificate public

concreteBishopHalfBallSquareCertificate :
  (value : BishopReal.ℝ) →
  BishopReal._≤_ (BishopReal.∣_∣ value) bishopHalf →
  ConcreteBishopHalfBallSquareCertificate value
concreteBishopHalfBallSquareCertificate value inside = record
  { insideHalf = inside
  ; squareBelowQuarter =
      bishopHalfBallMagnitudeSquareBelowQuarter value inside
  }

bishopConcreteHalfBallSquareLevel : ProofLevel
bishopConcreteHalfBallSquareLevel = machineChecked
