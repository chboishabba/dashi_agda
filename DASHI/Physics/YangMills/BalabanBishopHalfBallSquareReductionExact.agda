module DASHI.Physics.YangMills.BalabanBishopHalfBallSquareReductionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Zachary Murray, "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- This is the exact order-theoretic reduction needed by the half-radius
-- sine/cosine lane.  Once the concrete Bishop backend supplies monotonicity
-- of squaring with respect to the absolute-value bound and the normalization
-- (1/2)^2 = 1/4, the previously free square-inside-quarter field is derived.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _/_)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRationalConstantsExact as HalfRadius
open import DASHI.Physics.YangMills.CompactLieProofLevel

record BishopHalfBallSquareKernel (Real : Set) : Set₁ where
  field
    embedRational : ℚ → Real
    absolute square : Real → Real
    LessEqual : Real → Real → Set

    squareMonotoneFromAbsoluteBound :
      ∀ (x upper : Real) →
      LessEqual (absolute x) upper →
      LessEqual (square x) (square upper)

    embeddedHalfSquareIsEmbeddedQuarter :
      square (embedRational (+ 1 / 2))
        ≡ embedRational (+ 1 / 4)

open BishopHalfBallSquareKernel public

halfBallSquareBelowQuarter :
  ∀ {Real : Set} →
  (kernel : BishopHalfBallSquareKernel Real) →
  (x : Real) →
  LessEqual kernel
    (absolute kernel x)
    (embedRational kernel (+ 1 / 2)) →
  LessEqual kernel
    (square kernel x)
    (embedRational kernel (+ 1 / 4))
halfBallSquareBelowQuarter kernel x insideHalf =
  subst
    (λ upper → LessEqual kernel (square kernel x) upper)
    (embeddedHalfSquareIsEmbeddedQuarter kernel)
    (squareMonotoneFromAbsoluteBound kernel
      x
      (embedRational kernel (+ 1 / 2))
      insideHalf)

record HalfRadiusRatioEvidence : Set₁ where
  field
    sineTermRatioBelowTwentyFourth : Set
    sineTermRatioBelowTwentyFourthEvidence :
      sineTermRatioBelowTwentyFourth

    cosineTermRatioBelowEighth : Set
    cosineTermRatioBelowEighthEvidence :
      cosineTermRatioBelowEighth

open HalfRadiusRatioEvidence public

halfRadiusSeriesInputsFromSquareKernel :
  ∀ {Real : Set} →
  (kernel : BishopHalfBallSquareKernel Real) →
  (x : Real) →
  LessEqual kernel
    (absolute kernel x)
    (embedRational kernel (+ 1 / 2)) →
  (ratios : HalfRadiusRatioEvidence) →
  HalfRadius.HalfRadiusSeriesOrderInputs Real
halfRadiusSeriesInputsFromSquareKernel kernel x insideHalf ratios = record
  { embedRational = embedRational kernel
  ; absolute = absolute kernel
  ; square = square kernel
  ; LessEqual = LessEqual kernel
  ; x = x
  ; xInsideHalfBall = insideHalf
  ; squareInsideQuarter =
      halfBallSquareBelowQuarter kernel x insideHalf
  ; sineTermRatioBelowTwentyFourth =
      sineTermRatioBelowTwentyFourth ratios
  ; sineTermRatioBelowTwentyFourthEvidence =
      sineTermRatioBelowTwentyFourthEvidence ratios
  ; cosineTermRatioBelowEighth =
      cosineTermRatioBelowEighth ratios
  ; cosineTermRatioBelowEighthEvidence =
      cosineTermRatioBelowEighthEvidence ratios
  }

bishopHalfBallSquareReductionLevel : ProofLevel
bishopHalfBallSquareReductionLevel = machineChecked

bishopHalfBallSquarePhysicalKernelLevel : ProofLevel
bishopHalfBallSquarePhysicalKernelLevel = conditional
