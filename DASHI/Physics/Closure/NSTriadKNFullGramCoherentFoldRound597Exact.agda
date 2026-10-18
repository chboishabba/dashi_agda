{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNFullGramCoherentFoldRound597Exact where

------------------------------------------------------------------------
-- ROUND597 / COMPLETE FULL GRAM = COHERENT WORK OF THE FOLD
--
-- For any finite incidence list and vector-valued cell map A,
--
--   sum_{alpha,beta} W(A_alpha,A_beta)
--     = W(sum_alpha A_alpha, sum_beta A_beta),
--
-- where W(u,v)=2 Re<u,v>.
--
-- This is exact finite bilinearity only.  It is the missing representation
-- step that identifies the R596 full Gram with the SAME coherent self-work
-- coordinate used by the centered A3 normal form.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNPhysicalHeatDoubleSumFactorizationRound440Exact as R440
import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work

F : C3.RealField _
F = Rational.rationalRealField

workAddLeft :
  (leftA leftB right : C3.Complex3 F) →
  Work.coherentWork (C3.complex3Add leftA leftB) right
  ≡ Work.coherentWork leftA right + Work.coherentWork leftB right
workAddLeft leftA leftB right =
  trans
    (cong (Work.two *_) (R291.realCrossAddLeft leftA leftB right))
    (solve
      ( R179.realHermitianCross leftA right
      ∷ R179.realHermitianCross leftB right
      ∷ []))

workZeroLeft :
  (right : C3.Complex3 F) →
  Work.coherentWork (C3.complex3Zero F) right ≡ 0ℚ
workZeroLeft right =
  trans
    (cong (Work.two *_) (R440.crossZeroLeft right))
    (solve [])

workZeroRight :
  (left : C3.Complex3 F) →
  Work.coherentWork left (C3.complex3Zero F) ≡ 0ℚ
workZeroRight left =
  trans
    (cong (Work.two *_) (R440.crossZeroRight left))
    (solve [])

workPair :
  (Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence →
  Physical.PhysicalTriadIncidence → ℚ
workPair value alpha beta =
  Work.coherentWork (value alpha) (value beta)

rowWorkFactors :
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (alpha : Physical.PhysicalTriadIncidence) →
  (items : List Physical.PhysicalTriadIncidence) →
  R539.rowSum (workPair value) alpha items
  ≡ Work.coherentWork
      (value alpha)
      (R224.foldVector value items)
rowWorkFactors value alpha [] =
  sym (workZeroRight (value alpha))
rowWorkFactors value alpha (beta ∷ rest) =
  trans
    (cong
      (Work.coherentWork (value alpha) (value beta) +_)
      (rowWorkFactors value alpha rest))
    (sym
      (Work.workAddRight
        (value alpha)
        (value beta)
        (R224.foldVector value rest)))

columnWorkFactors :
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  (beta : Physical.PhysicalTriadIncidence) →
  R539.columnSum (workPair value) items beta
  ≡ Work.coherentWork
      (R224.foldVector value items)
      (value beta)
columnWorkFactors value [] beta =
  sym (workZeroLeft (value beta))
columnWorkFactors value (alpha ∷ rest) beta =
  trans
    (cong
      (Work.coherentWork (value alpha) (value beta) +_)
      (columnWorkFactors value rest beta))
    (sym
      (workAddLeft
        (value alpha)
        (R224.foldVector value rest)
        (value beta)))

fullGramIsCoherentFold :
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  R543.fullSquareSum (workPair value) items
  ≡ Work.coherentWork
      (R224.foldVector value items)
      (R224.foldVector value items)
fullGramIsCoherentFold value [] =
  sym (workZeroLeft (C3.complex3Zero F))
fullGramIsCoherentFold value (alpha ∷ rest)
  rewrite rowWorkFactors value alpha rest
        | columnWorkFactors value rest alpha
        | fullGramIsCoherentFold value rest =
  let
    a = value alpha
    tail = R224.foldVector value rest

    expanded :
      Work.coherentWork
        (C3.complex3Add a tail)
        (C3.complex3Add a tail)
      ≡
      Work.coherentWork a a
        + Work.coherentWork a tail
        + Work.coherentWork tail a
        + Work.coherentWork tail tail
    expanded =
      trans
        (workAddLeft a tail (C3.complex3Add a tail))
        (trans
          (cong₂ _+_
            (Work.workAddRight a a tail)
            (Work.workAddRight tail a tail))
          (solve
            ( Work.coherentWork a a
            ∷ Work.coherentWork a tail
            ∷ Work.coherentWork tail a
            ∷ Work.coherentWork tail tail
            ∷ [])))
  in
  trans
    (solve
      ( Work.coherentWork a a
      ∷ Work.coherentWork a tail
      ∷ Work.coherentWork tail a
      ∷ Work.coherentWork tail tail
      ∷ []))
    (sym expanded)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round597FullGramCoherentFoldClosed : Bool
round597FullGramCoherentFoldClosed = true

round597UsesOnlyFiniteBilinearity : Bool
round597UsesOnlyFiniteBilinearity = true

round597IntroducesEstimate : Bool
round597IntroducesEstimate = false

round597FullGramCoherentFoldClosedIsTrue :
  round597FullGramCoherentFoldClosed ≡ true
round597FullGramCoherentFoldClosedIsTrue = refl

round597IntroducesEstimateIsFalse :
  round597IntroducesEstimate ≡ false
round597IntroducesEstimateIsFalse = refl
