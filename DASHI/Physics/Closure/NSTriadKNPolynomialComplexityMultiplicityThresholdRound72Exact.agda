module DASHI.Physics.Closure.NSTriadKNPolynomialComplexityMultiplicityThresholdRound72Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND72 / MULTIPLICITY THRESHOLD
--
-- Round72 proves that a raw effective complexity N^d at frequency N=2^j
-- induces the reciprocal shell loss 2^(-dj) in the simplest Cauchy model.
-- Round71 already showed binary branching exactly compensates 2^(-j).
--
-- This file computes the next two thresholds exactly:
--
--   4 descendants per step x 1/4 floor loss  -> conserved generation mass,
--   8 descendants per step x 1/8 floor loss  -> conserved generation mass.
--
-- Thus an N^2 raw-complexity loss needs physical multiplicity on the order of
-- 4^j to remain critical, while an N^3 loss needs order 8^j.  These are
-- arithmetic thresholds only: no claim is made that Navier--Stokes supplies
-- four/eight genuinely separated descendants per shell step.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Rational.Base using (ℚ; 1ℚ; _*_; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSTriadKNHHBadDyadicScalePrimitivesRound58 as Scale
import DASHI.Physics.Closure.NSTriadKNScaleDependentConcentrationFundingRound70Exact as Funding
import DASHI.Physics.Closure.NSTriadKNBranchingCompensatesDyadicLossRound71Exact as Branch

quarter eighth : ℚ
quarter = Scale.half * Scale.half
eighth = quarter * Scale.half

append4 : List ℚ → List ℚ
append4 block =
  Branch.appendFloors block
    (Branch.appendFloors block
      (Branch.appendFloors block block))

append8 : List ℚ → List ℚ
append8 block = Branch.appendFloors (append4 block) (append4 block)

sumAppend4 : ∀ block →
  Funding.sumFloors (append4 block)
  ≡ Funding.sumFloors block
    + Funding.sumFloors block
    + Funding.sumFloors block
    + Funding.sumFloors block
sumAppend4 block =
  trans
    (Branch.sumAppendFloors block
      (Branch.appendFloors block (Branch.appendFloors block block)))
    (trans
      (cong
        (Funding.sumFloors block +_)
        (Branch.sumAppendFloors block (Branch.appendFloors block block)))
      (trans
        (cong
          (λ tail → Funding.sumFloors block +
            (Funding.sumFloors block + tail))
          (Branch.sumAppendFloors block block))
        (solve (Funding.sumFloors block ∷ []))))

sumAppend8 : ∀ block →
  Funding.sumFloors (append8 block)
  ≡ Funding.sumFloors (append4 block) + Funding.sumFloors (append4 block)
sumAppend8 block = Branch.sumAppendFloors (append4 block) (append4 block)

quadrupleMultiplicity : Nat → Nat
quadrupleMultiplicity zero = 1
quadrupleMultiplicity (suc n) =
  let old = quadrupleMultiplicity n
  in old + old + old + old

octupleMultiplicity : Nat → Nat
octupleMultiplicity zero = 1
octupleMultiplicity (suc n) =
  let old = octupleMultiplicity n
      four = old + old + old + old
  in four + four

floorCountAppend4 : ∀ block →
  Branch.floorCount (append4 block)
  ≡ Branch.floorCount block + Branch.floorCount block
    + Branch.floorCount block + Branch.floorCount block
floorCountAppend4 block =
  trans
    (Branch.floorCountAppend block
      (Branch.appendFloors block (Branch.appendFloors block block)))
    (trans
      (cong
        (Branch.floorCount block +_)
        (Branch.floorCountAppend block (Branch.appendFloors block block)))
      (trans
        (cong
          (λ tail → Branch.floorCount block +
            (Branch.floorCount block + tail))
          (Branch.floorCountAppend block block))
        refl))

floorCountAppend8 : ∀ block →
  Branch.floorCount (append8 block)
  ≡ Branch.floorCount (append4 block) + Branch.floorCount (append4 block)
floorCountAppend8 block = Branch.floorCountAppend (append4 block) (append4 block)

quadraticComplexityBranchBlock : Nat → List ℚ
quadraticComplexityBranchBlock zero = 1ℚ ∷ []
quadraticComplexityBranchBlock (suc n) =
  append4 (Branch.scaleFloors quarter (quadraticComplexityBranchBlock n))

cubicComplexityBranchBlock : Nat → List ℚ
cubicComplexityBranchBlock zero = 1ℚ ∷ []
cubicComplexityBranchBlock (suc n) =
  append8 (Branch.scaleFloors eighth (cubicComplexityBranchBlock n))

quadraticBranchCountExact : ∀ n →
  Branch.floorCount (quadraticComplexityBranchBlock n)
  ≡ quadrupleMultiplicity n
quadraticBranchCountExact zero = refl
quadraticBranchCountExact (suc n)
  rewrite floorCountAppend4
            (Branch.scaleFloors quarter (quadraticComplexityBranchBlock n))
        | Branch.floorCountScale quarter (quadraticComplexityBranchBlock n)
        | quadraticBranchCountExact n = refl

cubicBranchCountExact : ∀ n →
  Branch.floorCount (cubicComplexityBranchBlock n)
  ≡ octupleMultiplicity n
cubicBranchCountExact zero = refl
cubicBranchCountExact (suc n)
  rewrite floorCountAppend8
            (Branch.scaleFloors eighth (cubicComplexityBranchBlock n))
        | floorCountAppend4
            (Branch.scaleFloors eighth (cubicComplexityBranchBlock n))
        | Branch.floorCountScale eighth (cubicComplexityBranchBlock n)
        | cubicBranchCountExact n = refl

quadraticBranchMassExact : ∀ n →
  Funding.sumFloors (quadraticComplexityBranchBlock n) ≡ 1ℚ
quadraticBranchMassExact zero = solve []
quadraticBranchMassExact (suc n) =
  let
    old = Funding.sumFloors (quadraticComplexityBranchBlock n)
    scaled = Branch.scaleFloors quarter (quadraticComplexityBranchBlock n)
    expand :
      Funding.sumFloors (quadraticComplexityBranchBlock (suc n))
      ≡ quarter * old + quarter * old + quarter * old + quarter * old
    expand =
      trans
        (sumAppend4 scaled)
        (cong
          (λ mass → mass + mass + mass + mass)
          (Branch.sumScaleFloors quarter (quadraticComplexityBranchBlock n)))
  in
  trans expand
    (trans
      (cong
        (λ mass → quarter * mass + quarter * mass
          + quarter * mass + quarter * mass)
        (quadraticBranchMassExact n))
      (solve []))

cubicBranchMassExact : ∀ n →
  Funding.sumFloors (cubicComplexityBranchBlock n) ≡ 1ℚ
cubicBranchMassExact zero = solve []
cubicBranchMassExact (suc n) =
  let
    old = Funding.sumFloors (cubicComplexityBranchBlock n)
    scaled = Branch.scaleFloors eighth (cubicComplexityBranchBlock n)
    fourMass = Funding.sumFloors (append4 scaled)
    expand8 :
      Funding.sumFloors (cubicComplexityBranchBlock (suc n))
      ≡ fourMass + fourMass
    expand8 = sumAppend8 scaled
    expand4 :
      fourMass
      ≡ eighth * old + eighth * old + eighth * old + eighth * old
    expand4 =
      trans
        (sumAppend4 scaled)
        (cong
          (λ mass → mass + mass + mass + mass)
          (Branch.sumScaleFloors eighth (cubicComplexityBranchBlock n)))
  in
  trans expand8
    (trans
      (cong₂ _+_ expand4 expand4)
      (trans
        (cong
          (λ mass →
            (eighth * mass + eighth * mass + eighth * mass + eighth * mass)
            + (eighth * mass + eighth * mass + eighth * mass + eighth * mass))
          (cubicBranchMassExact n))
        (solve [])))

round72N2ComplexityNeedsFourWayCriticalMultiplicity : Bool
round72N2ComplexityNeedsFourWayCriticalMultiplicity = true

round72N3ComplexityNeedsEightWayCriticalMultiplicity : Bool
round72N3ComplexityNeedsEightWayCriticalMultiplicity = true

round72PhysicalFourWayOrEightWayDescendantsConstructed : Bool
round72PhysicalFourWayOrEightWayDescendantsConstructed = false

round72N3ComplexityNeedsEightWayCriticalMultiplicityIsTrue :
  round72N3ComplexityNeedsEightWayCriticalMultiplicity ≡ true
round72N3ComplexityNeedsEightWayCriticalMultiplicityIsTrue = refl
