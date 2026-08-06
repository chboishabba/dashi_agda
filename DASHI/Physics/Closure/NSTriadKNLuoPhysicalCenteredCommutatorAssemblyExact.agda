module DASHI.Physics.Closure.NSTriadKNLuoPhysicalCenteredCommutatorAssemblyExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- DOI: 10.1007/BF02099744.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphaël Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Assemble the centered paired-difference commutator estimate after the exact
-- algebraic cancellation has been proved.  Each pair contributes
--
--   mass(y) * (second-difference branch + derivative-variation branch).
--
-- A finite induction proves that uniform branch envelopes factor through the
-- kernel second moment.  A second induction proves the physical dyadic scaling
--
--   M_2(K_q) = 2^{-2q} M_2(K)
--
-- represented exactly by quarterPower q.  Thus the complete C1--C5 summation
-- and scale bookkeeping is checked rather than asserted by a final receipt.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

oneQuarter : ℚ
oneQuarter = Int.+ 1 / 4

quarterPower : Nat → ℚ
quarterPower zero = 1ℚ
quarterPower (suc shell) = oneQuarter * quarterPower shell

oneQuarterNonnegative : 0ℚ ≤ oneQuarter
oneQuarterNonnegative = ℚₚ.nonNegative⁻¹ oneQuarter

quarterPowerNonnegative :
  (shell : Nat) → 0ℚ ≤ quarterPower shell
quarterPowerNonnegative zero = ℚₚ.0≤1
quarterPowerNonnegative (suc shell) =
  let
    instance
      quarterNN = nonNegative oneQuarterNonnegative
      tailNN = nonNegative (quarterPowerNonnegative shell)
      productNN =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          oneQuarter
          (quarterPower shell)
  in
  ℚₚ.nonNegative⁻¹ (oneQuarter * quarterPower shell)

record CenteredPairCell
    (branchOneEnvelope branchTwoEnvelope : ℚ) : Set where
  constructor centered-pair-cell
  field
    secondMomentMass : ℚ
    secondDifferenceBranch : ℚ
    derivativeVariationBranch : ℚ

    secondMomentMassNonnegative :
      0ℚ ≤ secondMomentMass
    secondDifferenceBranchNonnegative :
      0ℚ ≤ secondDifferenceBranch
    derivativeVariationBranchNonnegative :
      0ℚ ≤ derivativeVariationBranch

    secondDifferenceBound :
      secondDifferenceBranch ≤ branchOneEnvelope
    derivativeVariationBound :
      derivativeVariationBranch ≤ branchTwoEnvelope

open CenteredPairCell public

kernelSecondMoment :
  (branchOne branchTwo : ℚ) →
  List (CenteredPairCell branchOne branchTwo) →
  ℚ
kernelSecondMoment branchOne branchTwo [] = 0ℚ
kernelSecondMoment branchOne branchTwo (cell ∷ cells) =
  secondMomentMass cell
  + kernelSecondMoment branchOne branchTwo cells

centeredCommutatorEnvelope :
  (branchOne branchTwo : ℚ) →
  List (CenteredPairCell branchOne branchTwo) →
  ℚ
centeredCommutatorEnvelope branchOne branchTwo [] = 0ℚ
centeredCommutatorEnvelope branchOne branchTwo (cell ∷ cells) =
  secondMomentMass cell
    * (secondDifferenceBranch cell + derivativeVariationBranch cell)
  + centeredCommutatorEnvelope branchOne branchTwo cells

branchEnvelopeNonnegative :
  ∀ {branchOne branchTwo}
    (cell : CenteredPairCell branchOne branchTwo) →
  0ℚ ≤ branchOne + branchTwo
branchEnvelopeNonnegative cell =
  L2.addNonnegative
    (ℚₚ.≤-trans
      (secondDifferenceBranchNonnegative cell)
      (secondDifferenceBound cell))
    (ℚₚ.≤-trans
      (derivativeVariationBranchNonnegative cell)
      (derivativeVariationBound cell))

localCenteredPairBound :
  ∀ {branchOne branchTwo}
    (cell : CenteredPairCell branchOne branchTwo) →
  secondMomentMass cell
    * (secondDifferenceBranch cell + derivativeVariationBranch cell)
  ≤ secondMomentMass cell * (branchOne + branchTwo)
localCenteredPairBound cell =
  L2.nonnegativeProductMonotone
    (secondMomentMassNonnegative cell)
    (L2.addNonnegative
      (secondDifferenceBranchNonnegative cell)
      (derivativeVariationBranchNonnegative cell))
    (secondMomentMassNonnegative cell)
    (branchEnvelopeNonnegative cell)
    ℚₚ.≤-refl
    (ℚₚ.+-mono-≤
      (secondDifferenceBound cell)
      (derivativeVariationBound cell))

centeredCommutatorMomentBound :
  (branchOne branchTwo : ℚ) →
  (cells : List (CenteredPairCell branchOne branchTwo)) →
  centeredCommutatorEnvelope branchOne branchTwo cells
  ≤ kernelSecondMoment branchOne branchTwo cells
    * (branchOne + branchTwo)
centeredCommutatorMomentBound branchOne branchTwo [] = ℚₚ.≤-refl
centeredCommutatorMomentBound
  branchOne branchTwo (cell ∷ cells) =
  let
    local = localCenteredPairBound cell
    tail = centeredCommutatorMomentBound branchOne branchTwo cells
    summed = ℚₚ.+-mono-≤ local tail

    factorized :
      secondMomentMass cell * (branchOne + branchTwo)
      + kernelSecondMoment branchOne branchTwo cells
        * (branchOne + branchTwo)
      ≡
      (secondMomentMass cell
        + kernelSecondMoment branchOne branchTwo cells)
      * (branchOne + branchTwo)
    factorized =
      solve
        ( secondMomentMass cell
        ∷ kernelSecondMoment branchOne branchTwo cells
        ∷ branchOne
        ∷ branchTwo
        ∷ [])
  in
  subst
    (λ upper →
      secondMomentMass cell
        * (secondDifferenceBranch cell + derivativeVariationBranch cell)
      + centeredCommutatorEnvelope branchOne branchTwo cells
      ≤ upper)
    factorized
    summed

scaleCenteredPairCell :
  ∀ {branchOne branchTwo} →
  (shell : Nat) →
  CenteredPairCell branchOne branchTwo →
  CenteredPairCell branchOne branchTwo
scaleCenteredPairCell {branchOne} {branchTwo} shell cell =
  centered-pair-cell
    (quarterPower shell * secondMomentMass cell)
    (secondDifferenceBranch cell)
    (derivativeVariationBranch cell)
    scaledMassNonnegative
    (secondDifferenceBranchNonnegative cell)
    (derivativeVariationBranchNonnegative cell)
    (secondDifferenceBound cell)
    (derivativeVariationBound cell)
  where
    scaledMassNonnegative :
      0ℚ ≤ quarterPower shell * secondMomentMass cell
    scaledMassNonnegative =
      let
        instance
          scaleNN = nonNegative (quarterPowerNonnegative shell)
          massNN = nonNegative (secondMomentMassNonnegative cell)
          productNN =
            ℚₚ.nonNeg*nonNeg⇒nonNeg
              (quarterPower shell)
              (secondMomentMass cell)
      in
      ℚₚ.nonNegative⁻¹
        (quarterPower shell * secondMomentMass cell)

scaleCenteredPairCells :
  ∀ {branchOne branchTwo} →
  (shell : Nat) →
  List (CenteredPairCell branchOne branchTwo) →
  List (CenteredPairCell branchOne branchTwo)
scaleCenteredPairCells shell [] = []
scaleCenteredPairCells shell (cell ∷ cells) =
  scaleCenteredPairCell shell cell
  ∷ scaleCenteredPairCells shell cells

kernelSecondMomentScaling :
  ∀ {branchOne branchTwo}
    (shell : Nat)
    (cells : List (CenteredPairCell branchOne branchTwo)) →
  kernelSecondMoment branchOne branchTwo
    (scaleCenteredPairCells shell cells)
  ≡ quarterPower shell
    * kernelSecondMoment branchOne branchTwo cells
kernelSecondMomentScaling shell [] =
  solve (quarterPower shell ∷ [])
kernelSecondMomentScaling
  {branchOne} {branchTwo} shell (cell ∷ cells)
  rewrite kernelSecondMomentScaling shell cells =
  solve
    ( quarterPower shell
    ∷ secondMomentMass cell
    ∷ kernelSecondMoment branchOne branchTwo cells
    ∷ [])

physicalCenteredCommutatorBound :
  (shell : Nat) →
  (branchOne branchTwo : ℚ) →
  (cells : List (CenteredPairCell branchOne branchTwo)) →
  centeredCommutatorEnvelope branchOne branchTwo
    (scaleCenteredPairCells shell cells)
  ≤
  (quarterPower shell
    * kernelSecondMoment branchOne branchTwo cells)
  * (branchOne + branchTwo)
physicalCenteredCommutatorBound shell branchOne branchTwo cells =
  subst
    (λ moment →
      centeredCommutatorEnvelope branchOne branchTwo
        (scaleCenteredPairCells shell cells)
      ≤ moment * (branchOne + branchTwo))
    (kernelSecondMomentScaling shell cells)
    (centeredCommutatorMomentBound
      branchOne branchTwo
      (scaleCenteredPairCells shell cells))
