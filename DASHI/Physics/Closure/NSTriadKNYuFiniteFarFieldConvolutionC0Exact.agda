module DASHI.Physics.Closure.NSTriadKNYuFiniteFarFieldConvolutionC0Exact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier--Stokes Equations".
-- arXiv DOI: 10.48550/arXiv.2606.27560.
--
-- PURPOSE
-- Prove the finite-Galerkin version of the standard l1*c0 -> c0 fact for the
-- explicit annular kernel h_m=2^{-(m+1)}. Every finite convolution prefix has
-- total weight at most one, uniformly in the annular cutoff. Therefore the
-- same c0 cutoff for Q controls every finite annular prefix.
--
-- This is the exact statement needed before Galerkin/annular limits are
-- taken. No exterior compactness is inferred from the energy inequality.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_+_; z≤n; s≤s)
import Data.Nat.Base as ℕ using (_≤_)
import Data.Nat.Properties as ℕₚ
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _+_; _*_; _≤_; _<_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNLuoFiniteHighLowDerivativeRatioExact as HL
import DASHI.Physics.Closure.NSTriadKNLuoTerminalInteractionDepletionTransferExact as Limit

half : ℚ
half = Int.+ 1 / 2

annularWeight : Nat → ℚ
annularWeight offset = half * Geo.pow half offset

annularWeightNonnegative :
  (offset : Nat) → 0ℚ ≤ annularWeight offset
annularWeightNonnegative offset =
  let
    instance
      halfNN = nonNegative HL.halfNonnegative
      powerNN =
        nonNegative (Geo.powNonnegative half offset HL.halfNonnegative)
      productNN = ℚₚ.nonNeg*nonNeg⇒nonNeg half (Geo.pow half offset)
  in
  ℚₚ.nonNegative⁻¹ (annularWeight offset)

annularWeightPrefix : Nat → ℚ
annularWeightPrefix cutoff = half * Geo.partialSum half cutoff

annularWeightPrefixBound :
  (cutoff : Nat) → annularWeightPrefix cutoff ≤ 1ℚ
annularWeightPrefixBound cutoff =
  let
    scaled :
      half * Geo.partialSum half cutoff ≤ half * HL.two
    scaled =
      let instance halfNN = nonNegative HL.halfNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg half (HL.unshiftedHalfPrefixBound cutoff)

    endpoint : half * HL.two ≡ 1ℚ
    endpoint = solve []
  in
  subst (λ upper → annularWeightPrefix cutoff ≤ upper) endpoint scaled

selfBelowSuccessor : (value : Nat) → value ℕ.≤ suc value
selfBelowSuccessor zero = z≤n
selfBelowSuccessor (suc value) = s≤s (selfBelowSuccessor value)

leftBelowAddition : (left right : Nat) → left ℕ.≤ left + right
leftBelowAddition zero right = z≤n
leftBelowAddition (suc left) right = s≤s (leftBelowAddition left right)

finiteAnnularConvolution :
  (Q : Nat → ℚ) → Nat → Nat → ℚ
finiteAnnularConvolution Q shell zero =
  annularWeight zero * Q shell
finiteAnnularConvolution Q shell (suc cutoff) =
  finiteAnnularConvolution Q shell cutoff
  + annularWeight (suc cutoff) * Q (shell + suc cutoff)

allShiftedBelow :
  (Q : Nat → ℚ) → Nat → Nat → ℚ → Set
allShiftedBelow Q shell cutoff epsilon =
  (offset : Nat) →
  offset ℕ.≤ cutoff →
  Q (shell + offset) ≤ epsilon

finiteConvolutionBelowWeightedEpsilon :
  (Q : Nat → ℚ)
  (shell cutoff : Nat)
  (epsilon : ℚ) →
  0ℚ ≤ epsilon →
  allShiftedBelow Q shell cutoff epsilon →
  finiteAnnularConvolution Q shell cutoff
  ≤ epsilon * annularWeightPrefix cutoff
finiteConvolutionBelowWeightedEpsilon
  Q shell zero epsilon epsilonNN shifted =
  let
    weightStep :
      annularWeight zero * Q (shell + zero)
      ≤ annularWeight zero * epsilon
    weightStep =
      let instance weightNN = nonNegative (annularWeightNonnegative zero)
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (annularWeight zero)
        (shifted zero ℕₚ.≤-refl)

    endpoint :
      annularWeight zero * epsilon
      ≡ epsilon * annularWeightPrefix zero
    endpoint = solve (epsilon ∷ [])
  in
  subst
    (λ upper → finiteAnnularConvolution Q shell zero ≤ upper)
    endpoint
    weightStep
finiteConvolutionBelowWeightedEpsilon
  Q shell (suc cutoff) epsilon epsilonNN shifted =
  let
    previousShifted : allShiftedBelow Q shell cutoff epsilon
    previousShifted offset offset≤cutoff =
      shifted offset
        (ℕₚ.≤-trans offset≤cutoff (selfBelowSuccessor cutoff))

    previous =
      finiteConvolutionBelowWeightedEpsilon
        Q shell cutoff epsilon epsilonNN previousShifted

    newWeight :
      annularWeight (suc cutoff) * Q (shell + suc cutoff)
      ≤ annularWeight (suc cutoff) * epsilon
    newWeight =
      let
        instance weightNN =
          nonNegative (annularWeightNonnegative (suc cutoff))
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (annularWeight (suc cutoff))
        (shifted (suc cutoff) ℕₚ.≤-refl)

    summed = ℚₚ.+-mono-≤ previous newWeight

    endpoint :
      epsilon * annularWeightPrefix cutoff
        + annularWeight (suc cutoff) * epsilon
      ≡ epsilon * annularWeightPrefix (suc cutoff)
    endpoint =
      solve
        ( epsilon
        ∷ Geo.partialSum half cutoff
        ∷ Geo.pow half (suc cutoff)
        ∷ [])
  in
  subst
    (λ upper →
      finiteAnnularConvolution Q shell (suc cutoff) ≤ upper)
    endpoint
    summed

finiteAnnularConvolutionBelowEpsilon :
  (Q : Nat → ℚ)
  (shell cutoff : Nat)
  (epsilon : ℚ) →
  0ℚ ≤ epsilon →
  allShiftedBelow Q shell cutoff epsilon →
  finiteAnnularConvolution Q shell cutoff ≤ epsilon
finiteAnnularConvolutionBelowEpsilon
  Q shell cutoff epsilon epsilonNN shifted =
  let
    weighted =
      finiteConvolutionBelowWeightedEpsilon
        Q shell cutoff epsilon epsilonNN shifted

    prefixStep :
      epsilon * annularWeightPrefix cutoff ≤ epsilon * 1ℚ
    prefixStep =
      let instance epsilonNNI = nonNegative epsilonNN
      in
      ℚₚ.*-monoˡ-≤-nonNeg epsilon (annularWeightPrefixBound cutoff)

    endpoint : epsilon * 1ℚ ≡ epsilon
    endpoint = solve (epsilon ∷ [])
  in
  ℚₚ.≤-trans
    weighted
    (subst
      (λ upper → epsilon * annularWeightPrefix cutoff ≤ upper)
      endpoint
      prefixStep)

finiteAnnularConvolutionVanishing :
  (Q : Nat → ℚ) →
  ((shell : Nat) → 0ℚ ≤ Q shell) →
  Limit.TendsToZero Q →
  (cutoff : Nat) →
  Limit.TendsToZero
    (λ shell → finiteAnnularConvolution Q shell cutoff)
finiteAnnularConvolutionVanishing Q QNN Qvanishing cutoff =
  Limit.tends-to-zero
    (λ epsilon epsilonPositive →
      let
        sourceTail =
          Limit.eventuallySmall Qvanishing epsilon epsilonPositive
        epsilonNN : 0ℚ ≤ epsilon
        epsilonNN = ℚₚ.<⇒≤ epsilonPositive
      in
      Limit.eventually-below
        (Limit.cutoff sourceTail)
        (λ shell cutoff≤shell →
          finiteAnnularConvolutionBelowEpsilon
            Q shell cutoff epsilon epsilonNN
            (λ offset offset≤cutoff →
              Limit.tailBound sourceTail
                (shell + offset)
                (ℕₚ.≤-trans
                  cutoff≤shell
                  (leftBelowAddition shell offset)))))
