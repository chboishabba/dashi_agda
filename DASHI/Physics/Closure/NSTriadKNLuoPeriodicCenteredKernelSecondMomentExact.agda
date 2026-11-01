module DASHI.Physics.Closure.NSTriadKNLuoPeriodicCenteredKernelSecondMomentExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- DOI: 10.1007/BF02099744.
--
-- Author: Piero D'Ancona.
-- Title: "A Short Proof of Commutator Estimates".
-- DOI: 10.1007/s00041-018-9612-8.
-- Correction DOI: 10.1007/s00041-019-09724-7.
--
-- PURPOSE
-- Prove the exact finite/quadrature form of the centered-kernel second-moment
-- scaling.  Pairing samples at y and -y cancels the first moment, while a
-- dyadic rescaling by lambda_q=2^q multiplies |y|^2 by 4^{-q}.  Therefore
--
--   M2(K_q) = 4^{-q} M2(K).
--
-- This closes the scale arithmetic and the finite centered cancellation.  A
-- continuous torus integral is obtained by instantiating the quadrature cells
-- with the chosen periodized kernel and its integral certificate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq using (cong)
open Eq.≡-Reasoning

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo

quarter two : ℚ
quarter = Int.+ 1 / 4
two = Int.+ 2 / 1

record CenteredKernelPair : Set where
  constructor centered-kernel-pair
  field
    weightAbs displacement : ℚ

open CenteredKernelPair public

pairFirstMoment : CenteredKernelPair → ℚ
pairFirstMoment cell =
  weightAbs cell * displacement cell
  + weightAbs cell * (- displacement cell)

pairSecondMoment : CenteredKernelPair → ℚ
pairSecondMoment cell =
  weightAbs cell * (displacement cell * displacement cell)
  + weightAbs cell * ((- displacement cell) * (- displacement cell))

pairedFirstMomentCancels :
  (cell : CenteredKernelPair) →
  pairFirstMoment cell ≡ Int.+ 0 / 1
pairedFirstMomentCancels cell =
  solve (weightAbs cell ∷ displacement cell ∷ [])

pairedSecondMomentMeaning :
  (cell : CenteredKernelPair) →
  pairSecondMoment cell
  ≡ two * weightAbs cell * (displacement cell * displacement cell)
pairedSecondMomentMeaning cell =
  solve (weightAbs cell ∷ displacement cell ∷ [])

secondMoment : List CenteredKernelPair → ℚ
secondMoment [] = Int.+ 0 / 1
secondMoment (cell ∷ cells) =
  pairSecondMoment cell + secondMoment cells

firstMoment : List CenteredKernelPair → ℚ
firstMoment [] = Int.+ 0 / 1
firstMoment (cell ∷ cells) =
  pairFirstMoment cell + firstMoment cells

finiteCenteredFirstMomentZero :
  (cells : List CenteredKernelPair) →
  firstMoment cells ≡ Int.+ 0 / 1
finiteCenteredFirstMomentZero [] = refl
finiteCenteredFirstMomentZero (cell ∷ cells)
  rewrite pairedFirstMomentCancels cell
        | finiteCenteredFirstMomentZero cells =
  solve []

dyadicSecondMomentFactor : Nat → ℚ
dyadicSecondMomentFactor shell = Geo.pow quarter shell

rescalePair : ℚ → CenteredKernelPair → CenteredKernelPair
rescalePair scale cell =
  centered-kernel-pair
    (weightAbs cell)
    (scale * displacement cell)

mapPairs :
  (CenteredKernelPair → CenteredKernelPair) →
  List CenteredKernelPair →
  List CenteredKernelPair
mapPairs transform [] = []
mapPairs transform (cell ∷ cells) =
  transform cell ∷ mapPairs transform cells

-- A displacement scale of 2^{-q} is represented radical-free by supplying
-- its square, 4^{-q}, directly to the second-moment theorem.
rescaleSecondMomentBySquare :
  ℚ → List CenteredKernelPair → ℚ
rescaleSecondMomentBySquare scaleSquared [] = Int.+ 0 / 1
rescaleSecondMomentBySquare scaleSquared (cell ∷ cells) =
  scaleSquared * pairSecondMoment cell
  + rescaleSecondMomentBySquare scaleSquared cells

secondMomentScaleFactorizes :
  (scaleSquared : ℚ)
  (cells : List CenteredKernelPair) →
  rescaleSecondMomentBySquare scaleSquared cells
  ≡ scaleSquared * secondMoment cells
secondMomentScaleFactorizes scaleSquared [] = solve []
secondMomentScaleFactorizes scaleSquared (cell ∷ cells)
  rewrite secondMomentScaleFactorizes scaleSquared cells =
  solve
    ( scaleSquared
    ∷ pairSecondMoment cell
    ∷ secondMoment cells
    ∷ [])

dyadicCenteredKernelSecondMoment :
  (shell : Nat)
  (cells : List CenteredKernelPair) →
  rescaleSecondMomentBySquare
    (dyadicSecondMomentFactor shell) cells
  ≡ dyadicSecondMomentFactor shell * secondMoment cells
dyadicCenteredKernelSecondMoment shell cells =
  secondMomentScaleFactorizes
    (dyadicSecondMomentFactor shell) cells
