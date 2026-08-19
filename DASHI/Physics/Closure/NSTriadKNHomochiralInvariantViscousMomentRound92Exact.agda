module DASHI.Physics.Closure.NSTriadKNHomochiralInvariantViscousMomentRound92Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- Authors: Zhen Lei; Fang-Hua Lin; Yi Zhou.
-- Title: "Structure of Helicity and Global Solutions of Incompressible
-- Navier-Stokes Equation".
-- Archive for Rational Mechanics and Analysis 218 (2015), 1417--1437.
-- DOI: 10.1007/s00205-015-0884-8.
--
-- ROUND92 / INVARIANT ELIMINATION BEFORE MAJORIZATION
--
-- For one homochiral Euler/NS nonlinear triad, write p,q,r for the positive
-- mode magnitudes and Tp,Tq,Tr for the three modal nonlinear energy transfers.
-- The nonlinear term conserves both energy and helicity on the triad:
--
--     E = Tp + Tq + Tr = 0,
--     H = p Tp + q Tq + r Tr = 0.
--
-- Define the Laplacian-weighted transfer
--
--     W = p^2 Tp + q^2 Tq + r^2 Tr.
--
-- Exact ring elimination gives the stronger identity
--
--   W = (q-p)(r-p) Tp - q r E + (q+r) H.
--
-- Hence on the invariant surface,
--
--     W = (q-p)(r-p) Tp.
--
-- No division by q-r or any non-resonance hypothesis is required.  If p is
-- the lowest magnitude, the coefficient is nonnegative, so the sign of the
-- complete Laplacian-weighted three-leg transfer is the sign of the low-leg
-- transfer.  This is a concrete route around total-variation loss on the
-- homochiral sector.
--
-- This file proves the scalar invariant algebra.  The physical same-object
-- theorem still has to identify the literal Fourier helical triad transfers
-- with Tp,Tq,Tr and supply triadwise energy/helicity conservation there.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

record HomochiralTriadTransfer : Set where
  constructor homochiral-triad-transfer
  field
    p q r : ℚ
    transferP transferQ transferR : ℚ

open HomochiralTriadTransfer public

energyDefect : HomochiralTriadTransfer → ℚ
energyDefect triad =
  transferP triad + transferQ triad + transferR triad

helicityDefect : HomochiralTriadTransfer → ℚ
helicityDefect triad =
  p triad * transferP triad
  + q triad * transferQ triad
  + r triad * transferR triad

laplacianWeightedTransfer : HomochiralTriadTransfer → ℚ
laplacianWeightedTransfer triad =
  p triad * p triad * transferP triad
  + q triad * q triad * transferQ triad
  + r triad * r triad * transferR triad

lowLegCoefficient : HomochiralTriadTransfer → ℚ
lowLegCoefficient triad =
  (q triad - p triad) * (r triad - p triad)

viscousMomentInvariantDecomposition :
  (triad : HomochiralTriadTransfer) →
  laplacianWeightedTransfer triad
  ≡ lowLegCoefficient triad * transferP triad
      + (- (q triad * r triad)) * energyDefect triad
      + (q triad + r triad) * helicityDefect triad
viscousMomentInvariantDecomposition triad =
  solve
    ( p triad ∷ q triad ∷ r triad
    ∷ transferP triad ∷ transferQ triad ∷ transferR triad ∷ [])

record ConservedHomochiralTriadTransfer : Set where
  constructor conserved-homochiral-triad-transfer
  field
    triad : HomochiralTriadTransfer
    energyConserved : energyDefect triad ≡ 0ℚ
    helicityConserved : helicityDefect triad ≡ 0ℚ

open ConservedHomochiralTriadTransfer public

viscousMomentCollapsesToLowLeg :
  (data : ConservedHomochiralTriadTransfer) →
  laplacianWeightedTransfer (triad data)
    ≡ lowLegCoefficient (triad data) * transferP (triad data)
viscousMomentCollapsesToLowLeg data
  rewrite viscousMomentInvariantDecomposition (triad data)
        | energyConserved data
        | helicityConserved data =
  solve
    ( lowLegCoefficient (triad data)
    ∷ transferP (triad data) ∷ [])

record OrderedLowLegHomochiralTransfer : Set where
  constructor ordered-low-leg-homochiral-transfer
  field
    conserved : ConservedHomochiralTriadTransfer
    pNonnegative : 0ℚ ≤ p (triad conserved)
    pBelowQ : p (triad conserved) ≤ q (triad conserved)
    pBelowR : p (triad conserved) ≤ r (triad conserved)

open OrderedLowLegHomochiralTransfer public

differenceNonnegative : ∀ {a b : ℚ} → a ≤ b → 0ℚ ≤ b - a
differenceNonnegative {a} {b} a≤b =
  let
    shifted = ℚP.+-monoʳ-≤ (- a) a≤b
    leftMeaning : a + (- a) ≡ 0ℚ
    leftMeaning = solve (a ∷ [])
    rightMeaning : b + (- a) ≡ b - a
    rightMeaning = solve (a ∷ b ∷ [])
  in
  subst
    (λ left → left ≤ b - a)
    leftMeaning
    (subst
      (λ right → a + (- a) ≤ right)
      rightMeaning shifted)

lowLegCoefficientNonnegative :
  (data : OrderedLowLegHomochiralTransfer) →
  0ℚ ≤ lowLegCoefficient (triad (conserved data))
lowLegCoefficientNonnegative data =
  let
    qGapNN = differenceNonnegative (pBelowQ data)
    rGapNN = differenceNonnegative (pBelowR data)
    instance
      qGapNNI = nonNegative qGapNN
      rGapNNI = nonNegative rGapNN
      productNNI = ℚP.nonNeg*nonNeg⇒nonNeg
        (q (triad (conserved data)) - p (triad (conserved data)))
        (r (triad (conserved data)) - p (triad (conserved data)))
  in
  ℚP.nonNegative⁻¹ (lowLegCoefficient (triad (conserved data)))

nonnegativeLowLegTransferGivesNonnegativeViscousMoment :
  (data : OrderedLowLegHomochiralTransfer) →
  0ℚ ≤ transferP (triad (conserved data)) →
  0ℚ ≤ laplacianWeightedTransfer (triad (conserved data))
nonnegativeLowLegTransferGivesNonnegativeViscousMoment data transferNN =
  let
    coefficientNN = lowLegCoefficientNonnegative data
    productNN :
      0ℚ ≤ lowLegCoefficient (triad (conserved data))
          * transferP (triad (conserved data))
    productNN =
      let instance
        coefficientNNI = nonNegative coefficientNN
        transferNNI = nonNegative transferNN
        productNNI = ℚP.nonNeg*nonNeg⇒nonNeg
          (lowLegCoefficient (triad (conserved data)))
          (transferP (triad (conserved data)))
      in
      ℚP.nonNegative⁻¹
        (lowLegCoefficient (triad (conserved data))
          * transferP (triad (conserved data)))
  in
  subst
    (0ℚ ≤_)
    (symEq (viscousMomentCollapsesToLowLeg (conserved data)))
    productNN
  where
  symEq : ∀ {a b : ℚ} → a ≡ b → b ≡ a
  symEq refl = refl

round92HomochiralEnergyHelicityEliminatesThreeLegViscousMoment : Bool
round92HomochiralEnergyHelicityEliminatesThreeLegViscousMoment = true

round92HomochiralLowLegSignControlsViscousMoment : Bool
round92HomochiralLowLegSignControlsViscousMoment = true

round92LiteralFourierTriadEnergyHelicityInstantiationConstructed : Bool
round92LiteralFourierTriadEnergyHelicityInstantiationConstructed = false

round92HomochiralEnergyHelicityEliminatesThreeLegViscousMomentIsTrue :
  round92HomochiralEnergyHelicityEliminatesThreeLegViscousMoment ≡ true
round92HomochiralEnergyHelicityEliminatesThreeLegViscousMomentIsTrue = refl

round92HomochiralLowLegSignControlsViscousMomentIsTrue :
  round92HomochiralLowLegSignControlsViscousMoment ≡ true
round92HomochiralLowLegSignControlsViscousMomentIsTrue = refl
