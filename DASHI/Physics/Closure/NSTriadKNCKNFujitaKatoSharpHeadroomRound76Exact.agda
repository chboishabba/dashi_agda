module DASHI.Physics.Closure.NSTriadKNCKNFujitaKatoSharpHeadroomRound76Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Luis Caffarelli; Robert Kohn; Louis Nirenberg.
-- Title: "Partial regularity of suitable weak solutions of the Navier-Stokes
-- equations".
-- DOI: 10.1002/cpa.3160350604.
--
-- Authors: Hiroshi Fujita; Tosio Kato.
-- Title: "On the Navier-Stokes initial value problem. I".
-- DOI: 10.1007/BF00276188.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- ROUND76 / EXACT HH-BAD HEADROOM INTERFACE
--
-- CKN epsilon-regularity and Fujita--Kato critical-space smallness are useful
-- precedents for the LOGICAL SHAPE "physical scale-invariant quantity below a
-- threshold -> regularity/continuation".  They do not provide the numerical
-- constant required by this repository's different localized triadic gate.
--
-- The existing Round62 sharp scalar gate has the irreducible form
--
--   eta_HHb + eta_soft + 1/16 < 1,
--
-- while Round63/68 prove
--
--   eta_HHb = 2 Lambda_bad,
--   Lambda_bad = C_* K_bad
--
-- on the same physical selected-profile/multiplicity object.
--
-- This file removes the last bookkeeping ambiguity around "available
-- headroom".  For any already-established soft tax S, define exactly
--
--   H_available = 1 - (S + 1/16).
--
-- Then the ONLY hard-HH inequality needed by the final scalar gate is
--
--   2 Lambda_bad < H_available.
--
-- The theorem below compiles that inequality directly to the sharp gate.
-- CKN/Fujita--Kato remain provenance/calibration only; no external epsilon is
-- substituted for the repository's physical Lambda_bad calculation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _-_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst₂)

import DASHI.Physics.Closure.NSTriadKNHHBadCapacityProductRound63Exact as Product
import DASHI.Physics.Closure.NSTriadKNHHBadPhysicalCapacityProductWeldRound68Exact as Physical
import DASHI.Physics.Closure.NSTriadKNJointGlobalFeasibilityRound54Exact as Existing

availableHHBadHeadroom : ℚ → ℚ
availableHHBadHeadroom softTax =
  1ℚ - (softTax + Existing.oneSixteenth)

sharpGateTotalFromCapacityProduct : ℚ → ℚ → ℚ
sharpGateTotalFromCapacityProduct lambdaBad softTax =
  Product.hhBadTaxFromCapacityProduct lambdaBad
  + softTax + Existing.oneSixteenth

hhBadTaxBelowAvailableHeadroomClosesSharpGate :
  ∀ lambdaBad softTax →
  Product.hhBadTaxFromCapacityProduct lambdaBad
    < availableHHBadHeadroom softTax →
  sharpGateTotalFromCapacityProduct lambdaBad softTax < 1ℚ
hhBadTaxBelowAvailableHeadroomClosesSharpGate lambdaBad softTax hardBelow =
  let
    hard = Product.hhBadTaxFromCapacityProduct lambdaBad
    rest = softTax + Existing.oneSixteenth

    shifted : hard + rest < availableHHBadHeadroom softTax + rest
    shifted = ℚP.+-monoʳ-< rest hardBelow

    leftMeaning :
      hard + rest ≡ sharpGateTotalFromCapacityProduct lambdaBad softTax
    leftMeaning = solve (hard ∷ softTax ∷ Existing.oneSixteenth ∷ [])

    rightMeaning :
      availableHHBadHeadroom softTax + rest ≡ 1ℚ
    rightMeaning = solve (softTax ∷ Existing.oneSixteenth ∷ [])
  in
  subst₂ _<_ leftMeaning rightMeaning shifted

physicalBadCapacityProductBelowAvailableHeadroomClosesSharpGate :
  ∀ {environment effectiveViscosity}
    (input : Physical.PhysicalSelectedProfileMultiplicityInput
      environment effectiveViscosity)
    (softTax : ℚ) →
  Product.hhBadTaxFromCapacityProduct
      (Physical.physicalBadCapacityProduct input)
    < availableHHBadHeadroom softTax →
  sharpGateTotalFromCapacityProduct
      (Physical.physicalBadCapacityProduct input) softTax
    < 1ℚ
physicalBadCapacityProductBelowAvailableHeadroomClosesSharpGate
    input softTax headroom =
  hhBadTaxBelowAvailableHeadroomClosesSharpGate
    (Physical.physicalBadCapacityProduct input) softTax headroom

round76HHBadTargetIsExactlyRemainingSharpGateHeadroom : Bool
round76HHBadTargetIsExactlyRemainingSharpGateHeadroom = true

round76CKNConstantImportedAsPhysicalHHBadConstant : Bool
round76CKNConstantImportedAsPhysicalHHBadConstant = false

round76FujitaKatoConstantImportedAsPhysicalSoftConstant : Bool
round76FujitaKatoConstantImportedAsPhysicalSoftConstant = false

round76HHBadTargetIsExactlyRemainingSharpGateHeadroomIsTrue :
  round76HHBadTargetIsExactlyRemainingSharpGateHeadroom ≡ true
round76HHBadTargetIsExactlyRemainingSharpGateHeadroomIsTrue = refl
