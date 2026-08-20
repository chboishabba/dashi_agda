module DASHI.Foundations.BishopMachinPiArchimedesWindowExact where

------------------------------------------------------------------------
-- UPSTREAM ARISTOTLE SOURCE / ATTRIBUTION
--
-- Aristotle (Harmonic), editor of the user-supplied Lean project.
-- Source module:
--   RequestProject.ArchimedesNinetySix
--   SHA-256 b04468675150478726d53b966886de449b75f915b5210e5676d2db16c833aaf7
--
-- The upstream README requests @Aristotle-Harmonic attribution and the commit
-- trailer
--   Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
--
-- PRIMARY / HISTORICAL SOURCES
--
-- Archimedes, "Measurement of a Circle", Proposition 3: the classical bounds
--   223/71 < pi < 22/7.
-- Ancient source; no DOI exists.
--
-- Errett Bishop and Douglas Bridges,
-- "Constructive Analysis", Springer, 1985.
-- DOI: 10.1007/978-3-642-61667-9.
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant", 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Prove the headline Archimedean numerical enclosure for the ACTUAL convergent
-- Bishop Machin real, without assuming that this real has already been
-- identified with the trigonometric/geometric pi.
--
-- The old lower certificate x-x^3/3 was only strong enough for 3 < pi_M.
-- The next valid alternating lower partial gives
--
--   S3(x) = x - x^3/3 + x^5/5 - x^7/7,
--
-- and at x=1/5:
--
--   16*S3(1/5) - 4/239
--     = 223/71 + 20785283/27839765625
--     > 223/71.
--
-- Together with the already-proved Bishop Machin upper bound pi_M < 22/7,
-- this yields
--
--   223/71 < bishopMachinPi < 22/7.
--
-- This imports the source's strongest numerical pi window while preserving the
-- semantic boundary: polygon/trigonometric identification remains a separate
-- theorem and is not smuggled into the proof.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_; nonNeg)
open import Data.Rational.Unnormalised as ℚ using
  (ℚᵘ; 0ℚᵘ; _/_; _+_; _<_; _≤_)
import Data.Rational.Unnormalised.Properties as ℚP

import Real as Bishop
import RealProperties as BishopP

import DASHI.Foundations.BishopMachinArctanConstructionExact as Atan
import DASHI.Foundations.BishopMachinPiRationalWindowExact as Window
import DASHI.Foundations.BishopArctanSeptimicLowerExact as Septimic
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpCoefficientExact as Order
open import DASHI.Physics.YangMills.CompactLieProofLevel

archimedesLower archimedesMargin archimedesLowerRational : ℚᵘ
archimedesLower = + 223 / 71
archimedesMargin = + 20785283 / 27839765625
archimedesLowerRational = archimedesLower ℚ.+ archimedesMargin

embed : ℚᵘ → Bishop.ℝ
embed = Bishop._⋆

machinArchimedesLowerCandidate : Bishop.ℝ
machinArchimedesLowerCandidate =
  Bishop._-_
    (Bishop._*_
      (embed Atan.sixteen)
      (Septimic.atanSeptimic Atan.bishopOneFifth))
    (Bishop._*_
      (embed Atan.four)
      Atan.bishopOneTwoHundredThirtyNinth)

machinArchimedesLowerCandidateSound :
  Bishop._≤_ machinArchimedesLowerCandidate Atan.bishopMachinPi
machinArchimedesLowerCandidateSound =
  let
    scaledA = BishopP.*-monoˡ-≤-nonNeg
      (Septimic.atanSeptimicLower Window.oneFifthPoint)
      Window.sixteenNN
    scaledB = BishopP.*-monoˡ-≤-nonNeg
      (Window.atanUpperByValue Window.oneTwoHundredThirtyNinthPoint)
      Window.fourNN
    negScaledB = BishopP.neg-mono-≤ scaledB
  in
  BishopP.+-mono-≤ scaledA negScaledB

machinArchimedesLowerCandidateIsRational :
  Bishop._≃_
    machinArchimedesLowerCandidate
    (embed archimedesLowerRational)
machinArchimedesLowerCandidateIsRational =
  let open BishopP.ℝ-Solver
  in solve 0
    ((Κ (+ 16 / 1) ⊗
       (((Κ (+ 1 / 5) ⊖
          (Κ (+ 1 / 3) ⊗
            ((Κ (+ 1 / 5) ⊗ Κ (+ 1 / 5)) ⊗ Κ (+ 1 / 5))))
         ⊕
         (Κ (+ 1 / 5) ⊗
           (((Κ (+ 1 / 5) ⊗ Κ (+ 1 / 5)) ⊗ Κ (+ 1 / 5))
             ⊗ (Κ (+ 1 / 5) ⊗ Κ (+ 1 / 5)))))
        ⊖
        (Κ (+ 1 / 7) ⊗
          (((((Κ (+ 1 / 5) ⊗ Κ (+ 1 / 5)) ⊗ Κ (+ 1 / 5))
              ⊗ (Κ (+ 1 / 5) ⊗ Κ (+ 1 / 5)))
            ⊗ (Κ (+ 1 / 5) ⊗ Κ (+ 1 / 5))))))
      ⊖ (Κ (+ 4 / 1) ⊗ Κ (+ 1 / 239))
      ⊜ Κ archimedesLowerRational)
    BishopP.≃-refl

archimedesLowerBelowCertifiedRational :
  archimedesLower ℚ.< archimedesLowerRational
archimedesLowerBelowCertifiedRational =
  ℚP.<-respˡ-≃
    (ℚP.≃-sym (ℚP.+-identityʳ archimedesLower))
    (ℚP.+-monoʳ-<
      archimedesLower
      (ℚP.positive⁻¹ archimedesMargin))

archimedesLowerBelowMachinPi :
  Bishop._<_ (embed archimedesLower) Atan.bishopMachinPi
archimedesLowerBelowMachinPi =
  BishopP.<-≤-trans
    (BishopP.<-respʳ-≃
      (BishopP.≃-symm machinArchimedesLowerCandidateIsRational)
      (BishopP.p<q⇒p⋆<q⋆
        archimedesLower
        archimedesLowerRational
        archimedesLowerBelowCertifiedRational))
    machinArchimedesLowerCandidateSound

machinPiBelowArchimedesUpper :
  Bishop._<_
    Atan.bishopMachinPi
    (embed Window.twentyTwoSevenths)
machinPiBelowArchimedesUpper =
  Window.machinPiBelowTwentyTwoSevenths

archimedesLowerBelowMachinPiNonStrict :
  Bishop._≤_ (embed archimedesLower) Atan.bishopMachinPi
archimedesLowerBelowMachinPiNonStrict =
  BishopP.<⇒≤ archimedesLowerBelowMachinPi

machinPiBelowArchimedesUpperNonStrict :
  Bishop._≤_ Atan.bishopMachinPi (embed Window.twentyTwoSevenths)
machinPiBelowArchimedesUpperNonStrict =
  BishopP.<⇒≤ machinPiBelowArchimedesUpper

bishopMachinPiArchimedesNumericalWindowLevel : ProofLevel
bishopMachinPiArchimedesNumericalWindowLevel = machineChecked

-- Numerical parity with the classical Archimedes headline is now present on
-- the actual Bishop Machin real.  Equality with the geometric/trigonometric pi
-- remains intentionally separate.
bishopMachinPiGeometricTrigIdentificationLevel : ProofLevel
bishopMachinPiGeometricTrigIdentificationLevel = conditional
