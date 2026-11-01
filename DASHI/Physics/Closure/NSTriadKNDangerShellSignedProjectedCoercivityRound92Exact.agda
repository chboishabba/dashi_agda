module DASHI.Physics.Closure.NSTriadKNDangerShellSignedProjectedCoercivityRound92Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / STRUCTURAL CALIBRATION
--
-- Authors: Peter Constantin; Vlad Vicol.
-- Title: "Nonlinear maximum principles for dissipative linear nonlocal
-- operators and applications".
-- Geometric and Functional Analysis 22 (2012), 1289--1321.
-- DOI: 10.1007/s00039-012-0172-9.
--
-- Authors: Alexander Kiselev; Fedor Nazarov; Alexander Volberg.
-- Title: "Global well-posedness for the critical 2D dissipative
-- quasi-geostrophic equation".
-- Inventiones Mathematicae 167 (2007), 445--453.
-- DOI: 10.1007/s00222-006-0020-3.
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- AUTHORITY BOUNDARY
--
-- Constantin--Vicol and Kiselev--Nazarov--Volberg are scalar/nonlocal
-- precedents for the proof SHAPE "structural defect + dissipative lower bound
-- beats the bad nonlinear contribution".  No SQG maximum principle is
-- imported into 3-D Navier--Stokes.  Waleffe is helical-triad structural
-- context only.
--
-- ROUND92 / EXACT CONSUMER ALGEBRA
--
-- The Round91 formulation
--
--   bad <= (1-eta) good + epsilon dissipation
--
-- is not enough by itself to manufacture a dissipation margin: one also needs
-- the good sector to fund the same dissipation currency.  The division-free
-- form is
--
--   bad + eta good <= good + epsilon D,
--   mu D <= good,
--   epsilon + delta <= eta mu.
--
-- Then, exactly,
--
--   bad + delta D <= good.
--
-- Thus the live PDE theorem is sharpened to TWO same-object structural facts:
--
--   (1) signed good/bad defect domination;
--   (2) quantitative good-sector funding of the literal dissipation.
--
-- Once those are supplied with epsilon + delta <= eta mu, the strict surplus
-- is pure ordered-field algebra.  No amplitude-smallness criterion is assumed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

record DangerShellSignedProjectedCoercivityData : Set where
  constructor danger-shell-signed-projected-coercivity-data
  field
    bad good dissipation : ℚ
    eta epsilon mu delta : ℚ

    badNonnegative : 0ℚ ≤ bad
    goodNonnegative : 0ℚ ≤ good
    dissipationNonnegative : 0ℚ ≤ dissipation
    etaNonnegative : 0ℚ ≤ eta
    epsilonNonnegative : 0ℚ ≤ epsilon
    muNonnegative : 0ℚ ≤ mu
    deltaNonnegative : 0ℚ ≤ delta

    signedDefectDomination :
      bad + eta * good ≤ good + epsilon * dissipation

    goodFundsDissipation :
      mu * dissipation ≤ good

    strictHeadroom :
      epsilon + delta ≤ eta * mu

open DangerShellSignedProjectedCoercivityData public

headroomTimesDissipation :
  (data : DangerShellSignedProjectedCoercivityData) →
  (epsilon data + delta data) * dissipation data
    ≤ (eta data * mu data) * dissipation data
headroomTimesDissipation data =
  L2.nonnegativeProductMonotone
    (ℚP.+-mono-≤ (epsilonNonnegative data) (deltaNonnegative data))
    (dissipationNonnegative data)
    (ℚP.*-nonNegative (etaNonnegative data) (muNonnegative data))
    (dissipationNonnegative data)
    (strictHeadroom data)
    ℚP.≤-refl

etaMuDissipationBelowEtaGood :
  (data : DangerShellSignedProjectedCoercivityData) →
  (eta data * mu data) * dissipation data ≤ eta data * good data
etaMuDissipationBelowEtaGood data =
  let
    scaled : eta data * (mu data * dissipation data) ≤ eta data * good data
    scaled =
      let instance etaNN = nonNegative (etaNonnegative data)
      in ℚP.*-monoˡ-≤-nonNeg (eta data) (goodFundsDissipation data)
  in
  subst
    (λ left → left ≤ eta data * good data)
    (solve (eta data ∷ mu data ∷ dissipation data ∷ []))
    scaled

headroomDissipationBelowEtaGood :
  (data : DangerShellSignedProjectedCoercivityData) →
  (epsilon data + delta data) * dissipation data ≤ eta data * good data
headroomDissipationBelowEtaGood data =
  ℚP.≤-trans
    (headroomTimesDissipation data)
    (etaMuDissipationBelowEtaGood data)

dangerShellStrictProjectedCoercivity :
  (data : DangerShellSignedProjectedCoercivityData) →
  bad data + delta data * dissipation data ≤ good data
dangerShellStrictProjectedCoercivity data =
  let
    addBad :
      bad data + (epsilon data + delta data) * dissipation data
      ≤ bad data + eta data * good data
    addBad =
      ℚP.+-mono-≤ ℚP.≤-refl (headroomDissipationBelowEtaGood data)

    throughSignedDefect :
      bad data + (epsilon data + delta data) * dissipation data
      ≤ good data + epsilon data * dissipation data
    throughSignedDefect =
      ℚP.≤-trans addBad (signedDefectDomination data)

    leftMeaning :
      bad data + (epsilon data + delta data) * dissipation data
      ≡ (bad data + delta data * dissipation data)
          + epsilon data * dissipation data
    leftMeaning =
      solve
        ( bad data ∷ epsilon data ∷ delta data
        ∷ dissipation data ∷ [])

    shifted :
      (bad data + delta data * dissipation data)
        + epsilon data * dissipation data
      ≤ good data + epsilon data * dissipation data
    shifted =
      subst
        (λ left → left ≤ good data + epsilon data * dissipation data)
        leftMeaning
        throughSignedDefect
  in
  ℚP.+-cancelʳ-≤ (epsilon data * dissipation data) shifted

record PhysicalDangerShellCoercivityInputs : Set where
  constructor physical-danger-shell-coercivity-inputs
  field
    algebra : DangerShellSignedProjectedCoercivityData

    -- These are deliberately theorem-valued boundaries rather than Bool
    -- receipts.  A physical instantiation must produce the two facts on the
    -- SAME shell/time/solution carrier.
    signedDefectIsPhysicalProjectedNonlinearity : Set
    goodFundingIsLiteralDissipation : Set

open PhysicalDangerShellCoercivityInputs public

physicalDangerShellStrictSurplusArithmetic :
  (inputs : PhysicalDangerShellCoercivityInputs) →
  bad (algebra inputs) + delta (algebra inputs) * dissipation (algebra inputs)
    ≤ good (algebra inputs)
physicalDangerShellStrictSurplusArithmetic inputs =
  dangerShellStrictProjectedCoercivity (algebra inputs)

round92SignedDefectPlusGoodFundingImpliesStrictSurplus : Bool
round92SignedDefectPlusGoodFundingImpliesStrictSurplus = true

round92RelativeSignedDominationAloneImpliesViscousMargin : Bool
round92RelativeSignedDominationAloneImpliesViscousMargin = false

round92PhysicalSignedDefectOnLiteralProjectedCarrierConstructed : Bool
round92PhysicalSignedDefectOnLiteralProjectedCarrierConstructed = false

round92PhysicalGoodSectorFundsLiteralDissipationConstructed : Bool
round92PhysicalGoodSectorFundsLiteralDissipationConstructed = false

round92DangerShellSignedProjectedNonlinearCoercivityConstructed : Bool
round92DangerShellSignedProjectedNonlinearCoercivityConstructed = false

round92SignedDefectPlusGoodFundingImpliesStrictSurplusIsTrue :
  round92SignedDefectPlusGoodFundingImpliesStrictSurplus ≡ true
round92SignedDefectPlusGoodFundingImpliesStrictSurplusIsTrue = refl

round92RelativeSignedDominationAloneImpliesViscousMarginIsFalse :
  round92RelativeSignedDominationAloneImpliesViscousMargin ≡ false
round92RelativeSignedDominationAloneImpliesViscousMarginIsFalse = refl
