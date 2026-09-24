module DASHI.Analysis.RiemannPlattTrudgianLocatedHeightArithmeticExact where

------------------------------------------------------------------------
-- EXACT RATIONAL ARITHMETIC FOR THE CONSTRUCTIVE LOCATED HEIGHT WINDOW
--
-- The source ledger records
--
--   X = 6000000185827,
--   T_PT = 3000175332800,
--   2 T_PT - X = 350479773.
--
-- We reconstruct the arithmetic here rather than promoting the prose/source
-- receipt into a theorem.  The resulting strict rational inequality is the
-- quantitative seed for the located low/high split.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_+_; _*_)
open import Data.Integer.Base as Int
open import Data.Rational.Base as Rational using (ℚ; _/_; _<_)
import Data.Rational.Properties as RationalLaws
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Data.Unit.Base using (tt)

import DASHI.Analysis.DeBruijnNewman2026SourceWeldExact as Source
import DASHI.Analysis.RiemannPlattTrudgianCanonicalLowRegionExact as Low

candidateHalfHeight : ℚ
candidateHalfHeight =
  Int.+ Source.candidateX / 2

publishedVerifiedHeightRational : ℚ
publishedVerifiedHeightRational =
  Int.+ Low.publishedVerifiedHeight / 1

candidateHalfBelowPublishedHeight :
  candidateHalfHeight < publishedVerifiedHeightRational
candidateHalfBelowPublishedHeight =
  toWitness
    {a? = RationalLaws._<?_
      candidateHalfHeight
      publishedVerifiedHeightRational}
    tt

doubledHeightSurplusExact :
  Source.candidateX + Source.reportedDoubledHeightSurplus
  ≡
  2 * Source.plattTrudgianVerifiedHeight
doubledHeightSurplusExact = refl

publishedHeightOwnerAgreement :
  Low.publishedVerifiedHeight ≡ Source.plattTrudgianVerifiedHeight
publishedHeightOwnerAgreement = refl

record LocatedHeightArithmeticBoundary : Set where
  constructor located-height-arithmetic-boundary
  field
    candidateHalfThresholdExact : Bool
    publishedHeightExact : Bool
    strictRationalWindowChecked : Bool
    reportedDoubledSurplusReconstructed : Bool
    sourceProseUsedAsProof : Bool
    rhDerivedHere : Bool

open LocatedHeightArithmeticBoundary public

canonicalLocatedHeightArithmeticBoundary : LocatedHeightArithmeticBoundary
canonicalLocatedHeightArithmeticBoundary =
  located-height-arithmetic-boundary
    true true true true false false
