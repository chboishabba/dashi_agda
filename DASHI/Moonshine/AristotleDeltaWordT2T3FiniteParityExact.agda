module DASHI.Moonshine.AristotleDeltaWordT2T3FiniteParityExact where

------------------------------------------------------------------------
-- UPSTREAM ARISTOTLE SOURCE / ATTRIBUTION
--
-- Aristotle (Harmonic), editor of the user-supplied Lean project.
-- Source modules:
--   RequestProject.DeltaWordGraphs
--   SHA-256 2aff96beec88c28999131f5ec06ecfe395f070bb7382dde3ea55a97659d0da34
--   RequestProject.T2vsT3
--   SHA-256 33eda89c443c6060bc1cc3facee7b3154ebaf89f6abe4e2f0fdb3f0f1e9862ab
--
-- The upstream README requests @Aristotle-Harmonic attribution and the commit
-- trailer
--   Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
--
-- PRIMARY MATHEMATICAL SOURCES / CONTEXT
-- Toshitsune Miyake, "Modular Forms", Springer, 2006.
-- DOI: 10.1007/3-540-29593-3.
-- Jean-Pierre Serre, "A Course in Arithmetic", Springer, 1973.
-- DOI: 10.1007/978-1-4684-9884-4.
--
-- DASHI CONTRIBUTION
-- Port the finite coefficient plate that the Aristotle source uses to compare
-- T2 Delta and T3 Delta.  This module stays deliberately finite: it derives
-- the five source word multipliers and the m=1,2,3 product/difference/
-- Euclidean-quotient/remainder rows from the already pinned tau(2), tau(3)
-- values.  It does not promote the finite coefficient scan to a global claim.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Data.Integer using (ℤ; +_; -[1+_])
  renaming
    ( _+_ to _+ℤ_
    ; _-_ to _-ℤ_
    ; _*_ to _*ℤ_
    )

import DASHI.Moonshine.RamanujanTauHecke23Exact as Tau

data Sample123 : Set where
  sample1 sample2 sample3 : Sample123

sampleTau : Sample123 → ℤ
sampleTau sample1 = + 1
sampleTau sample2 = Tau.tau2
sampleTau sample3 = Tau.tau3

wordT2Sample : Sample123 → ℤ
wordT2Sample sample = Tau.tau2 *ℤ sampleTau sample

wordT3Sample : Sample123 → ℤ
wordT3Sample sample = Tau.tau3 *ℤ sampleTau sample

productSample : Sample123 → ℤ
productSample sample = wordT2Sample sample *ℤ wordT3Sample sample

differenceSample : Sample123 → ℤ
differenceSample sample = wordT2Sample sample -ℤ wordT3Sample sample

-- The source uses Lean's Euclidean integer quotient/remainder convention.
-- We record the certified finite outputs and separately prove the defining
-- reconstruction identity at each sample.
integerQuotientSample : Sample123 → ℤ
integerQuotientSample sample1 = -[1+ 0 ]
integerQuotientSample sample2 = + 0
integerQuotientSample sample3 = -[1+ 0 ]

integerRemainderSample : Sample123 → ℤ
integerRemainderSample sample1 = + 228
integerRemainderSample sample2 = + 576
integerRemainderSample sample3 = + 57456

euclideanReconstruction :
  (sample : Sample123) →
  wordT2Sample sample
  ≡ wordT3Sample sample *ℤ integerQuotientSample sample
      +ℤ integerRemainderSample sample
euclideanReconstruction sample1 = refl
euclideanReconstruction sample2 = refl
euclideanReconstruction sample3 = refl

------------------------------------------------------------------------
-- Exact m = 1,2,3 source plate.
------------------------------------------------------------------------

sample1Row :
  wordT2Sample sample1 ≡ -[1+ 23 ]
  × wordT3Sample sample1 ≡ + 252
  × productSample sample1 ≡ -[1+ 6047 ]
  × differenceSample sample1 ≡ -[1+ 275 ]
  × integerQuotientSample sample1 ≡ -[1+ 0 ]
  × integerRemainderSample sample1 ≡ + 228
sample1Row = refl , refl , refl , refl , refl , refl

sample2Row :
  wordT2Sample sample2 ≡ + 576
  × wordT3Sample sample2 ≡ -[1+ 6047 ]
  × productSample sample2 ≡ -[1+ 3483647 ]
  × differenceSample sample2 ≡ + 6624
  × integerQuotientSample sample2 ≡ + 0
  × integerRemainderSample sample2 ≡ + 576
sample2Row = refl , refl , refl , refl , refl , refl

sample3Row :
  wordT2Sample sample3 ≡ -[1+ 6047 ]
  × wordT3Sample sample3 ≡ + 63504
  × productSample sample3 ≡ -[1+ 384072191 ]
  × differenceSample sample3 ≡ -[1+ 69551 ]
  × integerQuotientSample sample3 ≡ -[1+ 0 ]
  × integerRemainderSample sample3 ≡ + 57456
sample3Row = refl , refl , refl , refl , refl , refl

------------------------------------------------------------------------
-- DeltaWordGraphs word multipliers.
------------------------------------------------------------------------

wordMultiplierT2 : ℤ
wordMultiplierT2 = Tau.tau2

wordMultiplierT3 : ℤ
wordMultiplierT3 = Tau.tau3

wordMultiplierT2T3 : ℤ
wordMultiplierT2T3 = Tau.tau2 *ℤ Tau.tau3

wordMultiplierT2T3T2 : ℤ
wordMultiplierT2T3T2 = wordMultiplierT2T3 *ℤ Tau.tau2

wordMultiplierT3T3T3 : ℤ
wordMultiplierT3T3T3 = Tau.tau3 *ℤ Tau.tau3 *ℤ Tau.tau3

wordMultiplierPlate :
  wordMultiplierT2 ≡ -[1+ 23 ]
  × wordMultiplierT3 ≡ + 252
  × wordMultiplierT2T3 ≡ -[1+ 6047 ]
  × wordMultiplierT2T3T2 ≡ + 145152
  × wordMultiplierT3T3T3 ≡ + 16003008
wordMultiplierPlate = refl , refl , refl , refl , refl

------------------------------------------------------------------------
-- The anti-parallel comparison is division-free and therefore global on this
-- rescaled finite model: 21*T2 = -2*T3.
------------------------------------------------------------------------

antiparallelTwentyOneTwo :
  (sample : Sample123) →
  (+ 21 *ℤ wordT2Sample sample)
  ≡ (-[1+ 1 ] *ℤ wordT3Sample sample)
antiparallelTwentyOneTwo sample1 = refl
antiparallelTwentyOneTwo sample2 = refl
antiparallelTwentyOneTwo sample3 = refl

record AristotleDeltaWordT2T3FiniteBoundary : Set where
  field
    sourceThreeRowPlateConstructed : Bool
    sourceThreeRowPlateConstructedIsTrue : sourceThreeRowPlateConstructed ≡ true
    fiveWordMultipliersConstructed : Bool
    fiveWordMultipliersConstructedIsTrue : fiveWordMultipliersConstructed ≡ true
    globalCoefficientRangeClaimedHere : Bool
    globalCoefficientRangeClaimedHereIsFalse : globalCoefficientRangeClaimedHere ≡ false

canonicalAristotleDeltaWordT2T3FiniteBoundary :
  AristotleDeltaWordT2T3FiniteBoundary
canonicalAristotleDeltaWordT2T3FiniteBoundary = record
  { sourceThreeRowPlateConstructed = true
  ; sourceThreeRowPlateConstructedIsTrue = refl
  ; fiveWordMultipliersConstructed = true
  ; fiveWordMultipliersConstructedIsTrue = refl
  ; globalCoefficientRangeClaimedHere = false
  ; globalCoefficientRangeClaimedHereIsFalse = refl
  }
