module DASHI.Learning.Mod97GrokkingBoundary where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Learning.GrokkingOperatorContract
open import DASHI.Learning.Mod97WeightDecayReceipt

------------------------------------------------------------------------
-- Exact, horizon-aware consequences of the recorded 15000-epoch scan.
--
-- These statements intentionally avoid promoting a universal critical weight
-- decay.  The data establish a censored transition band for this fixed task,
-- architecture, optimizer, learning rate, split, and horizon.
------------------------------------------------------------------------

record ThreeSeedPassage (a b c : RunReceipt) : Set where
  field
    epoch0 : FirstPassage
    epoch1 : FirstPassage
    epoch2 : FirstPassage
    passage0 : test95 (observation a) ≡ epoch0
    passage1 : test95 (observation b) ≡ epoch1
    passage2 : test95 (observation c) ≡ epoch2

wd450-censored : ThreeSeedPassage wd450-s0 wd450-s1 wd450-s2
wd450-censored = record
  { epoch0 = rightCensored
  ; epoch1 = rightCensored
  ; epoch2 = rightCensored
  ; passage0 = refl
  ; passage1 = refl
  ; passage2 = refl
  }

wd500-mixed : ThreeSeedPassage wd500-s0 wd500-s1 wd500-s2
wd500-mixed = record
  { epoch0 = observedAt 14440
  ; epoch1 = rightCensored
  ; epoch2 = rightCensored
  ; passage0 = refl
  ; passage1 = refl
  ; passage2 = refl
  }

wd600-all-observed : ThreeSeedPassage wd600-s0 wd600-s1 wd600-s2
wd600-all-observed = record
  { epoch0 = observedAt 11560
  ; epoch1 = observedAt 13720
  ; epoch2 = observedAt 14620
  ; passage0 = refl
  ; passage1 = refl
  ; passage2 = refl
  }

wd700-all-observed : ThreeSeedPassage wd700-s0 wd700-s1 wd700-s2
wd700-all-observed = record
  { epoch0 = observedAt 10080
  ; epoch1 = observedAt 11760
  ; epoch2 = observedAt 12200
  ; passage0 = refl
  ; passage1 = refl
  ; passage2 = refl
  }

wd800-all-observed : ThreeSeedPassage wd800-s0 wd800-s1 wd800-s2
wd800-all-observed = record
  { epoch0 = observedAt 8640
  ; epoch1 = observedAt 10200
  ; epoch2 = observedAt 10620
  ; passage0 = refl
  ; passage1 = refl
  ; passage2 = refl
  }

wd900-all-observed : ThreeSeedPassage wd900-s0 wd900-s1 wd900-s2
wd900-all-observed = record
  { epoch0 = observedAt 7520
  ; epoch1 = observedAt 9280
  ; epoch2 = observedAt 9620
  ; passage0 = refl
  ; passage1 = refl
  ; passage2 = refl
  }

wd1000-all-observed : ThreeSeedPassage wd1000-s0 wd1000-s1 wd1000-s2
wd1000-all-observed = record
  { epoch0 = observedAt 6620
  ; epoch1 = observedAt 8160
  ; epoch2 = observedAt 8400
  ; passage0 = refl
  ; passage1 = refl
  ; passage2 = refl
  }

------------------------------------------------------------------------
-- The defensible boundary receipt:
--
-- * at 0.45, all three runs are right-censored at 15000;
-- * at 0.50, the three-seed outcome is mixed;
-- * at 0.60 and above in the coarse scan, all three runs reach 95% test
--   accuracy by 15000.
--
-- This is evidence for a horizon-dependent transition band, not a proof of an
-- asymptotic critical constant and not yet a power-law critical exponent.
------------------------------------------------------------------------

record Horizon15000Boundary : Set where
  field
    lowerCensored : ThreeSeedPassage wd450-s0 wd450-s1 wd450-s2
    mixedBand     : ThreeSeedPassage wd500-s0 wd500-s1 wd500-s2
    reliable600   : ThreeSeedPassage wd600-s0 wd600-s1 wd600-s2
    reliable700   : ThreeSeedPassage wd700-s0 wd700-s1 wd700-s2
    reliable800   : ThreeSeedPassage wd800-s0 wd800-s1 wd800-s2
    reliable900   : ThreeSeedPassage wd900-s0 wd900-s1 wd900-s2
    reliable1000  : ThreeSeedPassage wd1000-s0 wd1000-s1 wd1000-s2

mod97-boundary-15000 : Horizon15000Boundary
mod97-boundary-15000 = record
  { lowerCensored = wd450-censored
  ; mixedBand = wd500-mixed
  ; reliable600 = wd600-all-observed
  ; reliable700 = wd700-all-observed
  ; reliable800 = wd800-all-observed
  ; reliable900 = wd900-all-observed
  ; reliable1000 = wd1000-all-observed
  }
