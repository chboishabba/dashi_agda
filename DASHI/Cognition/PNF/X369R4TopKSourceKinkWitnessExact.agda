{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.X369R4TopKSourceKinkWitnessExact where

-- Concrete FINITE Nat witness for the existing early Agda owner.
-- Values (0,2,9,0) are from an explicitly declared, source-shaped
-- R4 coherent topk/softmax mathematical parameter fixture, checked
-- separately by scripts/check_x369_r4_topk_kink_sympy.py.
--
-- They are NOT observed trained-Leech tensors, and this Agda source
-- does not prove the PyTorch float execution of those weights.
-- No alternate ResponseKink definition or new biological claim.
-- Original Leech-LILA attribution: Anatolii Kornienko.

open import DASHI.Core.Prelude
import DASHI.Cognition.ResponseKink as Kink
import DASHI.Cognition.PNF.X369R4EarlyKinkSourceWeldExact as Weld

-- Original R4 fixed source-shaped parameter fixture:
-- t=0: selected [0,1], scalar softmax ~0.00669285 -> floor(10y)=0
-- t=1: selected [0,1], scalar softmax ~0.26894142 -> floor(10y)=2
-- t=2: selected [1,0], scalar softmax ~0.95257413 -> floor(10y)=9
-- t=3: selected [3,2], both outputs zero -> floor(10y)=0
-- All score/order and Nat-cell interval premises are implemented
-- in the corresponding external SymPy source calculator.

r4FixtureNatResponse : Kink.DriveStage → Nat
r4FixtureNatResponse Kink.insufficient = 0
r4FixtureNatResponse Kink.recruited = 2
r4FixtureNatResponse Kink.selected = 9
r4FixtureNatResponse Kink.overloaded = 0

r4FixtureProfile : Kink.RecruitmentSuppressionProfile Kink.DriveStage
r4FixtureProfile = record
  { lowInput = Kink.insufficient
  ; prePeakInput = Kink.recruited
  ; peakInput = Kink.selected
  ; overloadInput = Kink.overloaded
  ; response = r4FixtureNatResponse
  ; low-to-prePeak-rise = s≤s z≤n
  ; prePeak-to-peak-rise = s≤s (s≤s (s≤s z≤n))
  ; overload-below-peak = s≤s z≤n
  }

r4SameFixtureResponse :
  Weld.OriginalR4FourRegimeEvidence Kink.DriveStage
r4SameFixtureResponse = record
  { originalResponse = r4FixtureNatResponse
  ; originalShape = r4FixtureProfile
  ; sameOriginalResponse = λ stage → refl
  }

r4FiniteKinkSourceShape :
  (r4FixtureNatResponse Kink.insufficient
   < r4FixtureNatResponse Kink.recruited)
  × ((r4FixtureNatResponse Kink.recruited
      < r4FixtureNatResponse Kink.selected)
     × (r4FixtureNatResponse Kink.overloaded
        < r4FixtureNatResponse Kink.selected))
r4FiniteKinkSourceShape =
  Weld.sameSourceR4RiseAndOverload r4SameFixtureResponse

-- The fixed-route mathematical intervention instead produces
-- a strictly increasing softmax response, so there is no
-- overload-below-peak receipt for that intervention.
-- The difference is selected-set replacement, not GELU alone.
