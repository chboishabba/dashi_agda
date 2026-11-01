module DASHI.Dynamics.LogisticBifurcationDiagnostic where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Logistic equation: x_{n+1} = r · x_n · (1 - x_n)
--
-- r and x are modelled as rational approximations using Nat scaled
-- by 100 to avoid ℚ complexity while preserving diagnostic structure.
------------------------------------------------------------------------

RParam : Set
RParam = Nat

XState : Set
XState = Nat

------------------------------------------------------------------------
-- Bifurcation thresholds  (r values × 100)
------------------------------------------------------------------------

rStableFixedPoint : RParam
rStableFixedPoint = 300   -- r = 3.0 : first bifurcation (3: dialectic)

rPeriod4 : RParam
rPeriod4 = 345             -- r ≈ 3.45 : period-4 onset

rChaosOnset : RParam
rChaosOnset = 357          -- r ≈ 3.57 : chaos onset

rPeriod3Window : RParam
rPeriod3Window = 383       -- r ≈ 3.83 : period-3 window (3→6→12→chaos)

------------------------------------------------------------------------
-- Tlurey 3-6-9 phase labels
------------------------------------------------------------------------

data TlureyPhase : Set where
  phase3 : TlureyPhase   -- dialectic thesis / first bifurcation
  phase6 : TlureyPhase   -- antithesis / hybrid oscillatory exchange
  phase9 : TlureyPhase   -- synthesis / chaotic pluralism or rebirth

data BifurcationStage : Set where
  stageStable    : BifurcationStage
  stagePeriod2   : BifurcationStage
  stagePeriodN   : BifurcationStage
  stageChaos     : BifurcationStage
  stagePeriod3   : BifurcationStage
  stageUnbounded : BifurcationStage

------------------------------------------------------------------------
-- if-then-else helper
------------------------------------------------------------------------

if_then_else_ : ∀ {A : Set} → Bool → A → A → A
if true  then a else _ = a
if false then _ else b = b

------------------------------------------------------------------------
-- Comparison helper
------------------------------------------------------------------------

_<?_ : Nat → Nat → Bool
_     <? zero  = false
zero  <? suc _ = true
suc m <? suc n = m <? n

------------------------------------------------------------------------
-- Phase at threshold
------------------------------------------------------------------------

classifyBifurcation : RParam → BifurcationStage
classifyBifurcation r =
  if (r <? rPeriod4) then
    (if (r <? rStableFixedPoint) then stageStable else stagePeriod2)
  else
    (if (r <? rChaosOnset) then stagePeriodN else
     (if (r <? rPeriod3Window) then stageChaos else stagePeriod3))

phaseAtThreshold : RParam → TlureyPhase
phaseAtThreshold r =
  if (r <? rStableFixedPoint) then phase3 else
  (if (r <? rPeriod3Window) then phase6 else phase9)

------------------------------------------------------------------------
-- Yorke's theorem: period-3 implies chaos
------------------------------------------------------------------------

periodThreeImpliesChaos : Bool
periodThreeImpliesChaos = true

periodThreeWindowDialectic : String
periodThreeWindowDialectic =
  "Period-3 → period-6 → period-12 → ... → chaos."

------------------------------------------------------------------------
-- Diagnostic gates
------------------------------------------------------------------------

logisticIsDiagnostic : Bool
logisticIsDiagnostic = true

logisticIsCosmicProof : Bool
logisticIsCosmicProof = false

chaosRequiresExternalCalibration : Bool
chaosRequiresExternalCalibration = true
