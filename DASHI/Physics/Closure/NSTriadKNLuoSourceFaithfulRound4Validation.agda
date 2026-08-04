module DASHI.Physics.Closure.NSTriadKNLuoSourceFaithfulRound4Validation where

------------------------------------------------------------------------
-- Focused validation root for the source-faithful Luo round-four tranche.
-- It imports the cumulative physical-analytic root plus the quantitative
-- Schur finite-extension theorem added at the end of this branch.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNLuoPhysicalAnalyticFrontierValidation
import DASHI.Physics.Closure.NSTriadKNLuoFiniteSchurTailDominationExact

sourceFaithfulRound4ValidationConstructed : Bool
sourceFaithfulRound4ValidationConstructed = true

sourceFaithfulRound4ValidationConstructedIsTrue :
  sourceFaithfulRound4ValidationConstructed ≡ true
sourceFaithfulRound4ValidationConstructedIsTrue = refl
