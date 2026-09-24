{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTIsraelBranchMaxCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.GRQFTDeSitterKottlerJunctionExact as Matched
import DASHI.Physics.Foundations.GRQFTIsraelShellEnergyConditionExact as MatchedEC
import DASHI.Physics.Foundations.GRQFTGeneralIsraelDECCompatibleShellExact as General
import DASHI.Physics.Foundations.GRQFTCMP119DECRepulsiveExteriorCompilerExact as CMP

------------------------------------------------------------------------
-- ISRAEL BRANCH MAX-CUT
--
-- Branch A: matched coordinate lapse
--   sigma = 0
--   P > 0
--   DEC fails.
--
-- Branch B: general timelike Israel shell with independent coordinate lapses
--   matched by shell proper time
--   sigma > 0
--   P < 0
--   NEC/WEC/DEC pass
--   SEC fails
--   exterior acceleration outward.
--
-- Branch B is the stronger current physical construction.
------------------------------------------------------------------------

data IsraelRepulsiveShellBranch : Set where
  matchedLapseZeroSigmaBranch : IsraelRepulsiveShellBranch
  generalDECCompatibleBranch : IsraelRepulsiveShellBranch

preferredCurrentBranch : IsraelRepulsiveShellBranch
preferredCurrentBranch = generalDECCompatibleBranch

record IsraelBranchMaxCut : Set where
  constructor israel-branch-max-cut
  field
    matchedLapseWitness :
      Matched.DeSitterKottlerJunctionWitness

    matchedLapseEnergyConditions :
      MatchedEC.IsraelShellEnergyConditionWitness

    generalDECWitness :
      General.GeneralIsraelDECCompatibleShellWitness

    preferredBranch :
      IsraelRepulsiveShellBranch

    preferredBranchIsGeneral :
      preferredBranch ≡ generalDECCompatibleBranch

    matchedBranchDECFails :
      MatchedEC.shellDEC MatchedEC.fixtureShellClass
        ≡ MatchedEC.conditionFails

    generalBranchDECPasses :
      General.fixtureEnergyConditionStatus
        ≡ General.necWecDecCompatibleSecViolated

    generalBranchOutward :
      General.exteriorAcceleration ≡ Data.Integer.Base.+ 3 Data.Rational.Base./ 16

open IsraelBranchMaxCut public

canonicalIsraelBranchMaxCut :
  IsraelBranchMaxCut
canonicalIsraelBranchMaxCut =
  israel-branch-max-cut
    Matched.canonicalDeSitterKottlerJunctionWitness
    MatchedEC.canonicalIsraelShellEnergyConditionWitness
    General.canonicalGeneralIsraelDECCompatibleShellWitness
    generalDECCompatibleBranch
    refl
    MatchedEC.fixtureDECFails
    refl
    General.exteriorAccelerationIsThreeSixteenths

record IsraelBranchMaxCutBoundary : Set where
  constructor israel-branch-max-cut-boundary
  field
    matchedLapseBranchStillRecorded : Bool
    matchedLapseBranchAuthoritative : Bool
    generalDECCompatibleBranchConstructed : Bool
    positiveSurfaceEnergyAvailable : Bool
    negativeSurfaceEnergyRequired : Bool
    dominantEnergyViolationRequired : Bool
    strongEnergyViolationRetained : Bool
    outwardExteriorAccelerationRetained : Bool

canonicalIsraelBranchMaxCutBoundary :
  IsraelBranchMaxCutBoundary
canonicalIsraelBranchMaxCutBoundary =
  israel-branch-max-cut-boundary
    true false true true false false true true
