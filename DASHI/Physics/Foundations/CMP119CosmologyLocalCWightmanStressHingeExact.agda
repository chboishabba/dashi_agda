{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyLocalCWightmanStressHingeExact where

------------------------------------------------------------------------
-- SHARED HINGE FOR THE TWO REMAINING PRODUCERS.
--
-- The scoped OS/Wightman authority says that a Wightman QFT with Poincare
-- covariance is reconstructed from the OS Schwinger family, but it does not
-- expose a theorem-bearing map sending the already-selected Local-C stress
--
--   LocalC.stressTensor localC
--
-- to a Lorentzian operator on that reconstructed theory.
--
-- This module isolates exactly that missing map.  A Lorentzian operator carrier
-- is permitted here, but the selected Lorentzian stress is NOT free:
--
--   selectedLorentzianStress
--     = continueLocalCStress (LocalC.stressTensor localC).
--
-- Thus producer A (boost covariance) and producer B (E->L continuation) share
-- one and the same continuation image.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.YMSprint105OSToWightmanBridge as Sprint105
import DASHI.Physics.Closure.YMOSWightmanReconstructionAuthority as OSW
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as LocalC
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSReconstructionExact as OSR

record LocalCWightmanStressHinge
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (group : Top.CompactSimpleGroup C)
    {G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient Hilbert Vector Hamiltonian Algebra
     Scale Volume Root ContinuumFamily Core
     sequenceLimit limitLaws quotient division osS osInputs reconstruction}
    (localC :
      LocalC.PinnedCMP119ConcreteLocalCInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient (Top.StressTensor C)
        Hilbert Vector Hamiltonian Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = osS}
        osInputs reconstruction group)
    : Set₁ where
  field
    LorentzianStressOperator : Set

    continueLocalCStress :
      Top.StressTensor C → LorentzianStressOperator

    selectedLorentzianStress :
      LorentzianStressOperator

    selectedLorentzianStressIsContinuationImage :
      selectedLorentzianStress
      ≡ continueLocalCStress (LocalC.stressTensor localC)

    boostConjugate :
      LorentzianStressOperator → LorentzianStressOperator

    stress01Expectation :
      Vector → LorentzianStressOperator → ℚ

    lorentzianTraceExpectation :
      Vector → LorentzianStressOperator → ℚ

open LocalCWightmanStressHinge public

selectedStressIsPinnedLocalCContinuation :
  ∀ {C S Y group
      G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division osS osInputs reconstruction
      localC}
    (hinge :
      LocalCWightmanStressHinge
        {C = C} {S = S} Y group localC) →
  selectedLorentzianStress hinge
  ≡ continueLocalCStress hinge (LocalC.stressTensor localC)
selectedStressIsPinnedLocalCContinuation =
  selectedLorentzianStressIsContinuationImage

osWightmanAuthorityAvailableForHinge : Bool
osWightmanAuthorityAvailableForHinge =
  OSW.osWightmanReconstructionProviderAuthorityAvailable

osWightmanAuthorityAvailableForHingeIsTrue :
  osWightmanAuthorityAvailableForHinge ≡ true
osWightmanAuthorityAvailableForHingeIsTrue = refl

poincareCovarianceAuthorityConditionalForHinge : Bool
poincareCovarianceAuthorityConditionalForHinge =
  Sprint105.WightmanObligationStatus.authorityConditional
    Sprint105.covarianceObligation

poincareCovarianceAuthorityConditionalForHingeIsTrue :
  poincareCovarianceAuthorityConditionalForHinge ≡ true
poincareCovarianceAuthorityConditionalForHingeIsTrue = refl

hingeConstructedByOSAuthorityAlone : Bool
hingeConstructedByOSAuthorityAlone = false
