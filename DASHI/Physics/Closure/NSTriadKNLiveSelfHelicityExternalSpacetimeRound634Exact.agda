{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNLiveSelfHelicityExternalSpacetimeRound634Exact where

------------------------------------------------------------------------
-- ROUND634 / LIVE HOMOCHIRAL + HETEROCHIRAL SELF + EXTERNAL -> R568
--
-- R633 splits the literal spectator self row into:
--
--   homochiral radial row + heterochiral literal row.
--
-- Lift that equality through beta aggregation, output aggregation, the live
-- trajectory and time integration.  A three-channel signed budget
--
--   homochiral + heterochiral + canonical external
--
-- compiles back into R628's two-channel producer and hence R568.
--
-- No estimate is supplied here; all three signed spacetime inequalities remain
-- explicit proof inputs.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNFactoredFullCommutatorOnlyRound567Exact as R567
import DASHI.Physics.Closure.NSTriadKNLiveCommutatorOnlyLeafABoundaryRound568Exact as R568
import DASHI.Physics.Closure.NSTriadKNLiveSelfMultiplierExternalSpacetimeRound628Exact as R628
import DASHI.Physics.Closure.NSTriadKNSpectatorSelfHomochiralHeterochiralRowRound633Exact as R633

F : C3.RealField _
F = Rational.rationalRealField

module LiveSelfHelicityExternal634
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (integration : R495.IntegrationTransportAuthority Time integrateTo) where

  module Old =
    R628.LiveMultiplierExternal
      Time initialTime integrateTo DerivativeOf integration

  module Dyn = Old.Dyn
  module Support = Old.Support
  module Comm = Old.Comm

  module At
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T)
      (cutoff : Nat) (time : Time) where

    module A = Old.At T R cutoff time
    module Rows =
      R633.SpectatorSelfHelicityRow633
        A.A.B.Slice.PS A.A.B.S A.A.B.L A.A.B.H A.A.B.velocityTransverse

    homochiralRows heterochiralRows :
      Z3.FourierMode →
      List Physical.PhysicalTriadIncidence → ℚ
    homochiralRows output [] = 0ℚ
    homochiralRows output (beta ∷ rest) =
      let module B = Rows.At beta in
      B.homochiralRow output + homochiralRows output rest

    heterochiralRows output [] = 0ℚ
    heterochiralRows output (beta ∷ rest) =
      let module B = Rows.At beta in
      B.heterochiralRow output + heterochiralRows output rest

    selfMultiplierRowsSplit :
      (output : Z3.FourierMode) →
      (betas : List Physical.PhysicalTriadIncidence) →
      A.selfMultiplierRows output betas
      ≡ homochiralRows output betas + heterochiralRows output betas
    selfMultiplierRowsSplit output [] = refl
    selfMultiplierRowsSplit output (beta ∷ rest) =
      let module B = Rows.At beta in
      trans
        (cong₂ _+_
          (B.selfMultiplierRowSplits output)
          (selfMultiplierRowsSplit output rest))
        (solve
          ( B.homochiralRow output
          ∷ B.heterochiralRow output
          ∷ homochiralRows output rest
          ∷ heterochiralRows output rest
          ∷ []))

    homochiralOutput heterochiralOutput :
      Z3.FourierMode → ℚ
    homochiralOutput output =
      homochiralRows output (Output.physicalOutputFiber cutoff output)
    heterochiralOutput output =
      heterochiralRows output (Output.physicalOutputFiber cutoff output)

    selfMultiplierOutputSplits :
      (output : Z3.FourierMode) →
      A.selfMultiplierOutputForcingFull output
      ≡ homochiralOutput output + heterochiralOutput output
    selfMultiplierOutputSplits output =
      selfMultiplierRowsSplit output
        (Output.physicalOutputFiber cutoff output)

  homochiralSumOutputs heterochiralSumOutputs :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) → Time → List Z3.FourierMode → ℚ
  homochiralSumOutputs T R cutoff time [] = 0ℚ
  homochiralSumOutputs T R cutoff time (output ∷ rest) =
    let module A = At T R cutoff time in
    A.homochiralOutput output
      + homochiralSumOutputs T R cutoff time rest

  heterochiralSumOutputs T R cutoff time [] = 0ℚ
  heterochiralSumOutputs T R cutoff time (output ∷ rest) =
    let module A = At T R cutoff time in
    A.heterochiralOutput output
      + heterochiralSumOutputs T R cutoff time rest

  selfMultiplierSumOutputsSplits :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (time : Time) →
    (outputs : List Z3.FourierMode) →
    Old.selfMultiplierSumOutputs T R cutoff time outputs
    ≡
    homochiralSumOutputs T R cutoff time outputs
      + heterochiralSumOutputs T R cutoff time outputs
  selfMultiplierSumOutputsSplits T R cutoff time [] = refl
  selfMultiplierSumOutputsSplits T R cutoff time (output ∷ rest) =
    let module A = At T R cutoff time in
    trans
      (cong₂ _+_
        (A.selfMultiplierOutputSplits output)
        (selfMultiplierSumOutputsSplits T R cutoff time rest))
      (solve
        ( A.homochiralOutput output
        ∷ A.heterochiralOutput output
        ∷ homochiralSumOutputs T R cutoff time rest
        ∷ heterochiralSumOutputs T R cutoff time rest
        ∷ []))

  homochiralGlobal heterochiralGlobal :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  homochiralGlobal T R cutoff time =
    homochiralSumOutputs T R cutoff time
      (Canonical.nonzeroCutoffModes cutoff)
  heterochiralGlobal T R cutoff time =
    heterochiralSumOutputs T R cutoff time
      (Canonical.nonzeroCutoffModes cutoff)

  selfMultiplierGlobalSplits :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (time : Time) →
    Old.selfMultiplierGlobalForcingFull T R cutoff time
    ≡ homochiralGlobal T R cutoff time + heterochiralGlobal T R cutoff time
  selfMultiplierGlobalSplits T R cutoff time =
    selfMultiplierSumOutputsSplits
      T R cutoff time (Canonical.nonzeroCutoffModes cutoff)

  integratedHomochiral integratedHeterochiral :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  integratedHomochiral T R cutoff terminal =
    integrateTo (homochiralGlobal T R cutoff) terminal
  integratedHeterochiral T R cutoff terminal =
    integrateTo (heterochiralGlobal T R cutoff) terminal

  integratedSelfMultiplierSplits :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (terminal : Time) →
    Old.integratedSelfMultiplierGlobalForcingFull T R cutoff terminal
    ≡ integratedHomochiral T R cutoff terminal
      + integratedHeterochiral T R cutoff terminal
  integratedSelfMultiplierSplits T R cutoff terminal =
    trans
      (R495.integrateCongruent integration
        (Old.selfMultiplierGlobalForcingFull T R cutoff)
        (λ time →
          homochiralGlobal T R cutoff time
            + heterochiralGlobal T R cutoff time)
        (selfMultiplierGlobalSplits T R cutoff)
        terminal)
      (R495.integrateAdd integration
        (homochiralGlobal T R cutoff)
        (heterochiralGlobal T R cutoff)
        terminal)

  record SelfHelicityCanonicalExternalSpacetimeBudget
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T) : Set₁ where
    field
      homochiralBound heterochiralBound canonicalExternalBound : Time → ℚ

      homochiralSignedBudget :
        (cutoff : Nat) (terminal : Time) →
        R567.four567 * integratedHomochiral T R cutoff terminal
        ≤ homochiralBound terminal

      heterochiralSignedBudget :
        (cutoff : Nat) (terminal : Time) →
        R567.four567 * integratedHeterochiral T R cutoff terminal
        ≤ heterochiralBound terminal

      canonicalExternalSignedBudget :
        (cutoff : Nat) (terminal : Time) →
        R567.four567
          * Old.Base.integratedCanonicalExternalNestedGlobalForcingFull
              T R cutoff terminal
        ≤ canonicalExternalBound terminal

  open SelfHelicityCanonicalExternalSpacetimeBudget public

  toR628 :
    ∀ {T R} →
    SelfHelicityCanonicalExternalSpacetimeBudget T R →
    Old.SelfMultiplierCanonicalExternalSpacetimeBudget T R
  toR628 {T} {R} B = record
    { Old.selfMultiplierBound =
        λ terminal →
          homochiralBound B terminal + heterochiralBound B terminal
    ; Old.canonicalExternalBound = canonicalExternalBound B
    ; Old.selfMultiplierSignedBudget = λ cutoff terminal →
        let
          h = integratedHomochiral T R cutoff terminal
          e = integratedHeterochiral T R cutoff terminal
          summed =
            ℚP.+-mono-≤
              (homochiralSignedBudget B cutoff terminal)
              (heterochiralSignedBudget B cutoff terminal)
          scaleSplit :
            R567.four567
              * Old.integratedSelfMultiplierGlobalForcingFull
                  T R cutoff terminal
            ≡ R567.four567 * h + R567.four567 * e
          scaleSplit
            rewrite integratedSelfMultiplierSplits T R cutoff terminal =
            solve (h ∷ e ∷ [])
        in
        subst
          (_≤ homochiralBound B terminal + heterochiralBound B terminal)
          (sym scaleSplit)
          summed
    ; Old.canonicalExternalSignedBudget =
        canonicalExternalSignedBudget B
    }

  selfHelicityExternalBudgetBuildsR568 :
    ∀ {T R} →
    SelfHelicityCanonicalExternalSpacetimeBudget T R →
    Comm.CommutatorOnlySpacetimeBudget568 T R
  selfHelicityExternalBudgetBuildsR568 B =
    Old.multiplierExternalBudgetBuildsR568 (toR628 B)

------------------------------------------------------------------------
-- Status / frontier.
------------------------------------------------------------------------

round634LiveSelfHomochiralHeterochiralSplitClosed : Bool
round634LiveSelfHomochiralHeterochiralSplitClosed = true

round634ThreeChannelBudgetsCompileToR568 : Bool
round634ThreeChannelBudgetsCompileToR568 = true

round634SeparateThreeChannelBudgetsMandatoryForR568 : Bool
round634SeparateThreeChannelBudgetsMandatoryForR568 = false

round634HomochiralSignedBudgetClosed : Bool
round634HomochiralSignedBudgetClosed = false

round634HeterochiralSignedBudgetClosed : Bool
round634HeterochiralSignedBudgetClosed = false

round634CanonicalExternalSignedBudgetClosed : Bool
round634CanonicalExternalSignedBudgetClosed = false

round634IntroducesEstimate : Bool
round634IntroducesEstimate = false

round634LiveSelfHomochiralHeterochiralSplitClosedIsTrue :
  round634LiveSelfHomochiralHeterochiralSplitClosed ≡ true
round634LiveSelfHomochiralHeterochiralSplitClosedIsTrue = refl

round634ThreeChannelBudgetsCompileToR568IsTrue :
  round634ThreeChannelBudgetsCompileToR568 ≡ true
round634ThreeChannelBudgetsCompileToR568IsTrue = refl

round634SeparateThreeChannelBudgetsMandatoryForR568IsFalse :
  round634SeparateThreeChannelBudgetsMandatoryForR568 ≡ false
round634SeparateThreeChannelBudgetsMandatoryForR568IsFalse = refl

round634IntroducesEstimateIsFalse :
  round634IntroducesEstimate ≡ false
round634IntroducesEstimateIsFalse = refl
