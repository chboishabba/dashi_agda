{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNLiveNestedSelfCanonicalExternalSpacetimeRound624Exact where

------------------------------------------------------------------------
-- ROUND624 / LIVE R568 NESTED LEAF-A = SELF + CANONICAL EXTERNAL IN SPACETIME
--
-- R623 proves, on each live finite slice and for each spectator beta,
--
--   NestedRow = SelfNestedRow + CanonicalExternalNestedRow.
--
-- This owner lifts that exact signed identity through the SAME aggregations used
-- by the existing live spectator-resolvent Leaf-A route:
--
--   spectator beta sum
--   -> output k sum
--   -> canonical nonzero output list
--   -> time integration.
--
-- It then supplies a least-privilege producer:
--
--   cutoff-uniform self nested signed budget
--   + cutoff-uniform canonical-external nested signed budget
--     -> existing NestedSpectatorSpacetimeBudget
--     -> existing R568 CommutatorOnlySpacetimeBudget568.
--
-- No norm, absolute value, shell count, positivity replacement, or new PDE
-- estimate is introduced.  The two signed analytic inequalities remain open.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNFactoredFullCommutatorOnlyRound567Exact as R567
import DASHI.Physics.Closure.NSTriadKNLiveCommutatorOnlyLeafABoundaryRound568Exact as R568
import DASHI.Physics.Closure.NSTriadKNLiveSpectatorResolventNestedLeafABidiExact as LiveNested
import DASHI.Physics.Closure.NSTriadKNSpectatorNestedSelfCanonicalExternalRowRound623Exact as R623

F : C3.RealField _
F = Rational.rationalRealField

module LiveCanonicalSplit
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (integration : R495.IntegrationTransportAuthority Time integrateTo) where

  module Base = LiveNested.LiveNested
    Time initialTime integrateTo DerivativeOf integration

  module Dyn = Base.Dyn
  module Support = Base.Support
  module Comm = Base.Comm

  module At
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T)
      (cutoff : Nat) (time : Time) where

    module B = Base.At T R cutoff time
    module Rows = R623.SignedRowSplit
      B.Slice.PS B.S B.L B.H B.velocityTransverse

    selfRows :
      Z3.FourierMode →
      List Physical.PhysicalTriadIncidence → ℚ
    selfRows output [] = 0ℚ
    selfRows output (beta ∷ rest) =
      Rows.selfNestedForcingRow output beta
        + selfRows output rest

    canonicalExternalRows :
      Z3.FourierMode →
      List Physical.PhysicalTriadIncidence → ℚ
    canonicalExternalRows output [] = 0ℚ
    canonicalExternalRows output (beta ∷ rest) =
      Rows.canonicalExternalNestedForcingRow output beta
        + canonicalExternalRows output rest

    allRowsSplit :
      (output : Z3.FourierMode) →
      (betas : List Physical.PhysicalTriadIncidence) →
      B.Weld.allNestedForcingRows output betas
      ≡ selfRows output betas + canonicalExternalRows output betas
    allRowsSplit output [] = refl
    allRowsSplit output (beta ∷ rest)
      rewrite Rows.nestedForcingRowSplitsSelfCanonicalExternal output beta
            | allRowsSplit output rest =
      solve
        ( Rows.selfNestedForcingRow output beta
        ∷ Rows.canonicalExternalNestedForcingRow output beta
        ∷ selfRows output rest
        ∷ canonicalExternalRows output rest
        ∷ [])

    selfNestedOutputForcingFull :
      Z3.FourierMode → ℚ
    selfNestedOutputForcingFull output =
      selfRows output
        (Output.physicalOutputFiber cutoff output)

    canonicalExternalNestedOutputForcingFull :
      Z3.FourierMode → ℚ
    canonicalExternalNestedOutputForcingFull output =
      canonicalExternalRows output
        (Output.physicalOutputFiber cutoff output)

    nestedOutputSplitsSelfCanonicalExternal :
      (output : Z3.FourierMode) →
      B.nestedOutputForcingFull output
      ≡
      selfNestedOutputForcingFull output
        + canonicalExternalNestedOutputForcingFull output
    nestedOutputSplitsSelfCanonicalExternal output =
      allRowsSplit output
        (Output.physicalOutputFiber cutoff output)

  selfNestedSumOutputs :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) → Time → List Z3.FourierMode → ℚ
  selfNestedSumOutputs T R cutoff time [] = 0ℚ
  selfNestedSumOutputs T R cutoff time (output ∷ rest) =
    let module A = At T R cutoff time in
    A.selfNestedOutputForcingFull output
      + selfNestedSumOutputs T R cutoff time rest

  canonicalExternalNestedSumOutputs :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) → Time → List Z3.FourierMode → ℚ
  canonicalExternalNestedSumOutputs T R cutoff time [] = 0ℚ
  canonicalExternalNestedSumOutputs T R cutoff time (output ∷ rest) =
    let module A = At T R cutoff time in
    A.canonicalExternalNestedOutputForcingFull output
      + canonicalExternalNestedSumOutputs T R cutoff time rest

  nestedSumOutputsSplitsSelfCanonicalExternal :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (time : Time) →
    (outputs : List Z3.FourierMode) →
    Base.nestedSumOutputs T R cutoff time outputs
    ≡
    selfNestedSumOutputs T R cutoff time outputs
      + canonicalExternalNestedSumOutputs T R cutoff time outputs
  nestedSumOutputsSplitsSelfCanonicalExternal T R cutoff time [] = refl
  nestedSumOutputsSplitsSelfCanonicalExternal
      T R cutoff time (output ∷ rest) =
    let
      module A = At T R cutoff time
      selfHead = A.selfNestedOutputForcingFull output
      externalHead = A.canonicalExternalNestedOutputForcingFull output
      selfTail = selfNestedSumOutputs T R cutoff time rest
      externalTail = canonicalExternalNestedSumOutputs T R cutoff time rest
    in
    trans
      (cong₂ _+_
        (A.nestedOutputSplitsSelfCanonicalExternal output)
        (nestedSumOutputsSplitsSelfCanonicalExternal
          T R cutoff time rest))
      (solve
        (selfHead ∷ externalHead ∷ selfTail ∷ externalTail ∷ []))

  selfNestedGlobalForcingFull :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  selfNestedGlobalForcingFull T R cutoff time =
    selfNestedSumOutputs T R cutoff time
      (Canonical.nonzeroCutoffModes cutoff)

  canonicalExternalNestedGlobalForcingFull :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  canonicalExternalNestedGlobalForcingFull T R cutoff time =
    canonicalExternalNestedSumOutputs T R cutoff time
      (Canonical.nonzeroCutoffModes cutoff)

  nestedGlobalSplitsSelfCanonicalExternal :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (time : Time) →
    Base.nestedGlobalForcingFull T R cutoff time
    ≡
    selfNestedGlobalForcingFull T R cutoff time
      + canonicalExternalNestedGlobalForcingFull T R cutoff time
  nestedGlobalSplitsSelfCanonicalExternal T R cutoff time =
    nestedSumOutputsSplitsSelfCanonicalExternal
      T R cutoff time (Canonical.nonzeroCutoffModes cutoff)

  integratedSelfNestedGlobalForcingFull :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  integratedSelfNestedGlobalForcingFull T R cutoff terminal =
    integrateTo (selfNestedGlobalForcingFull T R cutoff) terminal

  integratedCanonicalExternalNestedGlobalForcingFull :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  integratedCanonicalExternalNestedGlobalForcingFull
      T R cutoff terminal =
    integrateTo
      (canonicalExternalNestedGlobalForcingFull T R cutoff)
      terminal

  integratedNestedSplitsSelfCanonicalExternal :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (terminal : Time) →
    Base.integratedNestedGlobalForcingFull T R cutoff terminal
    ≡
    integratedSelfNestedGlobalForcingFull T R cutoff terminal
      + integratedCanonicalExternalNestedGlobalForcingFull
          T R cutoff terminal
  integratedNestedSplitsSelfCanonicalExternal T R cutoff terminal =
    let
      full = Base.nestedGlobalForcingFull T R cutoff
      self = selfNestedGlobalForcingFull T R cutoff
      external = canonicalExternalNestedGlobalForcingFull T R cutoff
    in
    trans
      (R495.integrateCongruent integration
        full
        (λ time → self time + external time)
        (nestedGlobalSplitsSelfCanonicalExternal T R cutoff)
        terminal)
      (R495.integrateAdd integration self external terminal)

  record SelfCanonicalExternalNestedSpacetimeBudget
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T) : Set₁ where
    field
      selfNestedBound canonicalExternalNestedBound : Time → ℚ

      selfNestedSignedBudget :
        (cutoff : Nat) (terminal : Time) →
        R567.four567 *
          integratedSelfNestedGlobalForcingFull T R cutoff terminal
        ≤ selfNestedBound terminal

      canonicalExternalNestedSignedBudget :
        (cutoff : Nat) (terminal : Time) →
        R567.four567 *
          integratedCanonicalExternalNestedGlobalForcingFull
            T R cutoff terminal
        ≤ canonicalExternalNestedBound terminal

  open SelfCanonicalExternalNestedSpacetimeBudget public

  combinedNestedBound :
    ∀ {T R} →
    SelfCanonicalExternalNestedSpacetimeBudget T R →
    Time → ℚ
  combinedNestedBound B terminal =
    selfNestedBound B terminal + canonicalExternalNestedBound B terminal

  splitNestedBudgetBuildsExistingNestedBudget :
    ∀ {T R} →
    SelfCanonicalExternalNestedSpacetimeBudget T R →
    Base.NestedSpectatorSpacetimeBudget T R
  splitNestedBudgetBuildsExistingNestedBudget {T} {R} B = record
    { Base.cutoffIndependentNestedBound = combinedNestedBound B
    ; Base.nestedSpectatorBudget = λ cutoff terminal →
        let
          selfI =
            integratedSelfNestedGlobalForcingFull
              T R cutoff terminal
          externalI =
            integratedCanonicalExternalNestedGlobalForcingFull
              T R cutoff terminal
          fullI =
            Base.integratedNestedGlobalForcingFull
              T R cutoff terminal

          split : fullI ≡ selfI + externalI
          split =
            integratedNestedSplitsSelfCanonicalExternal
              T R cutoff terminal

          summed :
            R567.four567 * selfI
              + R567.four567 * externalI
            ≤ selfNestedBound B terminal
              + canonicalExternalNestedBound B terminal
          summed =
            ℚP.+-mono-≤
              (selfNestedSignedBudget B cutoff terminal)
              (canonicalExternalNestedSignedBudget B cutoff terminal)

          scaleSplit :
            R567.four567 * fullI
            ≡
            R567.four567 * selfI
              + R567.four567 * externalI
          scaleSplit rewrite split =
            solve (selfI ∷ externalI ∷ [])
        in
        subst
          (_≤ combinedNestedBound B terminal)
          (sym scaleSplit)
          summed
    }

  splitNestedBudgetBuildsR568 :
    ∀ {T R} →
    SelfCanonicalExternalNestedSpacetimeBudget T R →
    Comm.CommutatorOnlySpacetimeBudget568 T R
  splitNestedBudgetBuildsR568 B =
    Base.nestedBudgetBuildsR568
      (splitNestedBudgetBuildsExistingNestedBudget B)

------------------------------------------------------------------------
-- Status / frontier.
------------------------------------------------------------------------

round624LiveNestedSelfCanonicalExternalSplitClosed : Bool
round624LiveNestedSelfCanonicalExternalSplitClosed = true

round624IntegrationTransportClosed : Bool
round624IntegrationTransportClosed = true

round624SplitSignedNestedBudgetsCompileToR568 : Bool
round624SplitSignedNestedBudgetsCompileToR568 = true

round624CanonicalExternalChannelUsesExecutableOrbitResolution : Bool
round624CanonicalExternalChannelUsesExecutableOrbitResolution = true

round624SelfNestedSignedSpacetimeBudgetClosed : Bool
round624SelfNestedSignedSpacetimeBudgetClosed = false

round624CanonicalExternalNestedSignedSpacetimeBudgetClosed : Bool
round624CanonicalExternalNestedSignedSpacetimeBudgetClosed = false

round624IntroducesNormOrAbsoluteValue : Bool
round624IntroducesNormOrAbsoluteValue = false

round624IntroducesEstimate : Bool
round624IntroducesEstimate = false

round624ClayPromotion : Bool
round624ClayPromotion = false

round624LiveNestedSelfCanonicalExternalSplitClosedIsTrue :
  round624LiveNestedSelfCanonicalExternalSplitClosed ≡ true
round624LiveNestedSelfCanonicalExternalSplitClosedIsTrue = refl

round624SplitSignedNestedBudgetsCompileToR568IsTrue :
  round624SplitSignedNestedBudgetsCompileToR568 ≡ true
round624SplitSignedNestedBudgetsCompileToR568IsTrue = refl

round624CanonicalExternalChannelUsesExecutableOrbitResolutionIsTrue :
  round624CanonicalExternalChannelUsesExecutableOrbitResolution ≡ true
round624CanonicalExternalChannelUsesExecutableOrbitResolutionIsTrue = refl

round624IntroducesNormOrAbsoluteValueIsFalse :
  round624IntroducesNormOrAbsoluteValue ≡ false
round624IntroducesNormOrAbsoluteValueIsFalse = refl

round624IntroducesEstimateIsFalse :
  round624IntroducesEstimate ≡ false
round624IntroducesEstimateIsFalse = refl

round624ClayPromotionIsFalse :
  round624ClayPromotion ≡ false
round624ClayPromotionIsFalse = refl
