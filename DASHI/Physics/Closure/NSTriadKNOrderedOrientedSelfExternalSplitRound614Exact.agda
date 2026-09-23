{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNOrderedOrientedSelfExternalSplitRound614Exact where

------------------------------------------------------------------------
-- ROUND614 / TERMINAL ORDERED ORIENTED FORCE = SELF + EXTERNAL NETWORK
--
-- The direct R503 min-cut can be stated on one signed oriented kernel
--
--   H(alpha,beta)
--     = K(alpha,beta) Re < doubleForcing_alpha , doubleCell_beta >.
--
-- R606 already proves on the same physical pair carrier
--
--   doubleForcing_alpha
--     = selfDoubleForcing_alpha + externalDoubleForcing_alpha
--
-- and hence splits the corresponding R567 forcing pair.
--
-- This owner welds that split to the actual terminal oriented kernel and lifts
-- it through the ordered off-diagonal finite sum:
--
--   Ordered(H)
--     = Ordered(H_self) + Ordered(H_external).
--
-- No norm, absolute value, estimate, shell count, or time integration enters.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNDirectCompanionOrientedForceTransposeCompletionBidiExact as Oriented
import DASHI.Physics.Closure.NSTriadKNR567ForcingFullSelfExternalSplitRound606Exact as R606

F : C3.RealField _
F = Rational.rationalRealField

module FixedOutput
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module H = Oriented.OrientedForce physicalSystem S
  module Split = R606.FixedOutput physicalSystem S output

  selfOrientedForceCross :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  selfOrientedForceCross = Split.selfForcingPair

  externalOrientedForceCross :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  externalOrientedForceCross = Split.externalForcingPair

  terminalOrientedForceIsR567ForcingPair :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    H.orientedForceCross alpha beta
    ≡ Split.C.T.forcingPair alpha beta
  terminalOrientedForceIsR567ForcingPair alpha beta =
    sym (Split.C.T.forcingPairScalarized alpha beta)

  terminalOrientedForceSplitsSelfExternal :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    H.orientedForceCross alpha beta
    ≡
    selfOrientedForceCross alpha beta
      + externalOrientedForceCross alpha beta
  terminalOrientedForceSplitsSelfExternal alpha beta =
    trans
      (terminalOrientedForceIsR567ForcingPair alpha beta)
      (Split.forcingPairSplitsSelfExternal alpha beta)

  rowSplit :
    (selected : Physical.PhysicalTriadIncidence) →
    (items : List Physical.PhysicalTriadIncidence) →
    R539.rowSum H.orientedForceCross selected items
    ≡
    R539.rowSum selfOrientedForceCross selected items
      + R539.rowSum externalOrientedForceCross selected items
  rowSplit selected [] = refl
  rowSplit selected (beta ∷ rest)
    rewrite terminalOrientedForceSplitsSelfExternal selected beta
          | rowSplit selected rest =
    solve
      ( selfOrientedForceCross selected beta
      ∷ externalOrientedForceCross selected beta
      ∷ R539.rowSum selfOrientedForceCross selected rest
      ∷ R539.rowSum externalOrientedForceCross selected rest
      ∷ [])

  columnSplit :
    (items : List Physical.PhysicalTriadIncidence) →
    (selected : Physical.PhysicalTriadIncidence) →
    R539.columnSum H.orientedForceCross items selected
    ≡
    R539.columnSum selfOrientedForceCross items selected
      + R539.columnSum externalOrientedForceCross items selected
  columnSplit [] selected = refl
  columnSplit (alpha ∷ rest) selected
    rewrite terminalOrientedForceSplitsSelfExternal alpha selected
          | columnSplit rest selected =
    solve
      ( selfOrientedForceCross alpha selected
      ∷ externalOrientedForceCross alpha selected
      ∷ R539.columnSum selfOrientedForceCross rest selected
      ∷ R539.columnSum externalOrientedForceCross rest selected
      ∷ [])

  orderedOrientedForceSplitsSelfExternal :
    (items : List Physical.PhysicalTriadIncidence) →
    R539.orderedOffDiagonalSum H.orientedForceCross items
    ≡
    R539.orderedOffDiagonalSum selfOrientedForceCross items
      + R539.orderedOffDiagonalSum externalOrientedForceCross items
  orderedOrientedForceSplitsSelfExternal [] = refl
  orderedOrientedForceSplitsSelfExternal (alpha ∷ rest)
    rewrite rowSplit alpha rest
          | columnSplit rest alpha
          | orderedOrientedForceSplitsSelfExternal rest =
    solve
      ( R539.rowSum selfOrientedForceCross alpha rest
      ∷ R539.rowSum externalOrientedForceCross alpha rest
      ∷ R539.columnSum selfOrientedForceCross rest alpha
      ∷ R539.columnSum externalOrientedForceCross rest alpha
      ∷ R539.orderedOffDiagonalSum selfOrientedForceCross rest
      ∷ R539.orderedOffDiagonalSum externalOrientedForceCross rest
      ∷ [])

------------------------------------------------------------------------
-- Status / frontier.
------------------------------------------------------------------------

round614TerminalOrientedKernelSameObjectWeldClosed : Bool
round614TerminalOrientedKernelSameObjectWeldClosed = true

round614TerminalOrientedKernelSelfExternalSplitClosed : Bool
round614TerminalOrientedKernelSelfExternalSplitClosed = true

round614OrderedOffDiagonalSelfExternalSplitClosed : Bool
round614OrderedOffDiagonalSelfExternalSplitClosed = true

round614SelfOrderedBudgetClosed : Bool
round614SelfOrderedBudgetClosed = false

round614ExternalOrderedBudgetClosed : Bool
round614ExternalOrderedBudgetClosed = false

round614IntroducesEstimate : Bool
round614IntroducesEstimate = false

round614OrderedOffDiagonalSelfExternalSplitClosedIsTrue :
  round614OrderedOffDiagonalSelfExternalSplitClosed ≡ true
round614OrderedOffDiagonalSelfExternalSplitClosedIsTrue = refl

round614IntroducesEstimateIsFalse :
  round614IntroducesEstimate ≡ false
round614IntroducesEstimateIsFalse = refl
