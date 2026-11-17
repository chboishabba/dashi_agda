module DASHI.Physics.Closure.E6HyperformH3H2GapNonIdentificationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.E6HyperformH3H2IncidenceGroundStateExact as Ground
import DASHI.Physics.Closure.E6HyperformH3H2CommonActionBridgeExact as Fibre

------------------------------------------------------------------------
-- THE TWO NUMERICAL GAP-3 RECEIPTS ARE NOT THE SAME OPERATOR
--
-- Around an exact-cover incidence vacuum, moving one H3 patch from its selected
-- saturated H2 star to ANY of its other eight incident H2 faces changes the old
-- occupancy 4->3 and the new occupancy 0->1.  Hence every nontrivial one-patch
-- flip has incidence defect 3.
--
-- On the same nine-state local H2-choice fibre, the intrinsic quadratic
-- displacement distinguishes the eight alternatives into:
--
--   four axial / norm-1 moves with d^2 = 1,
--   four diagonal / norm-2 moves with d^2 = 2.
--
-- Therefore the equality of the two separately computed spectral/defect gaps
-- at the number 3 cannot identify the operators, even up to one Nat-valued
-- overall scale: that would require k*1=3 and k*2=3 simultaneously.
------------------------------------------------------------------------

incidenceOnePatchFlipDefect : Nat
incidenceOnePatchFlipDefect = 3

fibreAxialStepCost : Nat
fibreAxialStepCost = 1

fibreDiagonalStepCost : Nat
fibreDiagonalStepCost = 2

natScaleNoGo :
  (k : Nat) →
  k * fibreAxialStepCost ≡ incidenceOnePatchFlipDefect →
  k * fibreDiagonalStepCost ≡ incidenceOnePatchFlipDefect →
  ⊥
natScaleNoGo zero ()
natScaleNoGo (suc zero) ()
natScaleNoGo (suc (suc zero)) ()
natScaleNoGo (suc (suc (suc zero))) refl ()
natScaleNoGo (suc (suc (suc (suc n)))) ()

record H3H2GapNonIdentificationBoundary : Set where
  constructor h3-h2-gap-non-identification-boundary
  field
    sameNineStateFibreUsed : Bool
    incidenceOnePatchFlipCostThree : Bool
    fibreHasFourNormOneAlternatives : Bool
    fibreHasFourNormTwoAlternatives : Bool
    singleNatScaleIdentificationRefuted : Bool
    equalNumericalGapCreatesSameOperator : Bool
    independentCouplingsRemainAdmissible : Bool
    physicalRelationBetweenCouplingsDerived : Bool
    boundary : String
open H3H2GapNonIdentificationBoundary public

canonicalBoundary : H3H2GapNonIdentificationBoundary
canonicalBoundary =
  h3-h2-gap-non-identification-boundary
    true true true true true false true false
    "The incidence exact-cover defect and the local fibre quadratic live on related H3-H2 data but are not the same local operator: every one-patch incidence flip costs 3, whereas the fibre displacement distinguishes four cost-1 and four cost-2 alternatives. Equal numerical gap 3 therefore creates no same-operator theorem. A physical relation between their coefficients remains an independent dynamical payment."

groundReceipt : Ground.H3H2IncidenceGroundStateLocalReceipt
groundReceipt = Ground.canonicalBoundary

fibreActionBoundary : Fibre.H3H2CommonActionBridgeBoundary
fibreActionBoundary = Fibre.canonicalBoundary
