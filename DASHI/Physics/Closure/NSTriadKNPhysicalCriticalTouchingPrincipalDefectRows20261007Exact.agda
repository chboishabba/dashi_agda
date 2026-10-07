module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingPrincipalDefectRows20261007Exact where

------------------------------------------------------------------------
-- POSITIVE B4 / LITERAL PRINCIPAL-DEFECT ROW SPLIT / 2026-10-07
--
-- This closes only the first genuinely analytic B4 prerequisite from the
-- terminal max-cut: construct P and D on the SAME literal critical-touching
-- row carrier and prove
--
--   S_crit = P + D.
--
-- We choose the canonical tag split already present in the live R236 routing:
--
--   principal : Core-Core rows,
--   defect    : DFL-Core and DHH-Core rows (either orientation).
--
-- No norm, estimate, shell count, new scalar observable, or synthetic carrier
-- is introduced.  The two required strict inequalities remain open.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_; _++_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalParabolicCriticalRegionRoutingExact as Routing
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionLiteralPairExtractionMaxCutExact as Rows
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingLiteralRowsMaxCutExact as Critical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceLiveExact as LiveOwner
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceBonyLiveExact as RateLive
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalRegionPaymentLiveExact as Pay

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- One-pair partition of the literal critical-touching selector.
------------------------------------------------------------------------

principalRoute :
  Physical.PhysicalTriadIncidence →
  Physical.PhysicalTriadIncidence → List Rows.LiteralPairRow
principalRoute alpha beta
  with Routing.criticalRegionTag alpha | Routing.criticalRegionTag beta
... | Routing.deepFarLowRegion | Routing.deepFarLowRegion = []
... | Routing.deepFarLowRegion | Routing.deepHighHighRegion = []
... | Routing.deepFarLowRegion | Routing.criticalCoreRegion = []
... | Routing.deepHighHighRegion | Routing.deepFarLowRegion = []
... | Routing.deepHighHighRegion | Routing.deepHighHighRegion = []
... | Routing.deepHighHighRegion | Routing.criticalCoreRegion = []
... | Routing.criticalCoreRegion | Routing.deepFarLowRegion = []
... | Routing.criticalCoreRegion | Routing.deepHighHighRegion = []
... | Routing.criticalCoreRegion | Routing.criticalCoreRegion =
  Rows.literal-pair-row alpha beta ∷ []

defectRoute :
  Physical.PhysicalTriadIncidence →
  Physical.PhysicalTriadIncidence → List Rows.LiteralPairRow
defectRoute alpha beta
  with Routing.criticalRegionTag alpha | Routing.criticalRegionTag beta
... | Routing.deepFarLowRegion | Routing.deepFarLowRegion = []
... | Routing.deepFarLowRegion | Routing.deepHighHighRegion = []
... | Routing.deepFarLowRegion | Routing.criticalCoreRegion =
  Rows.literal-pair-row alpha beta ∷ []
... | Routing.deepHighHighRegion | Routing.deepFarLowRegion = []
... | Routing.deepHighHighRegion | Routing.deepHighHighRegion = []
... | Routing.deepHighHighRegion | Routing.criticalCoreRegion =
  Rows.literal-pair-row alpha beta ∷ []
... | Routing.criticalCoreRegion | Routing.deepFarLowRegion =
  Rows.literal-pair-row alpha beta ∷ []
... | Routing.criticalCoreRegion | Routing.deepHighHighRegion =
  Rows.literal-pair-row alpha beta ∷ []
... | Routing.criticalCoreRegion | Routing.criticalCoreRegion = []

criticalRouteSumSplit :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Rows.sumRows rate work (Critical.criticalTouchingRoute alpha beta)
  ≡ Rows.sumRows rate work (principalRoute alpha beta)
    + Rows.sumRows rate work (defectRoute alpha beta)
criticalRouteSumSplit rate work alpha beta
  with Routing.criticalRegionTag alpha | Routing.criticalRegionTag beta
... | Routing.deepFarLowRegion | Routing.deepFarLowRegion = solve []
... | Routing.deepFarLowRegion | Routing.deepHighHighRegion = solve []
... | Routing.deepFarLowRegion | Routing.criticalCoreRegion = solve []
... | Routing.deepHighHighRegion | Routing.deepFarLowRegion = solve []
... | Routing.deepHighHighRegion | Routing.deepHighHighRegion = solve []
... | Routing.deepHighHighRegion | Routing.criticalCoreRegion = solve []
... | Routing.criticalCoreRegion | Routing.deepFarLowRegion = solve []
... | Routing.criticalCoreRegion | Routing.deepHighHighRegion = solve []
... | Routing.criticalCoreRegion | Routing.criticalCoreRegion = solve []

------------------------------------------------------------------------
-- Replay the same unordered-pair recursion for principal and defect rows.
------------------------------------------------------------------------

principalAgainst :
  Physical.PhysicalTriadIncidence →
  List Physical.PhysicalTriadIncidence → List Rows.LiteralPairRow
principalAgainst head [] = []
principalAgainst head (x ∷ xs) =
  principalRoute head x ++ principalAgainst head xs

defectAgainst :
  Physical.PhysicalTriadIncidence →
  List Physical.PhysicalTriadIncidence → List Rows.LiteralPairRow
defectAgainst head [] = []
defectAgainst head (x ∷ xs) =
  defectRoute head x ++ defectAgainst head xs

principalRows : List Physical.PhysicalTriadIncidence → List Rows.LiteralPairRow
principalRows [] = []
principalRows (head ∷ rest) = principalAgainst head rest ++ principalRows rest

defectRows : List Physical.PhysicalTriadIncidence → List Rows.LiteralPairRow
defectRows [] = []
defectRows (head ∷ rest) = defectAgainst head rest ++ defectRows rest

criticalAgainstSumSplit :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (head : Physical.PhysicalTriadIncidence) →
  (rest : List Physical.PhysicalTriadIncidence) →
  Rows.sumRows rate work (Critical.criticalTouchingAgainst head rest)
  ≡ Rows.sumRows rate work (principalAgainst head rest)
    + Rows.sumRows rate work (defectAgainst head rest)
criticalAgainstSumSplit rate work head [] = solve []
criticalAgainstSumSplit rate work head (x ∷ xs)
  rewrite Rows.sumRowsAppend rate work
            (Critical.criticalTouchingRoute head x)
            (Critical.criticalTouchingAgainst head xs)
        | Rows.sumRowsAppend rate work
            (principalRoute head x)
            (principalAgainst head xs)
        | Rows.sumRowsAppend rate work
            (defectRoute head x)
            (defectAgainst head xs)
        | criticalRouteSumSplit rate work head x
        | criticalAgainstSumSplit rate work head xs = solve []

criticalRowsSumSplit :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (items : List Physical.PhysicalTriadIncidence) →
  Rows.sumRows rate work (Critical.criticalTouchingRows items)
  ≡ Rows.sumRows rate work (principalRows items)
    + Rows.sumRows rate work (defectRows items)
criticalRowsSumSplit rate work [] = solve []
criticalRowsSumSplit rate work (head ∷ rest)
  rewrite Rows.sumRowsAppend rate work
            (Critical.criticalTouchingAgainst head rest)
            (Critical.criticalTouchingRows rest)
        | Rows.sumRowsAppend rate work
            (principalAgainst head rest)
            (principalRows rest)
        | Rows.sumRowsAppend rate work
            (defectAgainst head rest)
            (defectRows rest)
        | criticalAgainstSumSplit rate work head rest
        | criticalRowsSumSplit rate work rest = solve []

------------------------------------------------------------------------
-- Live physical same-object split.
------------------------------------------------------------------------

module LivePrincipalDefect
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module Live = LiveOwner.Live physicalSystem S
  module Rate = RateLive.LiveBony physicalSystem S output
  module C = Critical.LiveCriticalRows physicalSystem S output
  module P = Pay.LiveRegionPayment physicalSystem S output

  items : List Physical.PhysicalTriadIncidence
  items = Live.fibre output

  principalLiteralRows : List Rows.LiteralPairRow
  principalLiteralRows = principalRows items

  defectLiteralRows : List Rows.LiteralPairRow
  defectLiteralRows = defectRows items

  principal : ℚ
  principal = Rows.sumRows Rate.inputMass (Live.work output) principalLiteralRows

  defect : ℚ
  defect = Rows.sumRows Rate.inputMass (Live.work output) defectLiteralRows

  literalRowSumSplit : C.rowSum ≡ principal + defect
  literalRowSumSplit =
    criticalRowsSumSplit Rate.inputMass (Live.work output) items

  liveCriticalTouchingSplit : P.criticalTouchingSigned ≡ principal + defect
  liveCriticalTouchingSplit =
    trans C.liveCriticalTouchingIsLiteralRows literalRowSumSplit

------------------------------------------------------------------------
-- Status: decomposition is closed; estimates are not.
------------------------------------------------------------------------

b4LiteralPrincipalDefectSplitClosed : Bool
b4LiteralPrincipalDefectSplitClosed = true

b4PrincipalIsLiteralCoreCoreRows : Bool
b4PrincipalIsLiteralCoreCoreRows = true

b4DefectIsLiteralCoreNoncoreRows : Bool
b4DefectIsLiteralCoreNoncoreRows = true

b4PrincipalPhysicalEstimateClosedHere : Bool
b4PrincipalPhysicalEstimateClosedHere = false

b4DefectPhysicalEstimateClosedHere : Bool
b4DefectPhysicalEstimateClosedHere = false

b4SplitIntroducesEstimate : Bool
b4SplitIntroducesEstimate = false

clayPromotion : Bool
clayPromotion = false

b4LiteralPrincipalDefectSplitClosedIsTrue :
  b4LiteralPrincipalDefectSplitClosed ≡ true
b4LiteralPrincipalDefectSplitClosedIsTrue = refl

b4PrincipalPhysicalEstimateClosedHereIsFalse :
  b4PrincipalPhysicalEstimateClosedHere ≡ false
b4PrincipalPhysicalEstimateClosedHereIsFalse = refl

b4DefectPhysicalEstimateClosedHereIsFalse :
  b4DefectPhysicalEstimateClosedHere ≡ false
b4DefectPhysicalEstimateClosedHereIsFalse = refl
