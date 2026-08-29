module DASHI.Physics.Closure.NSTriadKNExternalPureCommutatorBonyWeldRound123Exact where

------------------------------------------------------------------------
-- ROUND123 / END-TO-END EXACT CARRIER WELD
--
-- Round122 proves, on the complete physical cutoff enumeration,
--
--   2 * (full quartic fold) = fold (paired pure commutator cell).
--
-- Round121 proves that every signed incidence fold is exactly the sum of its
-- four authoritative Bony-filtered class folds.  Composing the two removes the
-- last finite carrier/reindexing ambiguity before the analytic estimate:
--
--   2 * full quartic fold
--     = LH(commutator)
--     + HL(commutator)
--     + HH->low(commutator)
--     + comparable(commutator).
--
-- No cellwise absolute value, matching hypothesis, shell-cardinality factor,
-- orbit quotient, or cutoff-dependent counting constant appears in this weld.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNExternalPureCommutatorPartnerRound120Exact as R120
import DASHI.Physics.Closure.NSTriadKNExternalPureCommutatorBonySumRound121Exact as R121
import DASHI.Physics.Closure.NSTriadKNExternalPureCommutatorSwapPairingRound122Exact as R122

pureCommutatorBonyFold :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (helical : ∀ tau → R120.PhysicalHelicalOutputPair system tau)
    (testCross : C3.Complex3 F)
    (cutoff : Nat) →
  C3.Complex F
pureCommutatorBonyFold system helical testCross cutoff =
  R121.fourWayBonyFold
    (R122.pairedPureCommutatorValue system helical testCross)
    (Physical.physicalTriadEnumeration cutoff)

twiceFullQuarticFoldEqualsFourWayPureCommutatorBonyFold :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (helical : ∀ tau → R120.PhysicalHelicalOutputPair system tau)
    (testCross : C3.Complex3 F)
    (cutoff : Nat) →
  C3.complexAdd
    (R122.foldComplex (R122.quarticValue system testCross)
      (Physical.physicalTriadEnumeration cutoff))
    (R122.foldComplex (R122.quarticValue system testCross)
      (Physical.physicalTriadEnumeration cutoff))
  ≡ pureCommutatorBonyFold system helical testCross cutoff
twiceFullQuarticFoldEqualsFourWayPureCommutatorBonyFold
    system helical testCross cutoff =
  trans
    (R122.twiceFullQuarticFoldEqualsPureCommutatorFold
      system helical testCross cutoff)
    (R121.foldComplexEqualsFourWayBonyFold
      (R122.pairedPureCommutatorValue system helical testCross)
      (Physical.physicalTriadEnumeration cutoff))

round123FullPhysicalToPureCommutatorBonyWeldClosed : Bool
round123FullPhysicalToPureCommutatorBonyWeldClosed = true

round123CellwiseAbsoluteValueIntroduced : Bool
round123CellwiseAbsoluteValueIntroduced = false

round123MatchingOrCardinalityHypothesisIntroduced : Bool
round123MatchingOrCardinalityHypothesisIntroduced = false

round123FarLowLHHLPaymentClosed : Bool
round123FarLowLHHLPaymentClosed = false

round123HighHighNearDiagonalPaymentClosed : Bool
round123HighHighNearDiagonalPaymentClosed = false

round123ComparableCriticalPaymentClosed : Bool
round123ComparableCriticalPaymentClosed = false

round123FullCriticalCommutatorPaymentClosed : Bool
round123FullCriticalCommutatorPaymentClosed = false

round123FullPhysicalToPureCommutatorBonyWeldClosedIsTrue :
  round123FullPhysicalToPureCommutatorBonyWeldClosed ≡ true
round123FullPhysicalToPureCommutatorBonyWeldClosedIsTrue = refl

round123CellwiseAbsoluteValueIntroducedIsFalse :
  round123CellwiseAbsoluteValueIntroduced ≡ false
round123CellwiseAbsoluteValueIntroducedIsFalse = refl

round123FullCriticalCommutatorPaymentClosedIsFalse :
  round123FullCriticalCommutatorPaymentClosed ≡ false
round123FullCriticalCommutatorPaymentClosedIsFalse = refl
