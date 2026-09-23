{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNSelfEnergyCancellationWeightNoGoRound629Exact where

------------------------------------------------------------------------
-- ROUND629 / UNWEIGHTED THREE-LEG CONSERVATION DOES NOT FORCE WEIGHTED ZERO
--
-- R95 proves exact selected-triad self-energy conservation:
--
--   T0 + T1 + T2 = 0.
--
-- R624/R628, however, consume a spectator/resolvent-weighted nested Hermitian
-- scalar, not the unweighted modal-energy sum.  The existing weighted-defect
-- algebra already shows that a conserved triple leaves weight-difference terms.
--
-- This owner adds a concrete rational countermodel so the invalid shortcut
--
--   unweighted conservation  ==>  arbitrary weighted sum = 0
--
-- cannot be reintroduced later.
--
-- This is a logical/algebraic firewall only.  It does NOT identify the R628
-- self multiplier row with this toy triple and does NOT close or refute the
-- physical signed estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≢_; trans)

import DASHI.Physics.Closure.NSTriadKNCyclicConservationWeightedDefectBidiExact as Weighted

counterexampleTriple : Weighted.CyclicTransferTriple
counterexampleTriple = record
  { Weighted.T0 = 1ℚ
  ; Weighted.T1 = 0ℚ
  ; Weighted.T2 = 0ℚ - 1ℚ
  ; Weighted.thirdFromConservation = solve []
  }

counterexampleUnweightedConservation :
  Weighted.T0 counterexampleTriple
    + Weighted.T1 counterexampleTriple
    + Weighted.T2 counterexampleTriple
  ≡ 0ℚ
counterexampleUnweightedConservation = solve []

counterexampleWeightedSum :
  Weighted.weightedCyclicSum 1ℚ 0ℚ 0ℚ counterexampleTriple
  ≡ 1ℚ
counterexampleWeightedSum = solve []

oneNotZero : 1ℚ ≢ 0ℚ
oneNotZero ()

counterexampleWeightedSumNonzero :
  Weighted.weightedCyclicSum 1ℚ 0ℚ 0ℚ counterexampleTriple
  ≢ 0ℚ
counterexampleWeightedSumNonzero equality =
  oneNotZero (trans (sym counterexampleWeightedSum) equality)

------------------------------------------------------------------------
-- Status / boundary.
------------------------------------------------------------------------

round629UnweightedCyclicConservationCountermodelConstructed : Bool
round629UnweightedCyclicConservationCountermodelConstructed = true

round629ArbitraryWeightedCancellationFromR95Admissible : Bool
round629ArbitraryWeightedCancellationFromR95Admissible = false

round629SameObjectWeightDefectWeldStillRequired : Bool
round629SameObjectWeightDefectWeldStillRequired = true

round629ClaimsPhysicalR628SelfBudgetImpossible : Bool
round629ClaimsPhysicalR628SelfBudgetImpossible = false

round629IntroducesEstimate : Bool
round629IntroducesEstimate = false

round629UnweightedCyclicConservationCountermodelConstructedIsTrue :
  round629UnweightedCyclicConservationCountermodelConstructed ≡ true
round629UnweightedCyclicConservationCountermodelConstructedIsTrue = refl

round629ArbitraryWeightedCancellationFromR95AdmissibleIsFalse :
  round629ArbitraryWeightedCancellationFromR95Admissible ≡ false
round629ArbitraryWeightedCancellationFromR95AdmissibleIsFalse = refl

round629SameObjectWeightDefectWeldStillRequiredIsTrue :
  round629SameObjectWeightDefectWeldStillRequired ≡ true
round629SameObjectWeightDefectWeldStillRequiredIsTrue = refl

round629ClaimsPhysicalR628SelfBudgetImpossibleIsFalse :
  round629ClaimsPhysicalR628SelfBudgetImpossible ≡ false
round629ClaimsPhysicalR628SelfBudgetImpossibleIsFalse = refl

round629IntroducesEstimateIsFalse :
  round629IntroducesEstimate ≡ false
round629IntroducesEstimateIsFalse = refl
