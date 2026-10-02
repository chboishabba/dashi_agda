{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345ActiveHelicalScalarsRound835Exact where

------------------------------------------------------------------------
-- R835 / EXACT ACTIVE 3-4-5 HELICAL SCALAR CALIBRATION
--
-- R834 proves that R829 may prune zero cells before evaluating helical
-- projectors.  Therefore the decision theorem does not need a globally
-- physically normalized rational |k| function.  It only needs the exact
-- rational radii and reciprocals on the eight active modes of the selected
-- 3-4-5 snapshot.
--
-- This owner supplies one executable HelicalModeScalars record:
--
--   |(±3,0,0)| = 3
--   |(0,±4,0)| = 4
--   |(±3,±4,0)| = 5
--
-- with reciprocals 1/3,1/4,1/5 and half=1/2.  Off the selected active set the
-- values are deliberately harmless defaults; R834 is the theorem that makes
-- those defaults irrelevant to the sparse R829 evaluation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_; -[1+_])
open import Data.Rational.Base using (ℚ; _/_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical

F : C3.RealField _
F = Rational.rationalRealField

k₁ k₂ k₃ k₄ k₅ k₆ k₇ k₈ : Z3.FourierMode
k₁ = Z3.mode (-[1+ 2 ]) (-[1+ 3 ]) (+ 0)
k₂ = Z3.mode (-[1+ 2 ]) (+ 0) (+ 0)
k₃ = Z3.mode (-[1+ 2 ]) (+ 4) (+ 0)
k₄ = Z3.mode (+ 0) (-[1+ 3 ]) (+ 0)
k₅ = Z3.mode (+ 0) (+ 4) (+ 0)
k₆ = Z3.mode (+ 3) (-[1+ 3 ]) (+ 0)
k₇ = Z3.mode (+ 3) (+ 0) (+ 0)
k₈ = Z3.mode (+ 3) (+ 4) (+ 0)

choose : Bool → ℚ → ℚ → ℚ
choose true yes no = yes
choose false yes no = no

activeModeNorm : Z3.FourierMode → ℚ
activeModeNorm mode =
  choose (Output.modeEqual mode k₁) 5
  (choose (Output.modeEqual mode k₂) 3
  (choose (Output.modeEqual mode k₃) 5
  (choose (Output.modeEqual mode k₄) 4
  (choose (Output.modeEqual mode k₅) 4
  (choose (Output.modeEqual mode k₆) 5
  (choose (Output.modeEqual mode k₇) 3
  (choose (Output.modeEqual mode k₈) 5 1)))))))

activeInverseModeNorm : Z3.FourierMode → ℚ
activeInverseModeNorm mode =
  choose (Output.modeEqual mode k₁) ((+ 1) / 5)
  (choose (Output.modeEqual mode k₂) ((+ 1) / 3)
  (choose (Output.modeEqual mode k₃) ((+ 1) / 5)
  (choose (Output.modeEqual mode k₄) ((+ 1) / 4)
  (choose (Output.modeEqual mode k₅) ((+ 1) / 4)
  (choose (Output.modeEqual mode k₆) ((+ 1) / 5)
  (choose (Output.modeEqual mode k₇) ((+ 1) / 3)
  (choose (Output.modeEqual mode k₈) ((+ 1) / 5) 1)))))))

selected345HelicalScalars : Helical.HelicalModeScalars F
selected345HelicalScalars = record
  { Helical.modeNorm = activeModeNorm
  ; Helical.inverseModeNorm = activeInverseModeNorm
  ; Helical.half = (+ 1) / 2
  }

norm₁ : activeModeNorm k₁ ≡ 5
norm₁ = refl

norm₂ : activeModeNorm k₂ ≡ 3
norm₂ = refl

norm₃ : activeModeNorm k₃ ≡ 5
norm₃ = refl

norm₄ : activeModeNorm k₄ ≡ 4
norm₄ = refl

norm₅ : activeModeNorm k₅ ≡ 4
norm₅ = refl

norm₆ : activeModeNorm k₆ ≡ 5
norm₆ = refl

norm₇ : activeModeNorm k₇ ≡ 3
norm₇ = refl

norm₈ : activeModeNorm k₈ ≡ 5
norm₈ = refl

inverseNorm₁ : activeInverseModeNorm k₁ ≡ (+ 1) / 5
inverseNorm₁ = refl

inverseNorm₂ : activeInverseModeNorm k₂ ≡ (+ 1) / 3
inverseNorm₂ = refl

inverseNorm₃ : activeInverseModeNorm k₃ ≡ (+ 1) / 5
inverseNorm₃ = refl

inverseNorm₄ : activeInverseModeNorm k₄ ≡ (+ 1) / 4
inverseNorm₄ = refl

inverseNorm₅ : activeInverseModeNorm k₅ ≡ (+ 1) / 4
inverseNorm₅ = refl

inverseNorm₆ : activeInverseModeNorm k₆ ≡ (+ 1) / 5
inverseNorm₆ = refl

inverseNorm₇ : activeInverseModeNorm k₇ ≡ (+ 1) / 3
inverseNorm₇ = refl

inverseNorm₈ : activeInverseModeNorm k₈ ≡ (+ 1) / 5
inverseNorm₈ = refl

halfExact : Helical.half selected345HelicalScalars ≡ (+ 1) / 2
halfExact = refl

round835EightActiveNormsExact : Bool
round835EightActiveNormsExact = true

round835EightActiveReciprocalsExact : Bool
round835EightActiveReciprocalsExact = true

round835GlobalPhysicalNormClaimed : Bool
round835GlobalPhysicalNormClaimed = false

round835SparsePruningRequiredForOffSupportIrrelevance : Bool
round835SparsePruningRequiredForOffSupportIrrelevance = true

round835ClayPromotion : Bool
round835ClayPromotion = false

round835EightActiveNormsExactIsTrue :
  round835EightActiveNormsExact ≡ true
round835EightActiveNormsExactIsTrue = refl

round835GlobalPhysicalNormClaimedIsFalse :
  round835GlobalPhysicalNormClaimed ≡ false
round835GlobalPhysicalNormClaimedIsFalse = refl
