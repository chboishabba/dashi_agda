module DASHI.Physics.Closure.NSTriadKNWaleffeOutputHelicitySplitRound286Exact where

------------------------------------------------------------------------
-- ROUND286 / WALEFFE CROSS-POLLINATION WITHOUT A GAUGE-DEPENDENT BASIS
--
-- Waleffe's helical analysis says to keep the helical channels separate before
-- taking transfer magnitudes.  The literal R227 object, however, is not a
-- scalar transfer coefficient: it is the C^3 vector
--
--   A_pq = u_p^+ x u_q^- .
--
-- A_pq is not generically transverse to the output k=p+q, so replacing it by
-- one phase-bearing Waleffe scalar would lose the longitudinal component and
-- would not preserve the R227/R220 Gram mass.
--
-- The repository already owns a gauge-invariant exact substitute for choosing
-- basis vectors h_+(k),h_-(k): first apply the literal Leray projector and then
-- its two output-helicity projectors.  Thus every R227 cell has the exact split
--
--   A_pq = A_pq^{k,+} + A_pq^{k,-} + A_pq^{k,parallel},
--
-- where the first two terms retain complex phase as vectors.  A later scalar
-- Waleffe coordinate may be added only with a phase-fixed basis realization
-- receipt; it is not needed for the first covariance reduction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224

F : C3.RealField _
F = Rational.rationalRealField

mixedCell :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
mixedCell E I S velocity = R224.mixedPlusMinus {E = E} {I = I} S velocity

outputProjectedCell :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
outputProjectedCell E I S velocity tau =
  C3.lerayProject3 E I (Physical.k tau) (mixedCell E I S velocity tau)

outputPlusCell :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
outputPlusCell E I S velocity tau =
  Helical.helicalProjectorPlus E I S (Physical.k tau)
    (mixedCell E I S velocity tau)

outputMinusCell :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
outputMinusCell E I S velocity tau =
  Helical.helicalProjectorMinus E I S (Physical.k tau)
    (mixedCell E I S velocity tau)

outputLongitudinalCell :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
outputLongitudinalCell E I S velocity tau =
  C3.complex3Subtract
    (mixedCell E I S velocity tau)
    (outputProjectedCell E I S velocity tau)

-- Additive identity b + (a-b) = a on the literal rational C^3 carrier.
addSubtractRecover : (a b : C3.Complex3 F) →
  C3.complex3Add b (C3.complex3Subtract a b) ≡ a
addSubtractRecover
    (C3.complex3 ax ay az) (C3.complex3 bx by bz) =
  Field.complex3Ext
    (R.solve 2 (λ a b → b R.⊕ (a R.⊕ (R.⊝ b)) R.⊜ a) refl ax bx)
    (R.solve 2 (λ a b → b R.⊕ (a R.⊕ (R.⊝ b)) R.⊜ a) refl ay by)
    (R.solve 2 (λ a b → b R.⊕ (a R.⊕ (R.⊝ b)) R.⊜ a) refl az bz)
  where module R = Ring.Solver F

projectedCellIsOutputHelicitySum :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (L : Helical.PeriodicHelicalProjectorLaws F E I S) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (tau : Physical.PhysicalTriadIncidence) →
  outputProjectedCell E I S velocity tau
  ≡ C3.complex3Add
      (outputPlusCell E I S velocity tau)
      (outputMinusCell E I S velocity tau)
projectedCellIsOutputHelicitySum E I S L velocity tau =
  sym (Helical.helicalProjectorsSumToLeray L
    (Physical.k tau) (mixedCell E I S velocity tau))

mixedCellIsProjectedPlusLongitudinal :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (tau : Physical.PhysicalTriadIncidence) →
  mixedCell E I S velocity tau
  ≡ C3.complex3Add
      (outputProjectedCell E I S velocity tau)
      (outputLongitudinalCell E I S velocity tau)
mixedCellIsProjectedPlusLongitudinal E I S velocity tau =
  sym (addSubtractRecover
    (mixedCell E I S velocity tau)
    (outputProjectedCell E I S velocity tau))

mixedCellIsOutputHelicityPlusLongitudinal :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (L : Helical.PeriodicHelicalProjectorLaws F E I S) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (tau : Physical.PhysicalTriadIncidence) →
  mixedCell E I S velocity tau
  ≡ C3.complex3Add
      (C3.complex3Add
        (outputPlusCell E I S velocity tau)
        (outputMinusCell E I S velocity tau))
      (outputLongitudinalCell E I S velocity tau)
mixedCellIsOutputHelicityPlusLongitudinal E I S L velocity tau =
  trans
    (mixedCellIsProjectedPlusLongitudinal E I S velocity tau)
    (cong
      (λ projected → C3.complex3Add projected
        (outputLongitudinalCell E I S velocity tau))
      (projectedCellIsOutputHelicitySum E I S L velocity tau))

round286UsesLiteralR227MixedCell : Bool
round286UsesLiteralR227MixedCell = true

round286ScalarWaleffeCoefficientDefinitionallyEqualsRawCell : Bool
round286ScalarWaleffeCoefficientDefinitionallyEqualsRawCell = false

round286GaugeInvariantOutputHelicitySplitClosed : Bool
round286GaugeInvariantOutputHelicitySplitClosed = true

round286LongitudinalComponentRetained : Bool
round286LongitudinalComponentRetained = true

round286PackageAClosed : Bool
round286PackageAClosed = false

round286ClayPromotion : Bool
round286ClayPromotion = false

round286GaugeInvariantOutputHelicitySplitClosedIsTrue :
  round286GaugeInvariantOutputHelicitySplitClosed ≡ true
round286GaugeInvariantOutputHelicitySplitClosedIsTrue = refl

round286ScalarWaleffeCoefficientDefinitionallyEqualsRawCellIsFalse :
  round286ScalarWaleffeCoefficientDefinitionallyEqualsRawCell ≡ false
round286ScalarWaleffeCoefficientDefinitionallyEqualsRawCellIsFalse = refl
