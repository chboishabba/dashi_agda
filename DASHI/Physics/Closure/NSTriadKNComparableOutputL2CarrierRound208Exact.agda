module DASHI.Physics.Closure.NSTriadKNComparableOutputL2CarrierRound208Exact where

------------------------------------------------------------------------
-- ROUND208 / DISTINCT OUTPUTS LIVE IN THE OUTER FOURIER L2 SUM
--
-- Round207 enforces that each compressed CC Gram block is a same-output
-- object.  The physical Fourier norm does not take one C3 norm after summing
-- different outputs; it sums the squared C3 norms output-by-output.
--
-- This module represents exactly that outer carrier for a finite family of
-- fixed-output localized comparable partner blocks.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNPhysicalRawCurlPartnerMassRound187Exact as R187
import DASHI.Physics.Closure.NSTriadKNComparableFixedOutputCarrierRound207Exact as R207

F = R187.F

record ComparableOutputBlockFamily
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I) : Set where
  constructor comparable-output-block-family
  field
    outputs : List Z3.FourierMode
    partnersAt :
      (output : Z3.FourierMode) →
      List (R207.FixedOutputLocalizedComparablePartner system output)

open ComparableOutputBlockFamily public

comparableOutputBlock :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I} →
  ComparableOutputBlockFamily system → Z3.FourierMode → C3.Complex3 F
comparableOutputBlock family output =
  R180.sumCells (R207.fixedOutputPartnerCells (partnersAt family output))

comparableOuterL2Mass :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I} →
  ComparableOutputBlockFamily system → ℚ
comparableOuterL2Mass family =
  L2.finiteComplex3L2NormSquared
    (outputs family)
    (comparableOutputBlock family)

outputBlockMassSum :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I} →
  (family : ComparableOutputBlockFamily system) →
  List Z3.FourierMode → ℚ
outputBlockMassSum family [] = 0ℚ
outputBlockMassSum family (output ∷ rest) =
  L2.complex3NormSquared (comparableOutputBlock family output)
  + outputBlockMassSum family rest

comparableOuterL2MassIsOutputwise :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    (family : ComparableOutputBlockFamily system) →
  comparableOuterL2Mass family
  ≡ outputBlockMassSum family (outputs family)
comparableOuterL2MassIsOutputwise family = refl

round208DistinctOutputsRecombinedByFourierL2 : Bool
round208DistinctOutputsRecombinedByFourierL2 = true

round208CrossOutputGramDebtIntroduced : Bool
round208CrossOutputGramDebtIntroduced = false

round208SameOutputDebtStillRequired : Bool
round208SameOutputDebtStillRequired = true

round208PhysicalCCResidualBudgetClosed : Bool
round208PhysicalCCResidualBudgetClosed = false

round208PackageAClosed : Bool
round208PackageAClosed = false

round208ClayPromotion : Bool
round208ClayPromotion = false

round208DistinctOutputsRecombinedByFourierL2IsTrue :
  round208DistinctOutputsRecombinedByFourierL2 ≡ true
round208DistinctOutputsRecombinedByFourierL2IsTrue = refl

round208CrossOutputGramDebtIntroducedIsFalse :
  round208CrossOutputGramDebtIntroduced ≡ false
round208CrossOutputGramDebtIntroducedIsFalse = refl
