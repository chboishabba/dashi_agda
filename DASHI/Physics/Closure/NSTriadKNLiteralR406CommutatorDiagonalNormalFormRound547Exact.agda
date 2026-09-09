module DASHI.Physics.Closure.NSTriadKNLiteralR406CommutatorDiagonalNormalFormRound547Exact where

------------------------------------------------------------------------
-- ROUND547 / LITERAL FIXED-OUTPUT R406 REMAINDER NORMAL FORM
--
-- Compose the finite exact chain:
--
--   R538  physical pair scalar is symmetric;
--   R539  ordered offdiag = 2 * unordered;
--   R540  unordered = literal R396/R385 weighted remainder;
--   R543  full square = diagonal + ordered offdiag;
--   R545  every complete spectator row factors through R294 commutator and
--         weighted amplitude folds;
--   R546  full square = sum of complete spectator rows.
--
-- Therefore on one literal physical output fibre:
--
--   FactoredFull = Diagonal + 2 * LiteralWeightedRemainder.
--
-- This is an exact representation theorem.  It does not bound either the
-- factored full term or the diagonal and introduces no absolute value.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNFiniteWeightedGramFluxAggregationRound385Exact as R385
import DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact as R396
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543
import DASHI.Physics.Closure.NSTriadKNLiteralR396OrderedOffDiagonalRemainderRound540Exact as R540
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventRowFactorizationRound545Exact as R545
import DASHI.Physics.Closure.NSTriadKNFullSquareAsSpectatorRowsRound546Exact as R546

F : C3.RealField _
F = Rational.rationalRealField

module NormalForm
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  module R = R545.Row physicalSystem S
  module O = R540.LiteralOrdered physicalSystem S

  system = Field30.finiteSystem physicalSystem

  factoredRow :
    Z3.FourierMode → Physical.PhysicalTriadIncidence → ℚ
  factoredRow output beta =
    let
      items = Output.physicalOutputFiber (Audit.cutoff system) output
      C = R224.foldVector (R.Weighted.Force.commutator beta) items
      A = R224.foldVector (R.Weighted.Amp.amplitude beta) items
      fourC = C3.complex3Add (C3.complex3Add C C) (C3.complex3Add C C)
      fourA = C3.complex3Add (C3.complex3Add A A) (C3.complex3Add A A)
    in
    R291.two *
      (R179.realHermitianCross fourC (R.doubleCell beta)
      + R179.realHermitianCross fourA (R.D.doubleForcing beta))

  factoredFull :
    Z3.FourierMode → List Physical.PhysicalTriadIncidence → ℚ
  factoredFull output [] = 0ℚ
  factoredFull output (beta ∷ rest) =
    factoredRow output beta + factoredFull output rest

  rowDefinitionsAgree :
    (beta : Physical.PhysicalTriadIncidence) →
    (items : List Physical.PhysicalTriadIncidence) →
    R546.spectatorRow R.pairScalar beta items ≡ R.spectatorRow beta items
  rowDefinitionsAgree beta [] = refl
  rowDefinitionsAgree beta (alpha ∷ rest) =
    cong₂ _+_ refl (rowDefinitionsAgree beta rest)

  allRowsFactor :
    (output : Z3.FourierMode) →
    (betas : List Physical.PhysicalTriadIncidence) →
    let items = Output.physicalOutputFiber (Audit.cutoff system) output in
    R546.allSpectatorRows R.pairScalar items betas
    ≡ factoredFull output betas
  allRowsFactor output [] = refl
  allRowsFactor output (beta ∷ rest) =
    let
      items = Output.physicalOutputFiber (Audit.cutoff system) output
      rowToR = rowDefinitionsAgree beta items
      rowToFactored = R.fixedOutputSpectatorRowFactorsThroughR294 output beta
    in
    cong₂ _+_
      (trans rowToR rowToFactored)
      (allRowsFactor output rest)

  fullSquareIsFactoredFull :
    (output : Z3.FourierMode) →
    let items = Output.physicalOutputFiber (Audit.cutoff system) output in
    R543.fullSquareSum R.pairScalar items ≡ factoredFull output items
  fullSquareIsFactoredFull output =
    let items = Output.physicalOutputFiber (Audit.cutoff system) output in
    trans
      (R546.fullSquareIsAllSpectatorRows R.pairScalar items)
      (allRowsFactor output items)

  factoredFullIsDiagonalPlusTwoLiteralRemainder :
    (output : Z3.FourierMode) →
    let items = Output.physicalOutputFiber (Audit.cutoff system) output in
    (positive : O.E.PairRatePositiveOn items) →
    factoredFull output items
    ≡ R543.diagonalSum R.pairScalar items
      + R539.two * R385.sumWeightedRemainder (O.E.allR290Pairs items positive)
  factoredFullIsDiagonalPlusTwoLiteralRemainder output positive =
    let
      items = Output.physicalOutputFiber (Audit.cutoff system) output
    in
    trans
      (sym (fullSquareIsFactoredFull output))
      (trans
        (R543.fullSquareIsDiagonalPlusOrderedOffDiagonal R.pairScalar items)
        (cong
          (R543.diagonalSum R.pairScalar items +_)
          (O.orderedOffDiagonalIsTwoLiteralWeightedRemainder items positive)))

round547LiteralFixedOutputNormalFormClosed : Bool
round547LiteralFixedOutputNormalFormClosed = true

round547NonseparabilityBlocksR294 : Bool
round547NonseparabilityBlocksR294 = false

round547DiagonalAutomaticallyPaid : Bool
round547DiagonalAutomaticallyPaid = false

round547FactoredFullSpacetimeBoundClosed : Bool
round547FactoredFullSpacetimeBoundClosed = false

round547LiteralR406SignedCrossPaymentClosed : Bool
round547LiteralR406SignedCrossPaymentClosed = false

round547ClayPromotion : Bool
round547ClayPromotion = false

round547LiteralFixedOutputNormalFormClosedIsTrue :
  round547LiteralFixedOutputNormalFormClosed ≡ true
round547LiteralFixedOutputNormalFormClosedIsTrue = refl

round547NonseparabilityBlocksR294IsFalse :
  round547NonseparabilityBlocksR294 ≡ false
round547NonseparabilityBlocksR294IsFalse = refl

round547ClayPromotionIsFalse : round547ClayPromotion ≡ false
round547ClayPromotionIsFalse = refl
