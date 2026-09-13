module DASHI.Physics.Closure.NSTriadKNFourHelicityComponentMassCollapseRound575Exact where

------------------------------------------------------------------------
-- ROUND575 / FOUR HELICITY CELL MAJORANTS COLLAPSE TO RAW MODAL MASS
--
-- R574 gives, for every physical inner triad a+b=p and each sign pair s,t,
--
--   ||M_st||^2 <= 9 |p|^2 ||u_a^s||^2 ||u_b^t||^2.
--
-- A possible hidden loss is the four-channel expansion itself.  This file
-- removes that ambiguity exactly.  R475 already proves concrete rational L2
-- Pythagoras for the +/- helical decomposition:
--
--   ||u_m||^2 = ||u_m^+||^2 + ||u_m^-||^2.
--
-- Therefore the SUM of the four R574 right-hand sides is exactly
--
--   9 |p|^2 ||u_a||^2 ||u_b||^2.
--
-- No factor 4 is introduced at the majorant level.  This does NOT claim
-- ||M+++M+-+M-++M--||^2 is bounded by that same quantity; cross-channel Gram
-- terms would be needed for that statement.  The intended shortest route is
-- instead to retain the four fixed channels through the nested row/column
-- aggregation and only combine their scalar budgets afterwards.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNRawCurlLowOutputKernelMassRound178Exact as R178
import DASHI.Physics.Closure.NSTriadKNInnerHelicalComponentCommutatorRound571Exact as R571
import DASHI.Physics.Closure.NSTriadKNR106ComponentLowOutputBoundRound574Exact as R574
import DASHI.Physics.Closure.NSTriadKNWeightedHelicalGramOperatorSplitRound475Exact as R475
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2.rationalRealField

module PhysicalCollapse
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (O : Leray.RationalInverseNormOrder E I)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  module C = R571.Componentwise system S L velocityTransverse
  module B = R574.PhysicalComponents E I O system S L velocityTransverse

  mass : Helical.HelicitySign → Z3.FourierMode → ℚ
  mass sign mode = L2.complex3NormSquared (C.component sign mode)

  rawMass : Z3.FourierMode → ℚ
  rawMass mode = L2.complex3NormSquared (Audit.velocity system mode)

  componentMassSplit :
    (mode : Z3.FourierMode) →
    rawMass mode ≡ mass Helical.plus mode + mass Helical.minus mode
  componentMassSplit mode =
    R475.l2NormHelicalSplit E I S L mode
      (Audit.velocity system mode) (velocityTransverse mode)

  fourInputMassProduct : Physical.PhysicalTriadIncidence → ℚ
  fourInputMassProduct tau =
      mass Helical.plus (Physical.p tau) * mass Helical.plus (Physical.q tau)
    + mass Helical.plus (Physical.p tau) * mass Helical.minus (Physical.q tau)
    + mass Helical.minus (Physical.p tau) * mass Helical.plus (Physical.q tau)
    + mass Helical.minus (Physical.p tau) * mass Helical.minus (Physical.q tau)

  fourInputMassProductCollapses :
    (tau : Physical.PhysicalTriadIncidence) →
    fourInputMassProduct tau
    ≡ rawMass (Physical.p tau) * rawMass (Physical.q tau)
  fourInputMassProductCollapses tau =
    let
      pp = mass Helical.plus (Physical.p tau)
      pm = mass Helical.minus (Physical.p tau)
      qp = mass Helical.plus (Physical.q tau)
      qm = mass Helical.minus (Physical.q tau)
      algebra :
        pp * qp + pp * qm + pm * qp + pm * qm
        ≡ (pp + pm) * (qp + qm)
      algebra = solve (pp ∷ pm ∷ qp ∷ qm ∷ [])
    in
    trans algebra
      (cong
        (λ pair → pair)
        (sym
          (cong₂Mul
            (componentMassSplit (Physical.p tau))
            (componentMassSplit (Physical.q tau)))))
    where
    cong₂Mul : ∀ {a b c d : ℚ} → a ≡ b → c ≡ d → a * c ≡ b * d
    cong₂Mul refl refl = refl

  componentMajorant :
    Physical.PhysicalTriadIncidence →
    Helical.HelicitySign → Helical.HelicitySign → ℚ
  componentMajorant tau signP signQ =
    R178.nine * C3.normSquared I (Physical.k tau)
      * mass signP (Physical.p tau)
      * mass signQ (Physical.q tau)

  fourComponentMajorant : Physical.PhysicalTriadIncidence → ℚ
  fourComponentMajorant tau =
      componentMajorant tau Helical.plus Helical.plus
    + componentMajorant tau Helical.plus Helical.minus
    + componentMajorant tau Helical.minus Helical.plus
    + componentMajorant tau Helical.minus Helical.minus

  fourComponentMajorantCollapses :
    (tau : Physical.PhysicalTriadIncidence) →
    fourComponentMajorant tau
    ≡ R178.nine * C3.normSquared I (Physical.k tau)
        * rawMass (Physical.p tau) * rawMass (Physical.q tau)
  fourComponentMajorantCollapses tau =
    let
      scale = R178.nine * C3.normSquared I (Physical.k tau)
      pp = mass Helical.plus (Physical.p tau)
      pm = mass Helical.minus (Physical.p tau)
      qp = mass Helical.plus (Physical.q tau)
      qm = mass Helical.minus (Physical.q tau)
      distribute :
        scale * pp * qp + scale * pp * qm
          + scale * pm * qp + scale * pm * qm
        ≡ scale * (pp * qp + pp * qm + pm * qp + pm * qm)
      distribute = solve (scale ∷ pp ∷ pm ∷ qp ∷ qm ∷ [])
    in
    trans distribute
      (trans
        (cong (scale *_) (fourInputMassProductCollapses tau))
        (solve
          ( scale
          ∷ rawMass (Physical.p tau)
          ∷ rawMass (Physical.q tau) ∷ [])))

  sumFourComponentCellBounds :
    (tau : Physical.PhysicalTriadIncidence) →
    (outputNonzero : Z3.NonZeroMode (Physical.k tau)) →
      L2.complex3NormSquared
        (C.multiplierDifferenceVector tau Helical.plus Helical.plus)
    + L2.complex3NormSquared
        (C.multiplierDifferenceVector tau Helical.plus Helical.minus)
    + L2.complex3NormSquared
        (C.multiplierDifferenceVector tau Helical.minus Helical.plus)
    + L2.complex3NormSquared
        (C.multiplierDifferenceVector tau Helical.minus Helical.minus)
    ≤ R178.nine * C3.normSquared I (Physical.k tau)
        * rawMass (Physical.p tau) * rawMass (Physical.q tau)
  sumFourComponentCellBounds tau outputNonzero =
    let
      bpp = B.componentLowOutputBound tau outputNonzero Helical.plus Helical.plus
      bpm = B.componentLowOutputBound tau outputNonzero Helical.plus Helical.minus
      bmp = B.componentLowOutputBound tau outputNonzero Helical.minus Helical.plus
      bmm = B.componentLowOutputBound tau outputNonzero Helical.minus Helical.minus
      summed :
          L2.complex3NormSquared
            (C.multiplierDifferenceVector tau Helical.plus Helical.plus)
        + L2.complex3NormSquared
            (C.multiplierDifferenceVector tau Helical.plus Helical.minus)
        + L2.complex3NormSquared
            (C.multiplierDifferenceVector tau Helical.minus Helical.plus)
        + L2.complex3NormSquared
            (C.multiplierDifferenceVector tau Helical.minus Helical.minus)
        ≤ fourComponentMajorant tau
      summed = ℚP.+-mono-≤ (ℚP.+-mono-≤ (ℚP.+-mono-≤ bpp bpm) bmp) bmm
    in
    subst
      (λ rhs →
        L2.complex3NormSquared
            (C.multiplierDifferenceVector tau Helical.plus Helical.plus)
        + L2.complex3NormSquared
            (C.multiplierDifferenceVector tau Helical.plus Helical.minus)
        + L2.complex3NormSquared
            (C.multiplierDifferenceVector tau Helical.minus Helical.plus)
        + L2.complex3NormSquared
            (C.multiplierDifferenceVector tau Helical.minus Helical.minus)
        ≤ rhs)
      (fourComponentMajorantCollapses tau)
      summed

------------------------------------------------------------------------
-- Status / BIDI consequence.
------------------------------------------------------------------------

round575FourHelicityMajorantsCollapseToRawModalMass : Bool
round575FourHelicityMajorantsCollapseToRawModalMass = true

round575FourChannelExpansionIntroducesFactorFourInMajorant : Bool
round575FourChannelExpansionIntroducesFactorFourInMajorant = false

round575NormOfFourVectorSumBoundClosed : Bool
round575NormOfFourVectorSumBoundClosed = false

round575RecommendedRouteRetainsChannelIndexThroughAggregation : Bool
round575RecommendedRouteRetainsChannelIndexThroughAggregation = true

round575InnerFibreRowColumnAggregationClosed : Bool
round575InnerFibreRowColumnAggregationClosed = false

round575CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round575CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round575ClayPromotion : Bool
round575ClayPromotion = false

round575FourHelicityMajorantsCollapseToRawModalMassIsTrue :
  round575FourHelicityMajorantsCollapseToRawModalMass ≡ true
round575FourHelicityMajorantsCollapseToRawModalMassIsTrue = refl

round575FourChannelExpansionIntroducesFactorFourInMajorantIsFalse :
  round575FourChannelExpansionIntroducesFactorFourInMajorant ≡ false
round575FourChannelExpansionIntroducesFactorFourInMajorantIsFalse = refl

round575ClayPromotionIsFalse : round575ClayPromotion ≡ false
round575ClayPromotionIsFalse = refl
