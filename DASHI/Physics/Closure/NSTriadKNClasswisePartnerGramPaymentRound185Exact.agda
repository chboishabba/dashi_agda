module DASHI.Physics.Closure.NSTriadKNClasswisePartnerGramPaymentRound185Exact where

------------------------------------------------------------------------
-- ROUND185 / CLASSWISE GRAM PAYMENT COMPILER
--
-- Round180 gives, for every signed finite fibre,
--
--   ||Σ cells||² = Σ ||cell||² + GramDebt.
--
-- Round184 shows that once the physical partner-compressed cells have been
-- routed into the three partner-invariant Bony blocks
--
--   FL = LH ∪ HL,  HH = HH -> low,  CC = comparable,
--
-- the three already-summed class vectors may be recombined with a universal
-- factor 3.  Consequently the global between-class Gram debt does NOT need a
-- sign theorem.  It is enough to pay the signed Gram debt inside each class.
--
-- This module composes those two exact owners.  No fibre cardinality enters.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNThreeClassFibreQuadraticRound184Exact as R184
import DASHI.Physics.Closure.NSTriadKNRawCurlLowOutputKernelMassRound178Exact as R178

F = R178.F

record ThreeClassSignedFibre : Set where
  constructor three-class-signed-fibre
  field
    farLowCells highHighCells comparableCells : List (C3.Complex3 F)

open ThreeClassSignedFibre public

farLowSum highHighSum comparableSum : ThreeClassSignedFibre → C3.Complex3 F
farLowSum fibre = R180.sumCells (farLowCells fibre)
highHighSum fibre = R180.sumCells (highHighCells fibre)
comparableSum fibre = R180.sumCells (comparableCells fibre)

globalThreeClassSum : ThreeClassSignedFibre → C3.Complex3 F
globalThreeClassSum fibre =
  R184.threeClassTotal
    (farLowSum fibre)
    (highHighSum fibre)
    (comparableSum fibre)

classCellMass : ThreeClassSignedFibre → ℚ
classCellMass fibre =
  R180.cellMassSum (farLowCells fibre)
  + R180.cellMassSum (highHighCells fibre)
  + R180.cellMassSum (comparableCells fibre)

record ClasswiseSignedGramPayment (fibre : ThreeClassSignedFibre) : Set where
  constructor classwise-signed-gram-payment
  field
    farLowDebtPaid : R180.gramDebt (farLowCells fibre) ≤ 0ℚ
    highHighDebtPaid : R180.gramDebt (highHighCells fibre) ≤ 0ℚ
    comparableDebtPaid : R180.gramDebt (comparableCells fibre) ≤ 0ℚ

open ClasswiseSignedGramPayment public

classwisePaymentClosesGlobalFibre :
  (fibre : ThreeClassSignedFibre) →
  ClasswiseSignedGramPayment fibre →
  L2.complex3NormSquared (globalThreeClassSum fibre)
  ≤ R178.three * classCellMass fibre
classwisePaymentClosesGlobalFibre fibre payment =
  let
    farLowBound :
      L2.complex3NormSquared (farLowSum fibre)
      ≤ R180.cellMassSum (farLowCells fibre)
    farLowBound =
      R180.nonpositiveGramDebtClosesFibre
        (farLowCells fibre)
        (farLowDebtPaid payment)

    highHighBound :
      L2.complex3NormSquared (highHighSum fibre)
      ≤ R180.cellMassSum (highHighCells fibre)
    highHighBound =
      R180.nonpositiveGramDebtClosesFibre
        (highHighCells fibre)
        (highHighDebtPaid payment)

    comparableBound :
      L2.complex3NormSquared (comparableSum fibre)
      ≤ R180.cellMassSum (comparableCells fibre)
    comparableBound =
      R180.nonpositiveGramDebtClosesFibre
        (comparableCells fibre)
        (comparableDebtPaid payment)
  in
  R184.threeClassPaidQuadraticBound
    (farLowSum fibre)
    (highHighSum fibre)
    (comparableSum fibre)
    (R180.cellMassSum (farLowCells fibre))
    (R180.cellMassSum (highHighCells fibre))
    (R180.cellMassSum (comparableCells fibre))
    farLowBound highHighBound comparableBound

round185CrossClassDebtNeedsSeparatePayment : Bool
round185CrossClassDebtNeedsSeparatePayment = false

round185OnlyThreeWithinClassDebtsRemain : Bool
round185OnlyThreeWithinClassDebtsRemain = true

round185NoFibreCardinalityFactor : Bool
round185NoFibreCardinalityFactor = true

round185PhysicalWithinClassDebtsPaid : Bool
round185PhysicalWithinClassDebtsPaid = false

round185PackageAClosed : Bool
round185PackageAClosed = false

round185ClayPromotion : Bool
round185ClayPromotion = false
