module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalDeepBlocksFromLiteralRowsMaxCutExact where

------------------------------------------------------------------------
-- POSITIVE B1-B3 / EXACT LIVE-BLOCK SAME-OBJECT FIELDS FROM LITERAL ROWS
--
-- The three analytic payment records historically asked their producers to
-- restate two logically different facts at once:
--
--   (a) the live R236 scalar is the selected literal physical pair family;
--   (b) that family is paid by shell/Bernstein/null/L2 estimates.
--
-- The new literal-row extractor closes (a) exactly.  This owner therefore
-- compiles row-paying analytic data into the existing B1/B2/B3 records.  After
-- this cut, analytic producers never need to assert another live-block
-- same-object equality; they only have to pay the already-extracted rows.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceLiveExact as LiveOwner
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceBonyLiveExact as RateLive
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionLiteralPairExtractionMaxCutExact as Extract
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalDeepFarLowLiteralInfinityShellPaymentExact as B1
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalDeepFarLowDeepHHFractionalShellPaymentExact as B2
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalDeepHHFractionalShellPaymentExact as B3

F : C3.RealField _
F = Rational.rationalRealField

module FromLiteralRows
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module Live = LiveOwner.Live physicalSystem S
  module Rate = RateLive.LiveBony physicalSystem S output
  module X = Extract.LiveExtraction physicalSystem S output
  module FF = B1.LiteralDeepFarLowPayment physicalSystem S output
  module FH = B2.DeepCrossPayment physicalSystem S output
  module HH = B3.DeepHHPayment physicalSystem S output

  rowSum : List Extract.LiteralPairRow → ℚ
  rowSum = Extract.sumRows Rate.inputMass (Live.work output)

  ----------------------------------------------------------------------
  -- B1.
  ----------------------------------------------------------------------

  record B1LiteralRowPayment : Set₁ where
    constructor b1-literal-row-payment
    field
      receipts : List FF.LiteralShellReceipt
      coefficient localED : ℚ

      shellMassesAreExtractedRows :
        FF.sumShellMass receipts ≡ rowSum X.b1Rows

      shellBudgetsPaidByLocalED :
        FF.sumShellBudget receipts ≤ coefficient * localED

  open B1LiteralRowPayment public

  b1RowsBuildExistingLeaf :
    B1LiteralRowPayment → FF.PhysicalDeepFarLowLiteralShellData
  b1RowsBuildExistingLeaf D = record
    { FF.receipts = receipts D
    ; FF.coefficient = coefficient D
    ; FF.localED = localED D
    ; FF.liveBlockIsLiteralShellMass =
        trans X.b1LiveBlockIsLiteralRows
          (sym (shellMassesAreExtractedRows D))
    ; FF.literalShellBudgetsPaidByLocalED =
        shellBudgetsPaidByLocalED D
    }

  ----------------------------------------------------------------------
  -- B2.
  ----------------------------------------------------------------------

  record B2LiteralRowPayment : Set where
    constructor b2-literal-row-payment
    field
      receipts : List FH.ShellPairReceipt
      coefficient localED : ℚ

      shellPairMassesAreExtractedRows :
        FH.sumSignedMass receipts ≡ rowSum X.b2Rows

      shellPairBudgetsPaidByLocalED :
        FH.sumBudget receipts ≤ coefficient * localED

  open B2LiteralRowPayment public

  b2RowsBuildExistingLeaf :
    B2LiteralRowPayment → FH.PhysicalDeepFarLowDeepHHFractionalShellData
  b2RowsBuildExistingLeaf D = record
    { FH.receipts = receipts D
    ; FH.coefficient = coefficient D
    ; FH.localED = localED D
    ; FH.liveBlockIsShellPairSum =
        trans X.b2LiveBlockIsLiteralRows
          (sym (shellPairMassesAreExtractedRows D))
    ; FH.shellPairBudgetsPaidByLocalED =
        shellPairBudgetsPaidByLocalED D
    }

  ----------------------------------------------------------------------
  -- B3.
  ----------------------------------------------------------------------

  record B3LiteralRowPayment : Set where
    constructor b3-literal-row-payment
    field
      receipts : List HH.ShellReceipt
      coefficient localED : ℚ

      shellMassesAreExtractedRows :
        HH.sumSignedMass receipts ≡ rowSum X.b3Rows

      shellBudgetsPaidByLocalED :
        HH.sumBudget receipts ≤ coefficient * localED

  open B3LiteralRowPayment public

  b3RowsBuildExistingLeaf :
    B3LiteralRowPayment → HH.PhysicalDeepHHFractionalShellData
  b3RowsBuildExistingLeaf D = record
    { HH.receipts = receipts D
    ; HH.coefficient = coefficient D
    ; HH.localED = localED D
    ; HH.liveBlockIsShellSum =
        trans X.b3LiveBlockIsLiteralRows
          (sym (shellMassesAreExtractedRows D))
    ; HH.shellBudgetsPaidByLocalED =
        shellBudgetsPaidByLocalED D
    }

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

b1B3LiveBlockSameObjectFieldsCompiledFromRows : Bool
b1B3LiveBlockSameObjectFieldsCompiledFromRows = true

b1B3LiteralRowsCarryPhysicalShellProvenance : Bool
b1B3LiteralRowsCarryPhysicalShellProvenance = true

b1B3RowsToAnalyticReceiptsClosedHere : Bool
b1B3RowsToAnalyticReceiptsClosedHere = false

b1B3IntroducesEstimate : Bool
b1B3IntroducesEstimate = false

clayPromotion : Bool
clayPromotion = false
