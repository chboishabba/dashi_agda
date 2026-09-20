module DASHI.Physics.Closure.NSTriadKNFourSignInnerFibreGramBoundaryRound577Exact where

------------------------------------------------------------------------
-- ROUND577 / EXACT VARIABLE-FIBRE GRAM BOUNDARY AFTER R576
--
-- R576 closes the fixed four-helicity recombination for every inner incidence:
--
--   ||M_tau||^2 <= 36 |k_tau|^2 E_p E_q.
--
-- The remaining danger is NOT another local norm estimate.  It is the signed
-- covariance created when a variable number of distinct incidences on the same
-- output fibre are summed.  R180 already owns the exact finite identity
--
--   ||sum cells||^2 = sum ||cell||^2 + GramDebt(cells).
--
-- This owner welds that old ledger to the NEW literal R571/R572 four-sign cell.
-- It also sums R576's pointwise majorants over an arbitrary finite incidence
-- list.  Therefore the complete variable-fibre problem is now exactly:
--
--   pay one signed Gram residual for the actual fourSignInner cells.
--
-- Nonpositivity is NOT required: any quantitative residual upper bound is
-- sufficient.  This mirrors the later R215 correction and avoids reinstating
-- the obsolete 'all covariance must cancel' requirement.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNRawCurlLowOutputKernelMassRound178Exact as R178
import DASHI.Physics.Closure.NSTriadKNFourHelicityVectorRecombinationRound576Exact as R576
import DASHI.Physics.Closure.NSTriadKNPhysicalResonantEuclideanSquareTriangleRound218Exact as R218
import DASHI.Physics.Closure.NSTriadKNPhysicalRawCurlCellEDAdapterRound219Exact as R219
import DASHI.Physics.Closure.NSTriadKNPhysicalOrderedTransferSquaredMajorantRound96Exact as R96
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = Rational.rationalRealField

module PhysicalFibre
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (O : Leray.RationalInverseNormOrder E I)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  module Cell = R576.PhysicalRecombination
    E I O system S L velocityTransverse

  fourSignCells :
    List Physical.PhysicalTriadIncidence → List (C3.Complex3 F)
  fourSignCells items = map Cell.fourSignInner items

  foldIsGramSum :
    (items : List Physical.PhysicalTriadIncidence) →
    R224.foldVector Cell.fourSignInner items
    ≡ R180.sumCells (fourSignCells items)
  foldIsGramSum [] = refl
  foldIsGramSum (tau ∷ rest) =
    cong₂ C3.complex3Add refl (foldIsGramSum rest)

  exactFourSignFibreGramLedger :
    (items : List Physical.PhysicalTriadIncidence) →
    L2.complex3NormSquared (R224.foldVector Cell.fourSignInner items)
    ≡ R180.cellMassSum (fourSignCells items)
      + R180.gramDebt (fourSignCells items)
  exactFourSignFibreGramLedger items =
    trans
      (cong L2.complex3NormSquared (foldIsGramSum items))
      (R180.finiteFibreGramLedger (fourSignCells items))

  pointwiseMajorant : Physical.PhysicalTriadIncidence → ℚ
  pointwiseMajorant tau =
    R576.thirtySix * C3.normSquared I (Physical.k tau)
      * L2.complex3NormSquared (Audit.velocity system (Physical.p tau))
      * L2.complex3NormSquared (Audit.velocity system (Physical.q tau))

  majorantSum : List Physical.PhysicalTriadIncidence → ℚ
  majorantSum [] = 0ℚ
  majorantSum (tau ∷ rest) = pointwiseMajorant tau + majorantSum rest

  cellMassSumBound :
    (items : List Physical.PhysicalTriadIncidence) →
    ((tau : Physical.PhysicalTriadIncidence) →
      Z3.NonZeroMode (Physical.k tau)) →
    R180.cellMassSum (fourSignCells items) ≤ majorantSum items
  cellMassSumBound [] allNonzero = ℚP.≤-refl
  cellMassSumBound (tau ∷ rest) allNonzero =
    ℚP.+-mono-≤
      (Cell.fourSignInnerLowOutputBound tau (allNonzero tau))
      (cellMassSumBound rest allNonzero)


  twoNN577 : 0ℚ ≤ R218.two
  twoNN577 = Rational.addNonnegative R178.oneNN R178.oneNN

  nineNN577 : 0ℚ ≤ R178.nine
  nineNN577 = R96.productNonnegative R178.threeNN R178.threeNN

  thirtySixNN577 : 0ℚ ≤ R576.thirtySix
  thirtySixNN577 =
    R96.productNonnegative R576.fourNN nineNN577

  seventyTwo : ℚ
  seventyTwo = R576.thirtySix * R218.two

  modalEnergy : Z3.FourierMode → ℚ
  modalEnergy mode =
    L2.complex3NormSquared (Audit.velocity system mode)

  modalDissipation : Z3.FourierMode → ℚ
  modalDissipation mode =
    C3.normSquared I mode * modalEnergy mode

  pairEDKernel577 :
    Physical.PhysicalTriadIncidence → ℚ
  pairEDKernel577 tau =
    modalDissipation (Physical.p tau) * modalEnergy (Physical.q tau)
    + modalEnergy (Physical.p tau) * modalDissipation (Physical.q tau)

  edKernelSum577 :
    List Physical.PhysicalTriadIncidence → ℚ
  edKernelSum577 [] = 0ℚ
  edKernelSum577 (tau ∷ rest) =
    pairEDKernel577 tau + edKernelSum577 rest

  pointwiseMajorantBelowSeventyTwoEDKernel :
    (tau : Physical.PhysicalTriadIncidence) →
    pointwiseMajorant tau ≤ seventyTwo * pairEDKernel577 tau
  pointwiseMajorantBelowSeventyTwoEDKernel tau =
    let
      k2 = C3.normSquared I (Physical.k tau)
      p2 = C3.normSquared I (Physical.p tau)
      q2 = C3.normSquared I (Physical.q tau)
      ep = modalEnergy (Physical.p tau)
      eq = modalEnergy (Physical.q tau)

      kNN = R219.modeSquareNonnegative E I (Physical.k tau)
      pNN = R219.modeSquareNonnegative E I (Physical.p tau)
      qNN = R219.modeSquareNonnegative E I (Physical.q tau)
      epNN = Separation.complex3NormSquaredNonnegative
        (Audit.velocity system (Physical.p tau))
      eqNN = Separation.complex3NormSquaredNonnegative
        (Audit.velocity system (Physical.q tau))

      pqNN : 0ℚ ≤ p2 + q2
      pqNN = Rational.addNonnegative pNN qNN

      radialNN : 0ℚ ≤ R218.two * (p2 + q2)
      radialNN = R96.productNonnegative twoNN577 pqNN

      triangle :
        k2 ≤ R218.two * (p2 + q2)
      triangle =
        R218.resonantEuclideanSquareTriangle
          E I (Physical.resonance tau)

      first :
        k2 * ep ≤ (R218.two * (p2 + q2)) * ep
      first =
        Rational.nonnegativeProductMonotone
          kNN epNN radialNN epNN triangle ℚP.≤-refl

      leftNN = R96.productNonnegative kNN epNN
      rightNN = R96.productNonnegative radialNN epNN

      second :
        (k2 * ep) * eq
        ≤ ((R218.two * (p2 + q2)) * ep) * eq
      second =
        Rational.nonnegativeProductMonotone
          leftNN eqNN rightNN eqNN first ℚP.≤-refl

      leftTripleNN = R96.productNonnegative leftNN eqNN
      rightTripleNN = R96.productNonnegative rightNN eqNN

      scaled :
        R576.thirtySix * ((k2 * ep) * eq)
        ≤ R576.thirtySix *
            (((R218.two * (p2 + q2)) * ep) * eq)
      scaled =
        Rational.nonnegativeProductMonotone
          thirtySixNN577 leftTripleNN
          thirtySixNN577 rightTripleNN
          ℚP.≤-refl second

      sourceMeaning :
        pointwiseMajorant tau
        ≡ R576.thirtySix * ((k2 * ep) * eq)
      sourceMeaning = solve
        (R576.thirtySix ∷ k2 ∷ ep ∷ eq ∷ [])

      targetMeaning :
        R576.thirtySix *
          (((R218.two * (p2 + q2)) * ep) * eq)
        ≡ seventyTwo * pairEDKernel577 tau
      targetMeaning = solve
        ( R576.thirtySix ∷ R218.two ∷ p2 ∷ q2 ∷ ep ∷ eq ∷ [])
    in
    subst
      (λ lower → lower ≤ seventyTwo * pairEDKernel577 tau)
      (sym sourceMeaning)
      (subst
        (λ upper →
          R576.thirtySix * ((k2 * ep) * eq) ≤ upper)
        targetMeaning
        scaled)

  majorantSumBelowSeventyTwoEDKernelSum :
    (items : List Physical.PhysicalTriadIncidence) →
    majorantSum items ≤ seventyTwo * edKernelSum577 items
  majorantSumBelowSeventyTwoEDKernelSum [] =
    subst
      (0ℚ ≤_)
      (sym (ℚP.*-zeroʳ seventyTwo))
      ℚP.≤-refl
  majorantSumBelowSeventyTwoEDKernelSum (tau ∷ rest) =
    let
      added =
        ℚP.+-mono-≤
          (pointwiseMajorantBelowSeventyTwoEDKernel tau)
          (majorantSumBelowSeventyTwoEDKernelSum rest)
      endpoint :
        seventyTwo * pairEDKernel577 tau
          + seventyTwo * edKernelSum577 rest
        ≡ seventyTwo * edKernelSum577 (tau ∷ rest)
      endpoint = solve
        (seventyTwo ∷ pairEDKernel577 tau ∷ edKernelSum577 rest ∷ [])
    in
    subst
      (λ upper → majorantSum (tau ∷ rest) ≤ upper)
      endpoint
      added

  record QuantitativeFourSignGramPayment577
      (items : List Physical.PhysicalTriadIncidence) : Set where
    constructor quantitative-four-sign-gram-payment-577
    field
      gramResidual577 : ℚ
      gramDebtUpper577 :
        R180.gramDebt (fourSignCells items) ≤ gramResidual577

  open QuantitativeFourSignGramPayment577 public

  paidVariableFibreBound :
    (items : List Physical.PhysicalTriadIncidence) →
    ((tau : Physical.PhysicalTriadIncidence) →
      Z3.NonZeroMode (Physical.k tau)) →
    (payment : QuantitativeFourSignGramPayment577 items) →
    L2.complex3NormSquared (R224.foldVector Cell.fourSignInner items)
    ≤ majorantSum items + gramResidual577 payment
  paidVariableFibreBound items allNonzero payment =
    let
      ledger = exactFourSignFibreGramLedger items
      masses = cellMassSumBound items allNonzero
      debt = gramDebtUpper577 payment
      combined :
        R180.cellMassSum (fourSignCells items)
          + R180.gramDebt (fourSignCells items)
        ≤ majorantSum items + gramResidual577 payment
      combined = ℚP.+-mono-≤ masses debt
    in
    subst
      (λ lower →
        lower ≤ majorantSum items + gramResidual577 payment)
      (sym ledger)
      combined

  nonpositiveGramIsOnlySufficientNotNecessary :
    (items : List Physical.PhysicalTriadIncidence) →
    R180.gramDebt (fourSignCells items) ≤ 0ℚ →
    QuantitativeFourSignGramPayment577 items
  nonpositiveGramIsOnlySufficientNotNecessary items nonpositive =
    quantitative-four-sign-gram-payment-577 0ℚ nonpositive

------------------------------------------------------------------------
-- Status / introspective cut.
------------------------------------------------------------------------

round577R576CellBoundAttachedToExactR180GramLedger : Bool
round577R576CellBoundAttachedToExactR180GramLedger = true

round577VariableFibreCellMassMajorantSummedExactly : Bool
round577VariableFibreCellMassMajorantSummedExactly = true

round577CellMassMajorantPaidByEnergyDissipationKernel : Bool
round577CellMassMajorantPaidByEnergyDissipationKernel = true

round577WithinFibreGramMustBeNonpositive : Bool
round577WithinFibreGramMustBeNonpositive = false

round577QuantitativeVariableFibreGramResidualPaid : Bool
round577QuantitativeVariableFibreGramResidualPaid = false

round577VariableFibreCardinalityFactorIntroduced : Bool
round577VariableFibreCardinalityFactorIntroduced = false

round577OuterSpectatorWeightedSpacetimeBoundClosed : Bool
round577OuterSpectatorWeightedSpacetimeBoundClosed = false

round577CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round577CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round577ClayPromotion : Bool
round577ClayPromotion = false

round577R576CellBoundAttachedToExactR180GramLedgerIsTrue :
  round577R576CellBoundAttachedToExactR180GramLedger ≡ true
round577R576CellBoundAttachedToExactR180GramLedgerIsTrue = refl

round577WithinFibreGramMustBeNonpositiveIsFalse :
  round577WithinFibreGramMustBeNonpositive ≡ false
round577WithinFibreGramMustBeNonpositiveIsFalse = refl

round577ClayPromotionIsFalse : round577ClayPromotion ≡ false
round577ClayPromotionIsFalse = refl
