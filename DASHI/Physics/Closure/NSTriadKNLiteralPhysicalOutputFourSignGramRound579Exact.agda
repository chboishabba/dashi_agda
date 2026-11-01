module DASHI.Physics.Closure.NSTriadKNLiteralPhysicalOutputFourSignGramRound579Exact where

------------------------------------------------------------------------
-- ROUND579 / R578 ON THE LITERAL PHYSICAL OUTPUT FIBRE
--
-- R578 still accepted an abstract finite list plus an all-elements-have-output
-- proof.  The repository already has a literal duplicate-free physical output
-- fibre.  This owner removes that final enumeration abstraction.
--
-- For
--
--   fibre(N,k) = physicalOutputFiber N k,
--
-- membership itself proves every selected incidence has output k.  Therefore,
-- for nonzero k,
--
--   ||sum_{tau in fibre(N,k)} fourSignInner_tau||^2
--     <= 36 |k|^2 sum_{tau in fibre(N,k)} E_p E_q + GramResidual(N,k).
--
-- The positive part is now a literal finite convolution on the exact R406-side
-- physical enumeration.  The ONLY unfunded within-fibre coordinate in this
-- theorem is the quantitative signed Gram residual.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact as R396
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNFourHelicityVectorRecombinationRound576Exact as R576
import DASHI.Physics.Closure.NSTriadKNFourSignInnerFibreGramBoundaryRound577Exact as R577
import DASHI.Physics.Closure.NSTriadKNFixedOutputFourSignFibreMajorantRound578Exact as R578
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = Rational.rationalRealField

occursToCube :
  ∀ {tau items} → tau R396.OccursIn items → tau Cube.∈ items
occursToCube R396.here = Cube.here refl
occursToCube (R396.there member) = Cube.there (occursToCube member)

literalFibreAllHaveOutput :
  (cutoff : Nat) (output : Z3.FourierMode) →
  (tau : Physical.PhysicalTriadIncidence) →
  tau R396.OccursIn Output.physicalOutputFiber cutoff output →
  Physical.k tau ≡ output
literalFibreAllHaveOutput cutoff output tau member =
  Output.physicalOutputFiberSound (occursToCube member)

module LiteralOutput
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (O : Leray.RationalInverseNormOrder E I)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  module Fixed = R578.FixedOutput E I O system S L velocityTransverse
  module Fibre = R577.PhysicalFibre E I O system S L velocityTransverse
  module Cell = R576.PhysicalRecombination E I O system S L velocityTransverse

  literalFibre : Nat → Z3.FourierMode → Agda.Builtin.List.List Physical.PhysicalTriadIncidence
  literalFibre cutoff output = Output.physicalOutputFiber cutoff output

  literalInputConvolutionMass : Nat → Z3.FourierMode → ℚ
  literalInputConvolutionMass cutoff output =
    Fixed.inputProductMassSum (literalFibre cutoff output)

  literalGramDebt : Nat → Z3.FourierMode → ℚ
  literalGramDebt cutoff output =
    R180.gramDebt (Fibre.fourSignCells (literalFibre cutoff output))

  record LiteralOutputGramPayment579 (cutoff : Nat) (output : Z3.FourierMode) : Set where
    constructor literal-output-gram-payment-579
    field
      gramResidual579 : ℚ
      literalGramDebtUpper579 :
        literalGramDebt cutoff output ≤ gramResidual579

  open LiteralOutputGramPayment579 public

  asR578Payment :
    (cutoff : Nat) (output : Z3.FourierMode) →
    LiteralOutputGramPayment579 cutoff output →
    Fixed.FixedOutputFourSignGramPayment578 output (literalFibre cutoff output)
  asR578Payment cutoff output payment =
    Fixed.fixed-output-four-sign-gram-payment-578
      (gramResidual579 payment)
      (literalGramDebtUpper579 payment)

  literalPhysicalOutputBound :
    (cutoff : Nat) (output : Z3.FourierMode) →
    (outputNonzero : Z3.NonZeroMode output) →
    (payment : LiteralOutputGramPayment579 cutoff output) →
    L2.complex3NormSquared
      (R224.foldVector Cell.fourSignInner (literalFibre cutoff output))
    ≤ R576.thirtySix * C3.normSquared I output
        * literalInputConvolutionMass cutoff output
      + gramResidual579 payment
  literalPhysicalOutputBound cutoff output outputNonzero payment =
    Fixed.paidFixedOutputBound
      output outputNonzero (literalFibre cutoff output)
      (literalFibreAllHaveOutput cutoff output)
      (asR578Payment cutoff output payment)

round579LiteralPhysicalOutputEnumerationAttached : Bool
round579LiteralPhysicalOutputEnumerationAttached = true

round579PositivePartLiteralFiniteConvolutionAttached : Bool
round579PositivePartLiteralFiniteConvolutionAttached = true

round579AdditionalEnumerationReceiptRequired : Bool
round579AdditionalEnumerationReceiptRequired = false

round579LiteralSignedGramResidualPaid : Bool
round579LiteralSignedGramResidualPaid = false

round579OuterSpectatorWeightedSpacetimeBoundClosed : Bool
round579OuterSpectatorWeightedSpacetimeBoundClosed = false

round579CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round579CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round579ClayPromotion : Bool
round579ClayPromotion = false

round579LiteralPhysicalOutputEnumerationAttachedIsTrue :
  round579LiteralPhysicalOutputEnumerationAttached ≡ true
round579LiteralPhysicalOutputEnumerationAttachedIsTrue = refl

round579AdditionalEnumerationReceiptRequiredIsFalse :
  round579AdditionalEnumerationReceiptRequired ≡ false
round579AdditionalEnumerationReceiptRequiredIsFalse = refl

round579ClayPromotionIsFalse : round579ClayPromotion ≡ false
round579ClayPromotionIsFalse = refl
