module DASHI.Physics.Closure.NSTriadKNFixedOutputFourSignFibreMajorantRound578Exact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
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
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = Rational.rationalRealField

nonzeroTransport :
  (left right : Z3.FourierMode) →
  left ≡ right → Z3.NonZeroMode right → Z3.NonZeroMode left
nonzeroTransport left right refl rightNonzero = rightNonzero

module FixedOutput
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (O : Leray.RationalInverseNormOrder E I)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  module Fibre = R577.PhysicalFibre E I O system S L velocityTransverse
  module Cell = R576.PhysicalRecombination E I O system S L velocityTransverse

  inputProductMass : Physical.PhysicalTriadIncidence → ℚ
  inputProductMass tau =
    L2.complex3NormSquared (Audit.velocity system (Physical.p tau))
      * L2.complex3NormSquared (Audit.velocity system (Physical.q tau))

  inputProductMassSum : List Physical.PhysicalTriadIncidence → ℚ
  inputProductMassSum [] = 0ℚ
  inputProductMassSum (tau ∷ rest) =
    inputProductMass tau + inputProductMassSum rest

  sameOutputMajorantFactorization :
    (output : Z3.FourierMode) →
    (items : List Physical.PhysicalTriadIncidence) →
    ((tau : Physical.PhysicalTriadIncidence) →
      tau R396.OccursIn items → Physical.k tau ≡ output) →
    Fibre.majorantSum items
    ≡ R576.thirtySix * C3.normSquared I output
        * inputProductMassSum items
  sameOutputMajorantFactorization output [] allOutput = solve []
  sameOutputMajorantFactorization output (tau ∷ rest) allOutput =
    let
      headOutput = allOutput tau R396.here
      tailOutput :
        (selected : Physical.PhysicalTriadIncidence) →
        selected R396.OccursIn rest → Physical.k selected ≡ output
      tailOutput selected member = allOutput selected (R396.there member)
      tail = sameOutputMajorantFactorization output rest tailOutput
      headMass = inputProductMass tau
      tailMass = inputProductMassSum rest
      headNorm : C3.normSquared I (Physical.k tau) ≡ C3.normSquared I output
      headNorm = cong (C3.normSquared I) headOutput
    in
    trans
      (cong₂ _+_
        (cong (λ norm → R576.thirtySix * norm * headMass) headNorm)
        tail)
      (solve
        ( R576.thirtySix
        ∷ C3.normSquared I output
        ∷ headMass ∷ tailMass ∷ []))

  sameOutputCellMassBound :
    (output : Z3.FourierMode) →
    (outputNonzero : Z3.NonZeroMode output) →
    (items : List Physical.PhysicalTriadIncidence) →
    (allOutput :
      (tau : Physical.PhysicalTriadIncidence) →
      tau R396.OccursIn items → Physical.k tau ≡ output) →
    R180.cellMassSum (Fibre.fourSignCells items)
    ≤ R576.thirtySix * C3.normSquared I output
        * inputProductMassSum items
  sameOutputCellMassBound output outputNonzero [] allOutput = ℚP.≤-refl
  sameOutputCellMassBound output outputNonzero (tau ∷ rest) allOutput =
    let
      headOutput = allOutput tau R396.here
      headNonzero = nonzeroTransport (Physical.k tau) output headOutput outputNonzero
      headBound = Cell.fourSignInnerLowOutputBound tau headNonzero
      tailOutput :
        (selected : Physical.PhysicalTriadIncidence) →
        selected R396.OccursIn rest → Physical.k selected ≡ output
      tailOutput selected member = allOutput selected (R396.there member)
      tailBound = sameOutputCellMassBound output outputNonzero rest tailOutput
      added = ℚP.+-mono-≤ headBound tailBound
      headMass = inputProductMass tau
      tailMass = inputProductMassSum rest
      normalize :
        R576.thirtySix * C3.normSquared I (Physical.k tau) * headMass
          + R576.thirtySix * C3.normSquared I output * tailMass
        ≡ R576.thirtySix * C3.normSquared I output * (headMass + tailMass)
      normalize rewrite headOutput =
        solve
          ( R576.thirtySix
          ∷ C3.normSquared I output
          ∷ headMass ∷ tailMass ∷ [])
    in
    subst
      (λ upper → R180.cellMassSum (Fibre.fourSignCells (tau ∷ rest)) ≤ upper)
      normalize added

  record FixedOutputFourSignGramPayment578
      (output : Z3.FourierMode)
      (items : List Physical.PhysicalTriadIncidence) : Set where
    constructor fixed-output-four-sign-gram-payment-578
    field
      gramResidual578 : ℚ
      gramDebtUpper578 :
        R180.gramDebt (Fibre.fourSignCells items) ≤ gramResidual578

  open FixedOutputFourSignGramPayment578 public

  paidFixedOutputBound :
    (output : Z3.FourierMode) →
    (outputNonzero : Z3.NonZeroMode output) →
    (items : List Physical.PhysicalTriadIncidence) →
    (allOutput :
      (tau : Physical.PhysicalTriadIncidence) →
      tau R396.OccursIn items → Physical.k tau ≡ output) →
    (payment : FixedOutputFourSignGramPayment578 output items) →
    L2.complex3NormSquared (R224.foldVector Cell.fourSignInner items)
    ≤ R576.thirtySix * C3.normSquared I output
        * inputProductMassSum items
      + gramResidual578 payment
  paidFixedOutputBound output outputNonzero items allOutput payment =
    let
      ledger = Fibre.exactFourSignFibreGramLedger items
      massBound = sameOutputCellMassBound output outputNonzero items allOutput
      combined = ℚP.+-mono-≤ massBound (gramDebtUpper578 payment)
    in
    subst
      (λ lower →
        lower ≤ R576.thirtySix * C3.normSquared I output
          * inputProductMassSum items + gramResidual578 payment)
      (sym ledger)
      combined

round578CommonOutputLowFrequencyFactorsExactly : Bool
round578CommonOutputLowFrequencyFactorsExactly = true

round578PositiveCellMassPartIsFiniteEnergyConvolution : Bool
round578PositiveCellMassPartIsFiniteEnergyConvolution = true

round578PositiveCellMassPartNeedsFibreCardinality : Bool
round578PositiveCellMassPartNeedsFibreCardinality = false

round578SignedVariableFibreGramResidualPaid : Bool
round578SignedVariableFibreGramResidualPaid = false

round578OuterSpectatorWeightedSpacetimeBoundClosed : Bool
round578OuterSpectatorWeightedSpacetimeBoundClosed = false

round578CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round578CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round578ClayPromotion : Bool
round578ClayPromotion = false

round578CommonOutputLowFrequencyFactorsExactlyIsTrue :
  round578CommonOutputLowFrequencyFactorsExactly ≡ true
round578CommonOutputLowFrequencyFactorsExactlyIsTrue = refl

round578PositiveCellMassPartNeedsFibreCardinalityIsFalse :
  round578PositiveCellMassPartNeedsFibreCardinality ≡ false
round578PositiveCellMassPartNeedsFibreCardinalityIsFalse = refl

round578ClayPromotionIsFalse : round578ClayPromotion ≡ false
round578ClayPromotionIsFalse = refl
