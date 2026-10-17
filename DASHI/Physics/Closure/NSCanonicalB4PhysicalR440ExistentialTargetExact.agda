{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSCanonicalB4PhysicalR440ExistentialTargetExact where

------------------------------------------------------------------------
-- CANONICAL B4 / EXISTENTIAL LITERAL R440 WITNESS
--
-- This is the next max-cut after the literal-uniform target.
--
-- * the R440 signed defect is definitionally fixed;
-- * the Core-Core companion mass is definitionally fixed;
-- * the local ED currency is definitionally fixed;
-- * the selector is fixed to ALL physical pairs;
-- * positivity of the two positive currencies is derived from their literal
--   definitions and is no longer an analytic witness field.
--
-- The only remaining quantitative witnesses are therefore thetaD and cD,
-- with
--
--   0 <= thetaD < 1/2,
--   0 <= cD,
--
-- and the single cutoff/state/output-uniform physical inequality.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_; ∣_∣)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNPhysicalOrderedTransferSquaredMajorantRound96Exact as R96
import DASHI.Physics.Closure.NSTriadKNSelectedPairEnergyDissipationProductRound109Exact as R109
import DASHI.Physics.Closure.NSTriadKNPhysicalRawCurlCellEDAdapterRound219Exact as R219
import DASHI.Physics.Closure.NSTriadKNSelectedPairPhysicalTriadRoutingRound469Exact as R469
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentWorkDifferenceVectorBridgeExact as Bridge
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceQuantitativePairBoundExact as Quant
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionLiteralPairExtractionMaxCutExact as Rows
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingLiteralCompanion20261007Exact as Companion
import DASHI.Physics.Closure.NSCanonicalB4PhysicalR440LiteralUniformTargetExact as Literal

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- One fixed selector for the whole positive-B family.
--
-- R469/R219 prove the global ED estimate for every Boolean selector.  Taking
-- all pairs removes the last selector degree of freedom and maximises the
-- nonnegative local ED currency available to B1/B2/B3/B4.
------------------------------------------------------------------------

allPairsSelect : Z3.FourierMode → Z3.FourierMode → Bool
allPairsSelect _ _ = true

------------------------------------------------------------------------
-- Positivity of the literal Core-Core companion is theorem-derived.
------------------------------------------------------------------------

rateWeightedYoungPairNonnegative :
  ∀ {A : Set} →
  (mixed : C3.Complex3 F) →
  (rate : A → ℚ) →
  (value : A → C3.Complex3 F) →
  (left right : A) →
  0ℚ ≤ Quant.rateWeightedYoungPair mixed rate value left right
rateWeightedYoungPairNonnegative mixed rate value left right =
  let
    rateNN : 0ℚ ≤ ∣ rate left - rate right ∣
    rateNN = ℚP.0≤∣p∣ (rate left - rate right)

    oneNN : 0ℚ ≤ 1ℚ
    oneNN = ℚP.0≤∣p∣ 1ℚ

    twoNN : 0ℚ ≤ Bridge.two
    twoNN = Rational.addNonnegative oneNN oneNN

    mixedNN : 0ℚ ≤ L2.complex3NormSquared mixed
    mixedNN = Separation.complex3NormSquaredNonnegative mixed

    differenceNN :
      0ℚ ≤ L2.complex3NormSquared
        (C3.complex3Subtract (value left) (value right))
    differenceNN =
      Separation.complex3NormSquaredNonnegative
        (C3.complex3Subtract (value left) (value right))

    innerNN :
      0ℚ ≤ L2.complex3NormSquared mixed
        + L2.complex3NormSquared
            (C3.complex3Subtract (value left) (value right))
    innerNN = Rational.addNonnegative mixedNN differenceNN
  in
  R96.productNonnegative
    (R96.productNonnegative rateNN twoNN)
    innerNN

rowCompanionNonnegative :
  (mixed : C3.Complex3 F) →
  (rate : Physical.PhysicalTriadIncidence → ℚ) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (row : Rows.LiteralPairRow) →
  0ℚ ≤ Companion.rowCompanion mixed rate value row
rowCompanionNonnegative mixed rate value row =
  rateWeightedYoungPairNonnegative
    mixed rate value (Rows.alpha row) (Rows.beta row)

companionSumNonnegative :
  (mixed : C3.Complex3 F) →
  (rate : Physical.PhysicalTriadIncidence → ℚ) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (rows : List Rows.LiteralPairRow) →
  0ℚ ≤ Companion.companionSum mixed rate value rows
companionSumNonnegative mixed rate value [] = ℚP.≤-refl
companionSumNonnegative mixed rate value (row ∷ rest) =
  Rational.addNonnegative
    (rowCompanionNonnegative mixed rate value row)
    (companionSumNonnegative mixed rate value rest)

literalCoreCompanionMassNonnegative :
  (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F) →
  (S : Helical.HelicalModeScalars F) →
  (output : Z3.FourierMode) →
  0ℚ ≤ Literal.literalCoreCompanionMass physicalSystem S output
literalCoreCompanionMassNonnegative physicalSystem S output =
  let module C = Companion.LiveLiteralCompanion physicalSystem S output
  in
  companionSumNonnegative
    (C.Live.mixed output)
    C.Rate.inputMass
    C.Live.value
    C.R.principalLiteralRows

------------------------------------------------------------------------
-- Positivity of the literal selected-pair local ED is theorem-derived.
------------------------------------------------------------------------

selectedTriadValueNonnegative :
  (M : R109.ModalEnergyDissipation Z3.FourierMode) →
  (select : Z3.FourierMode → Z3.FourierMode → Bool) →
  (tau : Physical.PhysicalTriadIncidence) →
  0ℚ ≤ R469.selectedTriadValue M select tau
selectedTriadValueNonnegative M select tau
  with select (Physical.p tau) (Physical.q tau)
... | true = R109.pairKernelNonnegative M (Physical.p tau) (Physical.q tau)
... | false = ℚP.≤-refl

foldPowerNonnegative :
  (value : Physical.PhysicalTriadIncidence → ℚ) →
  ((tau : Physical.PhysicalTriadIncidence) → 0ℚ ≤ value tau) →
  (items : List Physical.PhysicalTriadIncidence) →
  0ℚ ≤ R38.foldPower value items
foldPowerNonnegative value valueNN [] = ℚP.≤-refl
foldPowerNonnegative value valueNN (tau ∷ rest) =
  Rational.addNonnegative
    (valueNN tau)
    (foldPowerNonnegative value valueNN rest)

literalSelectedPairLocalEDNonnegative :
  (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F) →
  (select : Z3.FourierMode → Z3.FourierMode → Bool) →
  (output : Z3.FourierMode) →
  0ℚ ≤ Literal.literalSelectedPairLocalED physicalSystem select output
literalSelectedPairLocalEDNonnegative physicalSystem select output =
  let
    E = Field30.physicalEmbedding physicalSystem
    I = Field30.physicalInverseSquare physicalSystem
    system = Field30.finiteSystem physicalSystem
    velocity = Audit.velocity system
    cutoff = Audit.cutoff system
    M = R219.physicalModalED E I velocity
  in
  foldPowerNonnegative
    (R469.selectedTriadValue M select)
    (selectedTriadValueNonnegative M select)
    (Output.physicalOutputFiber cutoff output)

------------------------------------------------------------------------
-- Exact existential AST.
--
-- All positive-currency side conditions above are discharged by theorem.
-- The ONLY unproved quantitative invariants carried here are thetaD, cD and
-- the uniform literal R440 payment itself.
------------------------------------------------------------------------

record CanonicalB4PhysicalR440ExistentialWitness : Set₁ where
  field
    thetaD cD : ℚ

    thetaDNonnegative :
      0ℚ ≤ thetaD

    thetaDStrictlyBelowHalf :
      thetaD < Literal.oneHalf

    defectEDCoefficientNonnegative :
      0ℚ ≤ cD

    uniformLiteralPhysicalR440DefectPayment :
      (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F) →
      0ℚ ≤ Field30.viscosity physicalSystem →
      (S : Helical.HelicalModeScalars F) →
      (output : Z3.FourierMode) →
      Literal.literalSignedR440Work physicalSystem S output
      ≤ thetaD * Literal.literalCoreCompanionMass physicalSystem S output
        + cD * Literal.literalSelectedPairLocalED
            physicalSystem allPairsSelect output

open CanonicalB4PhysicalR440ExistentialWitness public

B4LiteralPhysicalR440ExistentialKeyOpenLemma : Set₁
B4LiteralPhysicalR440ExistentialKeyOpenLemma =
  CanonicalB4PhysicalR440ExistentialWitness

------------------------------------------------------------------------
-- Status / invariant ledger.
------------------------------------------------------------------------

b4ExistentialTargetUsesAllPairsSelector : Bool
b4ExistentialTargetUsesAllPairsSelector = true

b4CoreCompanionNonnegativeDerived : Bool
b4CoreCompanionNonnegativeDerived = true

b4AllPairsLocalEDNonnegativeDerived : Bool
b4AllPairsLocalEDNonnegativeDerived = true

b4OnlyThetaAndEDCoefficientRemainQuantitativeWitnesses : Bool
b4OnlyThetaAndEDCoefficientRemainQuantitativeWitnesses = true

b4ExistentialUniformPhysicalR440PaymentClosed : Bool
b4ExistentialUniformPhysicalR440PaymentClosed = false

clayPromotion : Bool
clayPromotion = false

b4ExistentialTargetUsesAllPairsSelectorIsTrue :
  b4ExistentialTargetUsesAllPairsSelector ≡ true
b4ExistentialTargetUsesAllPairsSelectorIsTrue = refl

b4CoreCompanionNonnegativeDerivedIsTrue :
  b4CoreCompanionNonnegativeDerived ≡ true
b4CoreCompanionNonnegativeDerivedIsTrue = refl

b4AllPairsLocalEDNonnegativeDerivedIsTrue :
  b4AllPairsLocalEDNonnegativeDerived ≡ true
b4AllPairsLocalEDNonnegativeDerivedIsTrue = refl

b4OnlyThetaAndEDCoefficientRemainQuantitativeWitnessesIsTrue :
  b4OnlyThetaAndEDCoefficientRemainQuantitativeWitnesses ≡ true
b4OnlyThetaAndEDCoefficientRemainQuantitativeWitnessesIsTrue = refl

b4ExistentialUniformPhysicalR440PaymentClosedIsFalse :
  b4ExistentialUniformPhysicalR440PaymentClosed ≡ false
b4ExistentialUniformPhysicalR440PaymentClosedIsFalse = refl
