module DASHI.Physics.Closure.NSTriadKNSpectatorWeightedAmplitudeGramResidualBidiExact where

------------------------------------------------------------------------
-- SPECTATOR-WEIGHTED AMPLITUDE -> ONE SIGNED GRAM RESIDUAL
--
-- The preceding owners now pay everything except cross-cell coherence:
--
--   ||sum w_beta A_alpha||^2
--     = cellMassSum(w_beta A) + gramDebt(w_beta A),
--
--   cellMassSum(w_beta A)
--     <= C_nu^2 * sum E_p E_q,
--
-- with C_nu = 1/(2 nu), on a nonzero fixed physical output fibre.
--
-- Therefore a caller needs only an upper bound on the SIGNED weighted Gram
-- debt.  This owner deliberately does not replace that debt by absolute values,
-- a fibre cardinality, or a Schur bound.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; Positive; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNRationalPhysicalPairRatePositivityRound400Exact as R400
import DASHI.Physics.Closure.NSTriadKNCanonicalFourierUnitGapRateFloorRound450Exact as R450
import DASHI.Physics.Closure.NSTriadKNSpectatorWeightedAmplitudeGramLedgerBidiExact as LedgerOwner
import DASHI.Physics.Closure.NSTriadKNSpectatorWeightedAmplitudeCellMassMajorantBidiExact as MassOwner

F : C3.RealField _
F = Rational.rationalRealField

module Residual
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (viscosityPositive : Positive (Field30.viscosity physicalSystem))
    (unitGap : R450.CanonicalFourierUnitGap physicalSystem)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode))
    (cutoff : Nat)
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output)
    (beta : Physical.PhysicalTriadIncidence)
    (betaOutput : Physical.k beta ≡ output) where

  module Rate = R400.PhysicalRate physicalSystem S viscosityPositive
  module Ledger = LedgerOwner.Ledger physicalSystem S
  module Mass = MassOwner.Majorant
    physicalSystem S L viscosityPositive unitGap velocityTransverse
    output outputNonzero beta betaOutput

  fibre = Output.physicalOutputFiber cutoff output

  amplitudeFold =
    LedgerOwner.Ledger.weightedAmplitudeCell physicalSystem S beta

  record WeightedAmplitudeGramPayment (upper : ℚ) : Set where
    constructor weighted-amplitude-gram-payment
    field
      gramDebtBelow :
        R180.gramDebt (Ledger.weightedAmplitudeCells beta fibre) ≤ upper

  open WeightedAmplitudeGramPayment public

  physicalCellMassBound :
    R180.cellMassSum (Ledger.weightedAmplitudeCells beta fibre)
    ≤ (Mass.ceiling * Mass.ceiling) * Mass.inputProductMassSum fibre
  physicalCellMassBound =
    Mass.weightedCellMassSumBelow fibre
      (Rate.allElementsHaveOutput cutoff output)

  paidAmplitudeNormBound :
    (upper : ℚ) →
    WeightedAmplitudeGramPayment upper →
    L2.complex3NormSquared
      (LedgerOwner.Ledger.weightedAmplitudeCell physicalSystem S beta
        -- only fixes the function below; the fold itself is written explicitly
        |>dummy)
    ≤ upper
  paidAmplitudeNormBound upper payment = impossible

  -- The theorem above is stated below in its actual fold shape; the tiny local
  -- aliases are intentionally avoided to keep the same-object carrier visible.
  amplitudeNormBelowEnergyConvolutionPlusGram :
    (upper : ℚ) →
    WeightedAmplitudeGramPayment upper →
    L2.complex3NormSquared
      (DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact.foldVector
        (Ledger.weightedAmplitudeCell beta) fibre)
    ≤ (Mass.ceiling * Mass.ceiling) * Mass.inputProductMassSum fibre + upper
  amplitudeNormBelowEnergyConvolutionPlusGram upper payment =
    let
      exact = Ledger.exactWeightedAmplitudeGramLedger beta fibre
      combined = ℚP.+-mono-≤ physicalCellMassBound (gramDebtBelow payment)
    in
    subst
      (λ lower →
        lower ≤ (Mass.ceiling * Mass.ceiling) * Mass.inputProductMassSum fibre + upper)
      exact combined

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

weightedAmplitudePositiveMassPaid : Bool
weightedAmplitudePositiveMassPaid = true

weightedAmplitudeOnlyGramResidualRemains : Bool
weightedAmplitudeOnlyGramResidualRemains = true

weightedAmplitudeGramResidualPaid : Bool
weightedAmplitudeGramResidualPaid = false

weightedAmplitudeSpacetimePaymentClosed : Bool
weightedAmplitudeSpacetimePaymentClosed = false

clayPromotion : Bool
clayPromotion = false
