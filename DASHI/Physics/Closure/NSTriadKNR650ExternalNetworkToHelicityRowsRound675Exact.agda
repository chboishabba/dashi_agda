{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650ExternalNetworkToHelicityRowsRound675Exact where

------------------------------------------------------------------------
-- ROUND675 / R606/R607 EXTERNAL NETWORK -> R636/R637 HELICITY ROW CARRIER
--
-- R674 identifies the complete R606 external forcing square on one physical
-- output fibre with the canonical R623/R631 external row sum.
--
-- R636 independently identifies each of those SAME canonical external rows
-- with the literal total external helicity-commutator scalar.  Therefore the
-- complete R606 external full square is exactly the finite helicity-row sum
-- which R637 later aggregates through outputs and spacetime.
--
-- R607 contributes one additional scalar factor AFTER the R606 square:
--
--   externalNetworkContribution
--     = rateTotal * externalForcingFull.
--
-- This owner keeps that factor explicit.  For any rational rateTotal,
--
--   rateTotal * R606.externalForcingFull
--     =
--   rateTotal * sum_beta R636.externalHelicityRow(beta).
--
-- Hence the C2 external-network residual has reached the mature C1-side
-- helicity-commutator carrier, but it is RATE-WEIGHTED.  The existing unweighted
-- R637 signed spacetime payment cannot be claimed to pay this term unless that
-- extra rate factor is handled by a genuine theorem.
--
-- No estimate, norm, absolute value, or new Clay-facing analytic leaf appears.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventR294WeightRound541Exact as R541
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventRowFactorizationRound545Exact as R545
import DASHI.Physics.Closure.NSTriadKNR567ForcingFullSelfExternalSplitRound606Exact as R606
import DASHI.Physics.Closure.NSTriadKNCanonicalExternalHelicityCommutatorRound636Exact as R636
import DASHI.Physics.Closure.NSTriadKNR650ExternalFullSquareToCanonicalRowsRound674Exact as R674

F : C3.RealField _
F = Rational.rationalRealField

module ExternalHelicityRows675
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode))
    (output : Z3.FourierMode) where

  E = Field30.physicalEmbedding physicalSystem
  I = Field30.physicalInverseSquare physicalSystem
  system = Field30.finiteSystem physicalSystem
  cutoff = Audit.cutoff system

  module Split = R606.FixedOutput physicalSystem S output
  module Rows = R674.ExternalRows674
    physicalSystem S L H velocityTransverse output
  module Spec = R541.Spectator physicalSystem S
  module Row = R545.Row physicalSystem S

  fibre : List Physical.PhysicalTriadIncidence
  fibre = Output.physicalOutputFiber cutoff output

  module HelicityAt (beta : Physical.PhysicalTriadIncidence) =
    R636.CanonicalExternalHelicity636
      E I (Spec.spectatorWeight beta)
      S L H system velocityTransverse

  helicityExternalRow :
    Physical.PhysicalTriadIncidence → ℚ
  helicityExternalRow beta =
    let module HB = HelicityAt beta in
    HB.totalExternalHelicityScalar output (Row.doubleCell beta)

  canonicalExternalRowIsHelicity :
    (beta : Physical.PhysicalTriadIncidence) →
    Rows.Rows.canonicalExternalNestedForcingRow output beta
    ≡ helicityExternalRow beta
  canonicalExternalRowIsHelicity beta =
    let module HB = HelicityAt beta in
    HB.canonicalExternalScalarIsHelicityCommutatorScalar
      output (Row.doubleCell beta)

  helicityExternalRows :
    List Physical.PhysicalTriadIncidence → ℚ
  helicityExternalRows [] = 0ℚ
  helicityExternalRows (beta ∷ rest) =
    helicityExternalRow beta + helicityExternalRows rest

  canonicalExternalRowsAreHelicity :
    (betas : List Physical.PhysicalTriadIncidence) →
    Rows.canonicalExternalRows betas
    ≡ helicityExternalRows betas
  canonicalExternalRowsAreHelicity [] = refl
  canonicalExternalRowsAreHelicity (beta ∷ rest) =
    cong₂ _+_
      (canonicalExternalRowIsHelicity beta)
      (canonicalExternalRowsAreHelicity rest)

  externalForcingFullIsHelicityRows :
    Split.externalForcingFull
    ≡ helicityExternalRows fibre
  externalForcingFullIsHelicityRows =
    trans
      Rows.externalForcingFullIsCanonicalExternalRows
      (canonicalExternalRowsAreHelicity fibre)

  rateWeightedExternalNetworkIsHelicityRows :
    (rateTotal : ℚ) →
    rateTotal * Split.externalForcingFull
    ≡ rateTotal * helicityExternalRows fibre
  rateWeightedExternalNetworkIsHelicityRows rateTotal =
    cong (rateTotal *_) externalForcingFullIsHelicityRows

------------------------------------------------------------------------
-- Status / multiplier firewall.
------------------------------------------------------------------------

round675R606ExternalFullSquareOnR636HelicityRows : Bool
round675R606ExternalFullSquareOnR636HelicityRows = true

round675R607RateMultiplierPreservedExactly : Bool
round675R607RateMultiplierPreservedExactly = true

round675R607ExternalNetworkOnRateWeightedR637Carrier : Bool
round675R607ExternalNetworkOnRateWeightedR637Carrier = true

round675ExistingUnweightedR637PaymentDirectlyPaysRateWeightedR607 : Bool
round675ExistingUnweightedR637PaymentDirectlyPaysRateWeightedR607 = false

round675IntroducesEstimate : Bool
round675IntroducesEstimate = false

round675RateWeightedExternalSignedPaymentClosed : Bool
round675RateWeightedExternalSignedPaymentClosed = false

round675IntroducesNewClayLeaf : Bool
round675IntroducesNewClayLeaf = false

round675ClayPromotion : Bool
round675ClayPromotion = false

round675R606ExternalFullSquareOnR636HelicityRowsIsTrue :
  round675R606ExternalFullSquareOnR636HelicityRows ≡ true
round675R606ExternalFullSquareOnR636HelicityRowsIsTrue = refl

round675R607RateMultiplierPreservedExactlyIsTrue :
  round675R607RateMultiplierPreservedExactly ≡ true
round675R607RateMultiplierPreservedExactlyIsTrue = refl

round675R607ExternalNetworkOnRateWeightedR637CarrierIsTrue :
  round675R607ExternalNetworkOnRateWeightedR637Carrier ≡ true
round675R607ExternalNetworkOnRateWeightedR637CarrierIsTrue = refl

round675ExistingUnweightedR637PaymentDirectlyPaysRateWeightedR607IsFalse :
  round675ExistingUnweightedR637PaymentDirectlyPaysRateWeightedR607 ≡ false
round675ExistingUnweightedR637PaymentDirectlyPaysRateWeightedR607IsFalse = refl

round675IntroducesEstimateIsFalse :
  round675IntroducesEstimate ≡ false
round675IntroducesEstimateIsFalse = refl

round675RateWeightedExternalSignedPaymentClosedIsFalse :
  round675RateWeightedExternalSignedPaymentClosed ≡ false
round675RateWeightedExternalSignedPaymentClosedIsFalse = refl

round675IntroducesNewClayLeafIsFalse :
  round675IntroducesNewClayLeaf ≡ false
round675IntroducesNewClayLeafIsFalse = refl

round675ClayPromotionIsFalse :
  round675ClayPromotion ≡ false
round675ClayPromotionIsFalse = refl
