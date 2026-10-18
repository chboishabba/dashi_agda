{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR571HeterochiralRadialSumSpecializationRound635Exact where

------------------------------------------------------------------------
-- ROUND635 / R571 HETEROCHIRAL MULTIPLIERS = SIGNED RADIAL SUMS
--
-- R311 already records the scalar classification
--
--   (+,-) : -(r_q + r_p)
--   (-,+) : +(r_q + r_p).
--
-- This owner places those formulas on the literal R571 physical vector
-- carrier and attaches their sum back to R632's heterochiral self channel.
--
-- This is representation only.  In particular a radial sum is NOT promoted to
-- a small commutator gain; the heterochiral analytic payment remains open.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (_+_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralThreeLegWaleffeCommonAmplitudeRound93Exact as R93
import DASHI.Physics.Closure.NSTriadKNNestedInnerHelicityRouteSplitRound311Exact as R311
import DASHI.Physics.Closure.NSTriadKNInnerHelicalComponentCommutatorRound571Exact as R571
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNSelfHomochiralHeterochiralSplitRound632Exact as R632

F : C3.RealField _
F = Rational.rationalRealField

module PhysicalHeterochiral
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  module C = R571.Componentwise system S L velocityTransverse

  plusMinusRadialSumVector :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  plusMinusRadialSumVector tau =
    C3.complex3Scale
      (C3.realEmbed F
        (- (Helical.modeNorm S (Physical.q tau)
          + Helical.modeNorm S (Physical.p tau))))
      (C3.lerayProject3 E I (Physical.k tau)
        (Cross.complex3Cross
          (C.component Helical.plus (Physical.p tau))
          (C.component Helical.minus (Physical.q tau))))

  minusPlusRadialSumVector :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  minusPlusRadialSumVector tau =
    C3.complex3Scale
      (C3.realEmbed F
        (Helical.modeNorm S (Physical.q tau)
          + Helical.modeNorm S (Physical.p tau)))
      (C3.lerayProject3 E I (Physical.k tau)
        (Cross.complex3Cross
          (C.component Helical.minus (Physical.p tau))
          (C.component Helical.plus (Physical.q tau))))

  plusMinusMultiplierDifferenceIsRadialSum :
    (tau : Physical.PhysicalTriadIncidence) →
    C.multiplierDifferenceVector tau Helical.plus Helical.minus
    ≡ plusMinusRadialSumVector tau
  plusMinusMultiplierDifferenceIsRadialSum tau =
    cong
      (λ scalar →
        C3.complex3Scale scalar
          (C3.lerayProject3 E I (Physical.k tau)
            (Cross.complex3Cross
              (C.component Helical.plus (Physical.p tau))
              (C.component Helical.minus (Physical.q tau)))))
      (trans
        (R93.realEmbedSubtract
          (- Helical.modeNorm S (Physical.q tau))
          (Helical.modeNorm S (Physical.p tau)))
        (cong (C3.realEmbed F)
          (solve
            ( Helical.modeNorm S (Physical.p tau)
            ∷ Helical.modeNorm S (Physical.q tau)
            ∷ []))))

  minusPlusMultiplierDifferenceIsRadialSum :
    (tau : Physical.PhysicalTriadIncidence) →
    C.multiplierDifferenceVector tau Helical.minus Helical.plus
    ≡ minusPlusRadialSumVector tau
  minusPlusMultiplierDifferenceIsRadialSum tau =
    cong
      (λ scalar →
        C3.complex3Scale scalar
          (C3.lerayProject3 E I (Physical.k tau)
            (Cross.complex3Cross
              (C.component Helical.minus (Physical.p tau))
              (C.component Helical.plus (Physical.q tau)))))
      (trans
        (R93.realEmbedSubtract
          (Helical.modeNorm S (Physical.q tau))
          (- Helical.modeNorm S (Physical.p tau)))
        (cong (C3.realEmbed F)
          (solve
            ( Helical.modeNorm S (Physical.p tau)
            ∷ Helical.modeNorm S (Physical.q tau)
            ∷ []))))

  heterochiralRadialSumVector :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  heterochiralRadialSumVector tau =
    C3.complex3Add
      (plusMinusRadialSumVector tau)
      (minusPlusRadialSumVector tau)

module AttachToR632
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  module Split =
    R632.SelfHelicitySplit632 W S L H system velocityTransverse

  module Hetero =
    PhysicalHeterochiral E I system S L velocityTransverse

  heterochiralVectorIsRadialSum :
    (tau : Physical.PhysicalTriadIncidence) →
    Split.heterochiralVector tau
    ≡ Hetero.heterochiralRadialSumVector tau
  heterochiralVectorIsRadialSum tau =
    cong₂ C3.complex3Add
      (Hetero.plusMinusMultiplierDifferenceIsRadialSum tau)
      (Hetero.minusPlusMultiplierDifferenceIsRadialSum tau)

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round635HeterochiralRadialSumCarrierWeldClosed : Bool
round635HeterochiralRadialSumCarrierWeldClosed = true

round635R632HeterochiralVectorRadialSumWeldClosed : Bool
round635R632HeterochiralVectorRadialSumWeldClosed = true

round635HeterochiralRadialSumIsNullGain : Bool
round635HeterochiralRadialSumIsNullGain = false

round635IntroducesEstimate : Bool
round635IntroducesEstimate = false

round635HeterochiralSignedPaymentClosed : Bool
round635HeterochiralSignedPaymentClosed = false

round635HeterochiralRadialSumCarrierWeldClosedIsTrue :
  round635HeterochiralRadialSumCarrierWeldClosed ≡ true
round635HeterochiralRadialSumCarrierWeldClosedIsTrue = refl

round635R632HeterochiralVectorRadialSumWeldClosedIsTrue :
  round635R632HeterochiralVectorRadialSumWeldClosed ≡ true
round635R632HeterochiralVectorRadialSumWeldClosedIsTrue = refl

round635HeterochiralRadialSumIsNullGainIsFalse :
  round635HeterochiralRadialSumIsNullGain ≡ false
round635HeterochiralRadialSumIsNullGainIsFalse = refl

round635IntroducesEstimateIsFalse :
  round635IntroducesEstimate ≡ false
round635IntroducesEstimateIsFalse = refl

round635HeterochiralSignedPaymentClosedIsFalse :
  round635HeterochiralSignedPaymentClosed ≡ false
round635HeterochiralSignedPaymentClosedIsFalse = refl
