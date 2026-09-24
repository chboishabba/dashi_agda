{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNSpectatorSelfHomochiralHeterochiralRowRound633Exact where

------------------------------------------------------------------------
-- ROUND633 / SPECTATOR SELF ROW = HOMOCHIRAL RADIAL + HETEROCHIRAL
--
-- R632 splits each literal self R573 nested cell into:
--
--   homochiral radial part + heterochiral literal part.
--
-- This owner lifts that exact equality through the complete fixed-output fold
-- and then through the SAME R545 spectator Hermitian test used by R627.
--
-- No norm, absolute value, estimate, positivity, or change of test functional
-- is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; _+_)
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
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventR294WeightRound541Exact as R541
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventRowFactorizationRound545Exact as R545
import DASHI.Physics.Closure.NSTriadKNR573SelfMultiplierDifferenceFoldRound626Exact as R626
import DASHI.Physics.Closure.NSTriadKNSpectatorSelfMultiplierDifferenceRowRound627Exact as R627
import DASHI.Physics.Closure.NSTriadKNSelfHomochiralHeterochiralSplitRound632Exact as R632

F : C3.RealField _
F = Rational.rationalRealField

module SpectatorSelfHelicityRow633
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
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode)) where

  system = Field30.finiteSystem physicalSystem

  module Spec = R541.Spectator physicalSystem S
  module Row = R545.Row physicalSystem S
  module Existing =
    R627.SpectatorSelfMultiplierRow
      physicalSystem S L H velocityTransverse

  module At (beta : Physical.PhysicalTriadIncidence) where

    W = Spec.spectatorWeight beta

    module MultFold =
      R626.SelfMultiplierFold W S L H system velocityTransverse

    module Split =
      R632.SelfHelicitySplit632 W S L H system velocityTransverse

    fibre : Z3.FourierMode → List Physical.PhysicalTriadIncidence
    fibre output =
      Output.physicalOutputFiber (Audit.cutoff system) output

    homochiralFold heterochiralFold :
      Z3.FourierMode → C3.Complex3 F
    homochiralFold output =
      R224.foldVector Split.homochiralNested (fibre output)
    heterochiralFold output =
      R224.foldVector Split.heterochiralNested (fibre output)

    selfMultiplierFoldSplits :
      (output : Z3.FourierMode) →
      MultFold.selfMultiplierNestedFold output
      ≡ C3.complex3Add
          (homochiralFold output)
          (heterochiralFold output)
    selfMultiplierFoldSplits output =
      trans
        (foldPointwise (fibre output))
        (R225.foldPointwiseAdd
          Split.homochiralNested
          Split.heterochiralNested
          (fibre output))
      where
      foldPointwise :
        (items : List Physical.PhysicalTriadIncidence) →
        R224.foldVector Split.Base.selfNestedMultiplierCompanion items
        ≡
        R224.foldVector
          (λ tau →
            C3.complex3Add
              (Split.homochiralNested tau)
              (Split.heterochiralNested tau))
          items
      foldPointwise [] = refl
      foldPointwise (tau ∷ rest) =
        cong₂ C3.complex3Add
          (Split.selfNestedMultiplierSplits tau)
          (foldPointwise rest)

    homochiralRow heterochiralRow :
      Z3.FourierMode → ℚ
    homochiralRow output =
      R179.realHermitianCross
        (homochiralFold output)
        (Row.doubleCell beta)
    heterochiralRow output =
      R179.realHermitianCross
        (heterochiralFold output)
        (Row.doubleCell beta)

    selfMultiplierRowSplits :
      (output : Z3.FourierMode) →
      Existing.selfMultiplierNestedForcingRow output beta
      ≡ homochiralRow output + heterochiralRow output
    selfMultiplierRowSplits output =
      trans
        (cong
          (λ force →
            R179.realHermitianCross force (Row.doubleCell beta))
          (selfMultiplierFoldSplits output))
        (R291.realCrossAddLeft
          (homochiralFold output)
          (heterochiralFold output)
          (Row.doubleCell beta))

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round633FixedOutputSelfHomochiralHeterochiralFoldSplitClosed : Bool
round633FixedOutputSelfHomochiralHeterochiralFoldSplitClosed = true

round633SpectatorSelfRowHomochiralHeterochiralSplitClosed : Bool
round633SpectatorSelfRowHomochiralHeterochiralSplitClosed = true

round633HomochiralPartAlreadyOnRadialCarrier : Bool
round633HomochiralPartAlreadyOnRadialCarrier = true

round633HeterochiralPartStillLiteral : Bool
round633HeterochiralPartStillLiteral = true

round633IntroducesEstimate : Bool
round633IntroducesEstimate = false

round633SelfSignedPaymentClosed : Bool
round633SelfSignedPaymentClosed = false

round633FixedOutputSelfHomochiralHeterochiralFoldSplitClosedIsTrue :
  round633FixedOutputSelfHomochiralHeterochiralFoldSplitClosed ≡ true
round633FixedOutputSelfHomochiralHeterochiralFoldSplitClosedIsTrue = refl

round633SpectatorSelfRowHomochiralHeterochiralSplitClosedIsTrue :
  round633SpectatorSelfRowHomochiralHeterochiralSplitClosed ≡ true
round633SpectatorSelfRowHomochiralHeterochiralSplitClosedIsTrue = refl

round633HomochiralPartAlreadyOnRadialCarrierIsTrue :
  round633HomochiralPartAlreadyOnRadialCarrier ≡ true
round633HomochiralPartAlreadyOnRadialCarrierIsTrue = refl

round633HeterochiralPartStillLiteralIsTrue :
  round633HeterochiralPartStillLiteral ≡ true
round633HeterochiralPartStillLiteralIsTrue = refl

round633IntroducesEstimateIsFalse :
  round633IntroducesEstimate ≡ false
round633IntroducesEstimateIsFalse = refl

round633SelfSignedPaymentClosedIsFalse :
  round633SelfSignedPaymentClosed ≡ false
round633SelfSignedPaymentClosedIsFalse = refl
