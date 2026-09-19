module DASHI.Physics.Closure.NSTriadKNCenteredMultiplierDoubleMixedWeldExact where

------------------------------------------------------------------------
-- CENTERED MULTIPLIER: MIXED COVARIANCE CARRIER -> R503 DOUBLE-MIXED CARRIER
--
-- R544 proves that any swap-invariant scalar weight preserves the exact
-- double-mixed normalization on a complete fixed-output fibre.
--
-- The physical centered-frequency multiplier
--
--   c(tau) = |p_tau-q_tau|^2
--
-- is swap invariant.  Therefore
--
--   sum_tau c(tau) doubleMixed(tau)
--     = 4 sum_tau c(tau) mixedPlusMinus(tau).
--
-- Together with R225's unweighted identity this shows that the vector
-- centered-multiplier residual appearing in the d1b2 covariance lane lives on
-- exactly the same double-mixed family as the R290/R503 quartic Gram lane.
--
-- No estimate, norm observer, pair multiplicity, or cutoff factor is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.List.Base using (length)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNLerayComplexScalarLinearityRound73Exact as R73
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNFixedOutputViscousRateDifferenceFactorizationExact as Rate
import DASHI.Physics.Closure.NSTriadKNSpectatorDoubleCellAmplitudeFoldRound544Exact as R544
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredMultiplierVectorCovarianceExact as Vector
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Cov

F : C3.RealField _
F = Rational.rationalRealField

centeredSquareSwap :
  (E : C3.IntegerEmbedding F) →
  (tau : Physical.PhysicalTriadIncidence) →
  Rate.centeredSquare E
      (Physical.p (Symmetry.swapTriad tau))
      (Physical.q (Symmetry.swapTriad tau))
  ≡
  Rate.centeredSquare E (Physical.p tau) (Physical.q tau)
centeredSquareSwap E tau =
  let
    px = C3.embedInteger E (Z3.kx (Physical.p tau))
    py = C3.embedInteger E (Z3.ky (Physical.p tau))
    pz = C3.embedInteger E (Z3.kz (Physical.p tau))
    qx = C3.embedInteger E (Z3.kx (Physical.q tau))
    qy = C3.embedInteger E (Z3.ky (Physical.q tau))
    qz = C3.embedInteger E (Z3.kz (Physical.q tau))
  in
  solve (px ∷ py ∷ pz ∷ qx ∷ qy ∷ qz ∷ [])

centeredSquareWeight :
  (E : C3.IntegerEmbedding F) →
  R294.SwapInvariantCellWeight F
centeredSquareWeight E = record
  { R294.weight = λ tau →
      C3.realEmbed F
        (Rate.centeredSquare E (Physical.p tau) (Physical.q tau))
  ; R294.swapInvariant = λ tau →
      cong (C3.realEmbed F) (centeredSquareSwap E tau)
  }

module PhysicalCenteredDoubleMixed
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  E = Field30.physicalEmbedding physicalSystem
  I = Field30.physicalInverseSquare physicalSystem
  system = Field30.finiteSystem physicalSystem

  W : R294.SwapInvariantCellWeight F
  W = centeredSquareWeight E

  module Weighted = R544.Fold physicalSystem S W

  multiplier : Physical.PhysicalTriadIncidence → ℚ
  multiplier = Vector.centeredFrequencyMultiplier E

  weightedMixedCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  weightedMixedCell tau =
    R291.realScale (multiplier tau)
      (R224.mixedPlusMinus S Weighted.D.Pair.velocity tau)

  weightedDoubleMixedCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  weightedDoubleMixedCell tau =
    R291.realScale (multiplier tau)
      (R225.doubleMixedCell S Weighted.D.Pair.velocity tau)

  weightedMixedCellIsR544Amplitude :
    (tau : Physical.PhysicalTriadIncidence) →
    weightedMixedCell tau ≡ Weighted.amplitude tau
  weightedMixedCellIsR544Amplitude tau = refl

  weightedDoubleMixedCellIsR544Cell :
    (tau : Physical.PhysicalTriadIncidence) →
    weightedDoubleMixedCell tau ≡ Weighted.weightedDoubleCell tau
  weightedDoubleMixedCellIsR544Cell tau = refl

  foldPointwise :
    (left right : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
    ((tau : Physical.PhysicalTriadIncidence) → left tau ≡ right tau) →
    (items : List Physical.PhysicalTriadIncidence) →
    R224.foldVector left items ≡ R224.foldVector right items
  foldPointwise left right pointwise [] = refl
  foldPointwise left right pointwise (tau ∷ rest) =
    cong₂ C3.complex3Add
      (pointwise tau)
      (foldPointwise left right pointwise rest)

  fixedOutputCenteredWeightedDoubleIsFourMixed :
    (output : Z3.FourierMode) →
    let
      items = Output.physicalOutputFiber (Audit.cutoff system) output
      A = R224.foldVector weightedMixedCell items
    in
    R224.foldVector weightedDoubleMixedCell items
    ≡ C3.complex3Add (C3.complex3Add A A) (C3.complex3Add A A)
  fixedOutputCenteredWeightedDoubleIsFourMixed output =
    let
      items = Output.physicalOutputFiber (Audit.cutoff system) output

      leftMeaning :
        R224.foldVector weightedDoubleMixedCell items
        ≡ R224.foldVector Weighted.weightedDoubleCell items
      leftMeaning =
        foldPointwise weightedDoubleMixedCell Weighted.weightedDoubleCell
          weightedDoubleMixedCellIsR544Cell items

      rightMeaning :
        R224.foldVector Weighted.amplitude items
        ≡ R224.foldVector weightedMixedCell items
      rightMeaning =
        foldPointwise Weighted.amplitude weightedMixedCell
          (λ tau → sym (weightedMixedCellIsR544Amplitude tau)) items
    in
    trans leftMeaning
      (trans
        (Weighted.fixedOutputWeightedDoubleCellIsFourAmplitudeFolds output)
        (cong
          (λ A →
            C3.complex3Add (C3.complex3Add A A)
              (C3.complex3Add A A))
          rightMeaning))


  weightedMixedVectorMeaning :
    (items : List Physical.PhysicalTriadIncidence) →
    Vector.weightedVectorSum multiplier
      (R224.mixedPlusMinus S Weighted.D.Pair.velocity) items
    ≡ R224.foldVector weightedMixedCell items
  weightedMixedVectorMeaning [] = refl
  weightedMixedVectorMeaning (tau ∷ rest) =
    cong (C3.complex3Add (weightedMixedCell tau))
      (weightedMixedVectorMeaning rest)

  weightedDoubleVectorMeaning :
    (items : List Physical.PhysicalTriadIncidence) →
    Vector.weightedVectorSum multiplier
      (R225.doubleMixedCell S Weighted.D.Pair.velocity) items
    ≡ R224.foldVector weightedDoubleMixedCell items
  weightedDoubleVectorMeaning [] = refl
  weightedDoubleVectorMeaning (tau ∷ rest) =
    cong (C3.complex3Add (weightedDoubleMixedCell tau))
      (weightedDoubleVectorMeaning rest)

  fixedOutputWeightedDoubleVectorIsFourMixed :
    (output : Z3.FourierMode) →
    let
      items = Output.physicalOutputFiber (Audit.cutoff system) output
      mixedWeighted =
        Vector.weightedVectorSum multiplier
          (R224.mixedPlusMinus S Weighted.D.Pair.velocity) items
      doubleWeighted =
        Vector.weightedVectorSum multiplier
          (R225.doubleMixedCell S Weighted.D.Pair.velocity) items
    in
    doubleWeighted ≡ R225.fourCopies mixedWeighted
  fixedOutputWeightedDoubleVectorIsFourMixed output =
    let
      items = Output.physicalOutputFiber (Audit.cutoff system) output
      mixedWeighted =
        Vector.weightedVectorSum multiplier
          (R224.mixedPlusMinus S Weighted.D.Pair.velocity) items
      doubleWeighted =
        Vector.weightedVectorSum multiplier
          (R225.doubleMixedCell S Weighted.D.Pair.velocity) items

      left =
        weightedDoubleVectorMeaning items

      fourFold =
        fixedOutputCenteredWeightedDoubleIsFourMixed output

      right :
        R225.fourCopies (R224.foldVector weightedMixedCell items)
        ≡ R225.fourCopies mixedWeighted
      right =
        cong R225.fourCopies (sym (weightedMixedVectorMeaning items))
    in
    trans left (trans fourFold right)

  realScaleFourCopies :
    (scalar : ℚ) (value : C3.Complex3 F) →
    R291.realScale scalar (R225.fourCopies value)
    ≡ R225.fourCopies (R291.realScale scalar value)
  realScaleFourCopies scalar value =
    let s = C3.realEmbed F scalar in
    trans
      (R73.complex3ScaleAdd s
        (C3.complex3Add value value)
        (C3.complex3Add value value))
      (cong₂ C3.complex3Add
        (R73.complex3ScaleAdd s value value)
        (R73.complex3ScaleAdd s value value))

  addFourCopies :
    (left right : C3.Complex3 F) →
    C3.complex3Add (R225.fourCopies left) (R225.fourCopies right)
    ≡ R225.fourCopies (C3.complex3Add left right)
  addFourCopies left right =
    trans
      (R230.complex3Shuffle
        (C3.complex3Add left left)
        (C3.complex3Add left left)
        (C3.complex3Add right right)
        (C3.complex3Add right right))
      (cong₂ C3.complex3Add
        (R230.complex3Shuffle left left right right)
        (R230.complex3Shuffle left left right right))

  fixedOutputDoubleResidualIsFourMixedResidual :
    (output : Z3.FourierMode) →
    let
      items = Output.physicalOutputFiber (Audit.cutoff system) output
      mixedValue = R224.mixedPlusMinus S Weighted.D.Pair.velocity
      doubleValue = R225.doubleMixedCell S Weighted.D.Pair.velocity
      mixedResidual =
        Vector.centeredMultiplierResidual multiplier mixedValue items
      doubleResidual =
        Vector.centeredMultiplierResidual multiplier doubleValue items
    in
    doubleResidual ≡ R225.fourCopies mixedResidual
  fixedOutputDoubleResidualIsFourMixedResidual output =
    let
      items = Output.physicalOutputFiber (Audit.cutoff system) output
      mixedValue = R224.mixedPlusMinus S Weighted.D.Pair.velocity
      doubleValue = R225.doubleMixedCell S Weighted.D.Pair.velocity
      mixed = R224.foldVector mixedValue items
      double = R224.foldVector doubleValue items
      mixedWeighted = Vector.weightedVectorSum multiplier mixedValue items
      doubleWeighted = Vector.weightedVectorSum multiplier doubleValue items
      n = Cov.natAsRational (length items)
      totalMultiplier =
        Cov.rateSum multiplier items
      negativeTotal = 0ℚ - totalMultiplier

      weightedFour :
        doubleWeighted ≡ R225.fourCopies mixedWeighted
      weightedFour = fixedOutputWeightedDoubleVectorIsFourMixed output

      unweightedFour :
        double ≡ R225.fourCopies mixed
      unweightedFour =
        R225.fixedOutputDoubleMixedSumIsFourPlusMinusSum
          S Weighted.D.Pair.velocity (Audit.cutoff system) output

      expose :
        Vector.centeredMultiplierResidual multiplier doubleValue items
        ≡ C3.complex3Add
            (R291.realScale n doubleWeighted)
            (R291.realScale negativeTotal double)
      expose = refl

      replaceFour :
        C3.complex3Add
          (R291.realScale n doubleWeighted)
          (R291.realScale negativeTotal double)
        ≡
        C3.complex3Add
          (R291.realScale n (R225.fourCopies mixedWeighted))
          (R291.realScale negativeTotal (R225.fourCopies mixed))
      replaceFour =
        cong₂ C3.complex3Add
          (cong (R291.realScale n) weightedFour)
          (cong (R291.realScale negativeTotal) unweightedFour)

      distribute :
        C3.complex3Add
          (R291.realScale n (R225.fourCopies mixedWeighted))
          (R291.realScale negativeTotal (R225.fourCopies mixed))
        ≡
        C3.complex3Add
          (R225.fourCopies (R291.realScale n mixedWeighted))
          (R225.fourCopies (R291.realScale negativeTotal mixed))
      distribute =
        cong₂ C3.complex3Add
          (realScaleFourCopies n mixedWeighted)
          (realScaleFourCopies negativeTotal mixed)

      collect :
        C3.complex3Add
          (R225.fourCopies (R291.realScale n mixedWeighted))
          (R225.fourCopies (R291.realScale negativeTotal mixed))
        ≡
        R225.fourCopies
          (C3.complex3Add
            (R291.realScale n mixedWeighted)
            (R291.realScale negativeTotal mixed))
      collect =
        addFourCopies
          (R291.realScale n mixedWeighted)
          (R291.realScale negativeTotal mixed)
    in
    trans expose (trans replaceFour (trans distribute collect))

centeredMultiplierWeightedDoubleMixedWeldClosed : Bool
centeredMultiplierWeightedDoubleMixedWeldClosed = true

centeredMultiplierWeightSwapInvariant : Bool
centeredMultiplierWeightSwapInvariant = true

centeredMultiplierDoubleMixedWeldAddsCutoffFactor : Bool
centeredMultiplierDoubleMixedWeldAddsCutoffFactor = false

centeredMultiplierDoubleMixedWeldIntroducesEstimate : Bool
centeredMultiplierDoubleMixedWeldIntroducesEstimate = false

clayPromotion : Bool
clayPromotion = false

centeredMultiplierWeightedDoubleMixedWeldClosedIsTrue :
  centeredMultiplierWeightedDoubleMixedWeldClosed ≡ true
centeredMultiplierWeightedDoubleMixedWeldClosedIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
