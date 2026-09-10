module DASHI.Physics.Closure.NSTriadKNSpectatorWeightedAmplitudeCellMassMajorantBidiExact where

------------------------------------------------------------------------
-- SPECTATOR-WEIGHTED MIXED AMPLITUDE CELL MASS -> ENERGY CONVOLUTION
--
-- On a fixed nonzero output fibre, R450 gives the physical cell-rate floor
--
--   nu <= lambda_alpha,  nu <= lambda_beta.
--
-- Hence the literal R541 spectator Cauchy weight satisfies
--
--   w_beta(alpha) = 1 / (lambda_alpha + lambda_beta) <= 1 / (2 nu).
--
-- The mixed-helicity cell owner gives
--
--   ||A_alpha||^2 <= E_p E_q.
--
-- Therefore, with C_nu = 1/(2 nu),
--
--   sum_alpha ||w_beta(alpha) A_alpha||^2
--     <= C_nu^2 sum_alpha E_p E_q.
--
-- This is a finite positive-mass estimate.  It introduces no fibre cardinality
-- and leaves the signed weighted Gram debt completely separate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; Positive; NonNegative; _+_; _*_; _≤_; _<_; positive; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNHHAntiParallelQuadraticKernelNormRound174Exact as R174
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact as R396
import DASHI.Physics.Closure.NSTriadKNRationalPhysicalPairRatePositivityRound400Exact as R400
import DASHI.Physics.Closure.NSTriadKNDiagonalResolventRateFloorRound449Exact as R449
import DASHI.Physics.Closure.NSTriadKNCanonicalFourierUnitGapRateFloorRound450Exact as R450
import DASHI.Physics.Closure.NSTriadKNRationalNormalizedDirectionUnitRound455Exact as R455
import DASHI.Physics.Closure.NSTriadKNDirectResolventPairSwapSymmetryRound538Exact as R538
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventR294WeightRound541Exact as R541
import DASHI.Physics.Closure.NSTriadKNMixedHelicityCellEnergyProductBidiExact as Cell
import DASHI.Physics.Closure.NSTriadKNSpectatorWeightedAmplitudeGramLedgerBidiExact as LedgerOwner
import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quotient

F : C3.RealField _
F = Rational.rationalRealField

module Majorant
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
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output)
    (beta : Physical.PhysicalTriadIncidence)
    (betaOutput : Physical.k beta ≡ output) where

  E = Field30.physicalEmbedding physicalSystem
  I = Field30.physicalInverseSquare physicalSystem
  system = Field30.finiteSystem physicalSystem
  velocity = Audit.velocity system

  module Rate = R400.PhysicalRate physicalSystem S viscosityPositive
  module Floor = R450.PhysicalCellRateFloor
    physicalSystem S viscosityPositive unitGap
  module Swap = R538.PairSwap physicalSystem S
  module Spec = R541.Spectator physicalSystem S
  module Ledger = LedgerOwner.Ledger physicalSystem S

  nu : ℚ
  nu = Floor.nu

  ceiling : ℚ
  ceiling = R449.diagonalCeilingAt nu Floor.nuPositive

  ceilingPositive : 0ℚ < ceiling
  ceilingPositive =
    Quotient.positiveReciprocalPositive
      (R449.two * nu) (R449.twicePositive Floor.nuPositive)

  ceilingNN : 0ℚ ≤ ceiling
  ceilingNN = ℚP.<⇒≤ ceilingPositive

  pairRate : Physical.PhysicalTriadIncidence → ℚ
  pairRate alpha = R291.pairRate (Swap.Q alpha beta)

  pairRatePositive :
    (alpha : Physical.PhysicalTriadIncidence) →
    Physical.k alpha ≡ output →
    Positive (pairRate alpha)
  pairRatePositive alpha alphaOutput =
    Rate.pairRatePositiveFromCellRates alpha beta
      (Rate.cellRatePositiveFromNonzeroOutput
        output outputNonzero alpha alphaOutput)
      (Rate.cellRatePositiveFromNonzeroOutput
        output outputNonzero beta betaOutput)

  twoNuBelowPairRate :
    (alpha : Physical.PhysicalTriadIncidence) →
    Physical.k alpha ≡ output →
    R449.two * nu ≤ pairRate alpha
  twoNuBelowPairRate alpha alphaOutput =
    let
      alphaFloor = Floor.cellRateAtLeastNuFromNonzeroOutput
        output outputNonzero alpha alphaOutput
      betaFloor = Floor.cellRateAtLeastNuFromNonzeroOutput
        output outputNonzero beta betaOutput
      raw = ℚP.+-mono-≤ alphaFloor betaFloor
      lowerMeaning : nu + nu ≡ R449.two * nu
      lowerMeaning = solve (nu ∷ [])
    in
    subst (_≤ pairRate alpha) lowerMeaning raw

  pairResolventBelowCeiling :
    (alpha : Physical.PhysicalTriadIncidence) →
    Physical.k alpha ≡ output →
    Swap.pairResolvent alpha beta ≤ ceiling
  pairResolventBelowCeiling alpha alphaOutput =
    let
      instance pairPositiveI : Positive (pairRate alpha)
      pairPositiveI = pairRatePositive alpha alphaOutput
      pairStrict : 0ℚ < pairRate alpha
      pairStrict = ℚP.positive⁻¹ (pairRate alpha)
      lowerStrict = R449.twicePositive Floor.nuPositive
      asPositiveReciprocal :
        Swap.pairResolvent alpha beta
        ≡ Quotient.positiveReciprocal (pairRate alpha) pairStrict
      asPositiveReciprocal =
        R449.safeReciprocalIsPositiveReciprocal (pairRate alpha) pairStrict
      antitone :
        Quotient.positiveReciprocal (pairRate alpha) pairStrict
        ≤ Quotient.positiveReciprocal (R449.two * nu) lowerStrict
      antitone =
        Quotient.reciprocalAntitonePositive
          (R449.two * nu) (pairRate alpha)
          lowerStrict pairStrict (twoNuBelowPairRate alpha alphaOutput)
    in
    subst (λ selected → selected ≤ ceiling)
      (sym asPositiveReciprocal) antitone

  pairResolventPositive :
    (alpha : Physical.PhysicalTriadIncidence) →
    Physical.k alpha ≡ output →
    0ℚ < Swap.pairResolvent alpha beta
  pairResolventPositive alpha alphaOutput =
    let
      instance pairPositiveI : Positive (pairRate alpha)
      pairPositiveI = pairRatePositive alpha alphaOutput
      pairStrict : 0ℚ < pairRate alpha
      pairStrict = ℚP.positive⁻¹ (pairRate alpha)
      asPositiveReciprocal :
        Swap.pairResolvent alpha beta
        ≡ Quotient.positiveReciprocal (pairRate alpha) pairStrict
      positiveReciprocal = Quotient.positiveReciprocalPositive
        (pairRate alpha) pairStrict
    in
    subst (0ℚ <_) (sym asPositiveReciprocal) positiveReciprocal

  pairResolventSquareBelowCeilingSquare :
    (alpha : Physical.PhysicalTriadIncidence) →
    Physical.k alpha ≡ output →
    Swap.pairResolvent alpha beta * Swap.pairResolvent alpha beta
    ≤ ceiling * ceiling
  pairResolventSquareBelowCeilingSquare alpha alphaOutput =
    let
      r = Swap.pairResolvent alpha beta
      bound = pairResolventBelowCeiling alpha alphaOutput
      rNN = ℚP.<⇒≤ (pairResolventPositive alpha alphaOutput)
      first : r * r ≤ ceiling * r
      first =
        let instance rNNI : NonNegative r = nonNegative rNN
        in ℚP.*-monoʳ-≤-nonNeg r bound
      second : ceiling * r ≤ ceiling * ceiling
      second =
        let instance ceilingNNI : NonNegative ceiling = nonNegative ceilingNN
        in ℚP.*-monoˡ-≤-nonNeg ceiling bound
    in
    ℚP.≤-trans first second

  weightedCellNormMeaning :
    (alpha : Physical.PhysicalTriadIncidence) →
    L2.complex3NormSquared (Ledger.weightedAmplitudeCell beta alpha)
    ≡
    (Swap.pairResolvent alpha beta * Swap.pairResolvent alpha beta)
      * L2.complex3NormSquared (R224.mixedPlusMinus S velocity alpha)
  weightedCellNormMeaning alpha
    rewrite Spec.spectatorWeightMeaning beta alpha =
    trans
      (R174.normScale
        (C3.realEmbed F (Swap.pairResolvent alpha beta))
        (R224.mixedPlusMinus S velocity alpha))
      (cong
        (_* L2.complex3NormSquared (R224.mixedPlusMinus S velocity alpha))
        (R455.realEmbedModulusSquared (Swap.pairResolvent alpha beta)))

  inputProductMass : Physical.PhysicalTriadIncidence → ℚ
  inputProductMass alpha =
    L2.complex3NormSquared (velocity (Physical.p alpha))
      * L2.complex3NormSquared (velocity (Physical.q alpha))

  inputProductMassNN :
    (alpha : Physical.PhysicalTriadIncidence) →
    0ℚ ≤ inputProductMass alpha
  inputProductMassNN alpha =
    let
      pNN = Separation.complex3NormSquaredNonnegative (velocity (Physical.p alpha))
      qNN = Separation.complex3NormSquaredNonnegative (velocity (Physical.q alpha))
      instance pNNI = nonNegative pNN
      instance qNNI = nonNegative qNN
      instance productNNI = ℚP.nonNeg*nonNeg⇒nonNeg
        (L2.complex3NormSquared (velocity (Physical.p alpha)))
        (L2.complex3NormSquared (velocity (Physical.q alpha)))
    in
    ℚP.nonNegative⁻¹ (inputProductMass alpha)

  weightedCellMassBelow :
    (alpha : Physical.PhysicalTriadIncidence) →
    Physical.k alpha ≡ output →
    L2.complex3NormSquared (Ledger.weightedAmplitudeCell beta alpha)
    ≤ (ceiling * ceiling) * inputProductMass alpha
  weightedCellMassBelow alpha alphaOutput =
    let
      r = Swap.pairResolvent alpha beta
      rSquare = r * r
      mixed = R224.mixedPlusMinus S velocity alpha
      mixedBound = Cell.mixedPlusMinusCellBelowEnergyProduct
        E I S L velocity velocityTransverse alpha
      rSquareNN = Rational.squareNonnegative r
      scaleMixed :
        rSquare * L2.complex3NormSquared mixed
        ≤ rSquare * inputProductMass alpha
      scaleMixed =
        let instance rSquareNNI : NonNegative rSquare = nonNegative rSquareNN
        in ℚP.*-monoˡ-≤-nonNeg rSquare mixedBound
      scaleWeight :
        rSquare * inputProductMass alpha
        ≤ (ceiling * ceiling) * inputProductMass alpha
      scaleWeight =
        let instance inputNNI : NonNegative (inputProductMass alpha) =
              nonNegative (inputProductMassNN alpha)
        in ℚP.*-monoʳ-≤-nonNeg (inputProductMass alpha)
          (pairResolventSquareBelowCeilingSquare alpha alphaOutput)
      core = ℚP.≤-trans scaleMixed scaleWeight
    in
    subst
      (λ selected → selected ≤ (ceiling * ceiling) * inputProductMass alpha)
      (sym (weightedCellNormMeaning alpha)) core

  inputProductMassSum : List Physical.PhysicalTriadIncidence → ℚ
  inputProductMassSum [] = 0ℚ
  inputProductMassSum (alpha ∷ rest) =
    inputProductMass alpha + inputProductMassSum rest

  weightedCellMassSumBelow :
    (items : List Physical.PhysicalTriadIncidence) →
    ((alpha : Physical.PhysicalTriadIncidence) →
      alpha R396.OccursIn items → Physical.k alpha ≡ output) →
    R180.cellMassSum (Ledger.weightedAmplitudeCells beta items)
    ≤ (ceiling * ceiling) * inputProductMassSum items
  weightedCellMassSumBelow [] allOutput = ℚP.≤-refl
  weightedCellMassSumBelow (alpha ∷ rest) allOutput =
    let
      head = weightedCellMassBelow alpha (allOutput alpha R396.here)
      tailOutput :
        (selected : Physical.PhysicalTriadIncidence) →
        selected R396.OccursIn rest → Physical.k selected ≡ output
      tailOutput selected member = allOutput selected (R396.there member)
      tail = weightedCellMassSumBelow rest tailOutput
      added = ℚP.+-mono-≤ head tail
      endpoint :
        (ceiling * ceiling) * inputProductMass alpha
          + (ceiling * ceiling) * inputProductMassSum rest
        ≡ (ceiling * ceiling)
          * (inputProductMass alpha + inputProductMassSum rest)
      endpoint = solve
        (ceiling ∷ inputProductMass alpha ∷ inputProductMassSum rest ∷ [])
    in
    subst
      (λ upper →
        R180.cellMassSum (Ledger.weightedAmplitudeCells beta (alpha ∷ rest))
        ≤ upper)
      endpoint added

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

spectatorWeightCutoffIndependentCeilingClosed : Bool
spectatorWeightCutoffIndependentCeilingClosed = true

weightedAmplitudeCellMassEnergyConvolutionClosed : Bool
weightedAmplitudeCellMassEnergyConvolutionClosed = true

weightedAmplitudeCellMassIntroducesCardinalityTax : Bool
weightedAmplitudeCellMassIntroducesCardinalityTax = false

weightedAmplitudeGramDebtPaid : Bool
weightedAmplitudeGramDebtPaid = false

weightedAmplitudeSpacetimeEstimateClosed : Bool
weightedAmplitudeSpacetimeEstimateClosed = false

clayPromotion : Bool
clayPromotion = false
