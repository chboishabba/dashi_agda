{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650RateLiftedR568ToC2CommutatorRound687Exact where

------------------------------------------------------------------------
-- ROUND687 / PAIR-RATE-LIFTED R568 FORCING FULL = 8 * C2 COMMUTATOR WORK
--
-- On one nonzero physical fixed-output fibre:
--
--   ForcingPair_ab
--     = K_ab Re <DoubleForcing_a, DoubleCell_b>,
--
-- with K_ab (r_a+r_b) = 1.  Hence
--
--   (r_a+r_b) ForcingPair_ab
--     = Re <DoubleForcing_a, DoubleCell_b>.
--
-- The complete ordered square then factors.  R542 gives
--
--   sum_a DoubleForcing_a = 4 C
--
-- for the ordinary unweighted mixed commutator C, while R225 gives
--
--   sum_b DoubleCell_b = 4 M.
--
-- Since coherentWork = 2 Re <.,.>,
--
--   Full((r_a+r_b) ForcingPair_ab) = 8 coherentWork(M,C).
--
-- Thus the nonlinear local currency in R686 is exactly one eighth of the
-- pair-rate lift of the R568 forcing square.  No inequality is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; Positive; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNProjectedHelicalSelfForcingVectorRound106Exact as R106
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact as R396
import DASHI.Physics.Closure.NSTriadKNRationalPhysicalPairRatePositivityRound400Exact as R400
import DASHI.Physics.Closure.NSTriadKNOutputLocalSelectorFixedOutputReductionExact as OutputLocal
import DASHI.Physics.Closure.NSTriadKNSpectatorDoubleForcingCommutatorFoldRound542Exact as R542
import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543
import DASHI.Physics.Closure.NSTriadKNFactoredFullCommutatorOnlyRound567Exact as R567
import DASHI.Physics.Closure.NSTriadKNR567CauchyGramFluxNormalFormRound596Exact as R596
import DASHI.Physics.Closure.NSTriadKNCauchyResolvedFullSquareRateCancellationExact as R595
import DASHI.Physics.Closure.NSTriadKNA3CenteredCauchyPairNormalFormRound600Exact as R600

F : C3.RealField _
F = Rational.rationalRealField

eight : ℚ
eight = 8

pairRateLift :
  ∀ {A : Set} →
  (A → ℚ) →
  (A → A → ℚ) →
  A → A → ℚ
pairRateLift rate pair alpha beta =
  (rate alpha + rate beta) * pair alpha beta

module FixedOutput
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (viscosityPositive : Positive (Field30.viscosity physicalSystem))
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output) where

  module Base =
    R596.FixedOutput physicalSystem S viscosityPositive output outputNonzero
  module Rate = R400.PhysicalRate physicalSystem S viscosityPositive
  module Resolved = R595.PhysicalResolved physicalSystem S
  module OnOutput =
    Resolved.OnNonzeroOutput viscosityPositive output outputNonzero
  module C = R567.CommutatorOnly physicalSystem S
  module T = C.T
  module Row = T.Row
  module D = Row.D

  cutoff = Base.cutoff
  fibre : List Physical.PhysicalTriadIncidence
  fibre = Base.fibre

  rate : Physical.PhysicalTriadIncidence → ℚ
  rate = Resolved.cellRate

  forcingPair :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  forcingPair = T.forcingPair

  liftedForcingPair :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  liftedForcingPair = pairRateLift rate forcingPair

  rawCrossPair :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  rawCrossPair alpha beta =
    R179.realHermitianCross
      (D.doubleForcing alpha)
      (Row.doubleCell beta)

  liftedPointwiseOnOutput :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    Physical.k alpha ≡ output →
    Physical.k beta ≡ output →
    liftedForcingPair alpha beta ≡ rawCrossPair alpha beta
  liftedPointwiseOnOutput alpha beta alphaOutput betaOutput
    rewrite T.forcingPairScalarized alpha beta
          | OnOutput.physicalPairResolventLawOnOutput
              alpha beta alphaOutput betaOutput =
    solve
      ( rate alpha
      ∷ rate beta
      ∷ T.Swap.pairResolvent alpha beta
      ∷ rawCrossPair alpha beta
      ∷ [])

  rowCongruentOnOutput :
    (alpha : Physical.PhysicalTriadIncidence) →
    Physical.k alpha ≡ output →
    (items : List Physical.PhysicalTriadIncidence) →
    ((beta : Physical.PhysicalTriadIncidence) →
      beta R396.OccursIn items → Physical.k beta ≡ output) →
    R539.rowSum liftedForcingPair alpha items
    ≡ R539.rowSum rawCrossPair alpha items
  rowCongruentOnOutput alpha alphaOutput [] allOutput = refl
  rowCongruentOnOutput alpha alphaOutput (beta ∷ rest) allOutput =
    cong₂ _+_
      (liftedPointwiseOnOutput
        alpha beta alphaOutput (allOutput beta R396.here))
      (rowCongruentOnOutput
        alpha alphaOutput rest
        (λ gamma member → allOutput gamma (R396.there member)))

  columnCongruentOnOutput :
    (items : List Physical.PhysicalTriadIncidence) →
    ((alpha : Physical.PhysicalTriadIncidence) →
      alpha R396.OccursIn items → Physical.k alpha ≡ output) →
    (beta : Physical.PhysicalTriadIncidence) →
    Physical.k beta ≡ output →
    R539.columnSum liftedForcingPair items beta
    ≡ R539.columnSum rawCrossPair items beta
  columnCongruentOnOutput [] allOutput beta betaOutput = refl
  columnCongruentOnOutput (alpha ∷ rest) allOutput beta betaOutput =
    cong₂ _+_
      (liftedPointwiseOnOutput
        alpha beta (allOutput alpha R396.here) betaOutput)
      (columnCongruentOnOutput
        rest
        (λ gamma member → allOutput gamma (R396.there member))
        beta betaOutput)

  fullSquareCongruentOnOutput :
    (items : List Physical.PhysicalTriadIncidence) →
    ((alpha : Physical.PhysicalTriadIncidence) →
      alpha R396.OccursIn items → Physical.k alpha ≡ output) →
    R543.fullSquareSum liftedForcingPair items
    ≡ R543.fullSquareSum rawCrossPair items
  fullSquareCongruentOnOutput [] allOutput = refl
  fullSquareCongruentOnOutput (alpha ∷ rest) allOutput
    rewrite
      liftedPointwiseOnOutput
        alpha alpha
        (allOutput alpha R396.here)
        (allOutput alpha R396.here)
      | rowCongruentOnOutput
          alpha
          (allOutput alpha R396.here)
          rest
          (λ beta member → allOutput beta (R396.there member))
      | columnCongruentOnOutput
          rest
          (λ beta member → allOutput beta (R396.there member))
          alpha
          (allOutput alpha R396.here)
      | fullSquareCongruentOnOutput
          rest
          (λ beta member → allOutput beta (R396.there member)) =
    refl

  liftedFullIsRawCrossFull :
    R543.fullSquareSum liftedForcingPair fibre
    ≡ R543.fullSquareSum rawCrossPair fibre
  liftedFullIsRawCrossFull =
    fullSquareCongruentOnOutput
      fibre
      (Rate.allElementsHaveOutput cutoff output)

  coherentPair :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  coherentPair alpha beta =
    Work.coherentWork
      (D.doubleForcing alpha)
      (Row.doubleCell beta)

  coherentPairIsTwiceRaw :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    coherentPair alpha beta
    ≡ R291.two * rawCrossPair alpha beta
  coherentPairIsTwiceRaw alpha beta = refl

  coherentFullIsTwiceRawFull :
    R543.fullSquareSum coherentPair fibre
    ≡ R291.two * R543.fullSquareSum rawCrossPair fibre
  coherentFullIsTwiceRawFull =
    trans
      (R595.fullSquareCongruent
        coherentPair
        (R600.scaledPair R291.two rawCrossPair)
        coherentPairIsTwiceRaw
        fibre)
      (R600.fullSquareScale R291.two rawCrossPair fibre)

  coherentFullFactors :
    R543.fullSquareSum coherentPair fibre
    ≡ Work.coherentWork
        (R224.foldVector D.doubleForcing fibre)
        (R224.foldVector Row.doubleCell fibre)
  coherentFullFactors =
    R600.fullWorkLRFactors D.doubleForcing Row.doubleCell fibre

  allSelected : Z3.FourierMode → Bool
  allSelected _ = true

  unitWeight : R294.SwapInvariantCellWeight F
  unitWeight =
    OutputLocal.outputLocalSwapInvariantWeight F allSelected

  module Unit = R542.Fold physicalSystem S unitWeight

  weightedDoubleIsDouble :
    (tau : Physical.PhysicalTriadIncidence) →
    Unit.weightedDouble tau ≡ D.doubleForcing tau
  weightedDoubleIsDouble tau
    rewrite R106.complex3ScaleOne (D.doubleForcing tau) =
    refl

  weightedDoubleFoldIsDoubleFold :
    (items : List Physical.PhysicalTriadIncidence) →
    R224.foldVector Unit.weightedDouble items
    ≡ R224.foldVector D.doubleForcing items
  weightedDoubleFoldIsDoubleFold [] = refl
  weightedDoubleFoldIsDoubleFold (tau ∷ rest) =
    cong₂ C3.complex3Add
      (weightedDoubleIsDouble tau)
      (weightedDoubleFoldIsDoubleFold rest)

  unitCommutatorFoldIsUnweighted :
    R224.foldVector Unit.commutator fibre
    ≡ Work.fixedOutputCommutator
        S
        (Audit.velocityAt (Field30.finiteSystem physicalSystem))
        (Audit.projectedNonlinearity (Field30.finiteSystem physicalSystem))
        cutoff output
  unitCommutatorFoldIsUnweighted =
    OutputLocal.outputLocalActiveFixedOutputReduction
      allSelected output refl
      S
      (Audit.velocityAt (Field30.finiteSystem physicalSystem))
      (Audit.projectedNonlinearity (Field30.finiteSystem physicalSystem))
      cutoff

  fourCommutator :
    C3.Complex3 F
  fourCommutator =
    let
      C0 = Work.fixedOutputCommutator
        S
        (Audit.velocityAt (Field30.finiteSystem physicalSystem))
        (Audit.projectedNonlinearity (Field30.finiteSystem physicalSystem))
        cutoff output
    in
    C3.complex3Add (C3.complex3Add C0 C0) (C3.complex3Add C0 C0)

  doubleForcingFoldIsFourCommutator :
    R224.foldVector D.doubleForcing fibre ≡ fourCommutator
  doubleForcingFoldIsFourCommutator =
    trans
      (sym (weightedDoubleFoldIsDoubleFold fibre))
      (trans
        (Unit.fixedOutputWeightedDoubleIsFourCommutatorFolds output)
        (cong
          (λ C0 →
            C3.complex3Add
              (C3.complex3Add C0 C0)
              (C3.complex3Add C0 C0))
          unitCommutatorFoldIsUnweighted))

  mixed :
    C3.Complex3 F
  mixed =
    Work.fixedOutputMixedProduct
      S
      (Audit.velocityAt (Field30.finiteSystem physicalSystem))
      cutoff output

  doubleCellFoldIsFourMixed :
    R224.foldVector Row.doubleCell fibre
    ≡ R225.fourCopies mixed
  doubleCellFoldIsFourMixed =
    R225.fixedOutputDoubleMixedSumIsFourPlusMinusSum
      S
      (Audit.velocityAt (Field30.finiteSystem physicalSystem))
      cutoff output

  commutator :
    C3.Complex3 F
  commutator =
    Work.fixedOutputCommutator
      S
      (Audit.velocityAt (Field30.finiteSystem physicalSystem))
      (Audit.projectedNonlinearity (Field30.finiteSystem physicalSystem))
      cutoff output

  foldedCoherentWorkIsSixteenCommutatorWork :
    Work.coherentWork
      (R224.foldVector D.doubleForcing fibre)
      (R224.foldVector Row.doubleCell fibre)
    ≡
    (R291.two * eight) * Work.coherentWork commutator mixed
  foldedCoherentWorkIsSixteenCommutatorWork
    rewrite doubleForcingFoldIsFourCommutator
          | doubleCellFoldIsFourMixed =
    solve
      ( R179.realHermitianCross commutator mixed
      ∷ [])

  liftedForcingFullIsEightCommutatorWork :
    R543.fullSquareSum liftedForcingPair fibre
    ≡ eight * Work.coherentWork mixed commutator
  liftedForcingFullIsEightCommutatorWork =
    let
      raw = R543.fullSquareSum rawCrossPair fibre
      coh = R543.fullSquareSum coherentPair fibre
      commWork = Work.coherentWork mixed commutator

      twoRawIsSixteen :
        R291.two * raw ≡ (R291.two * eight) * commWork
      twoRawIsSixteen =
        trans
          (sym coherentFullIsTwiceRawFull)
          (trans coherentFullFactors
            foldedCoherentWorkIsSixteenCommutatorWork)

      rawIsEight : raw ≡ eight * commWork
      rawIsEight =
        solve
          ( raw
          ∷ commWork
          ∷ [])
    in
    trans liftedFullIsRawCrossFull rawIsEight

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round687RateLiftedR568ForcingFullIsEightC2CommutatorWork : Bool
round687RateLiftedR568ForcingFullIsEightC2CommutatorWork = true

round687UsesNonzeroOutputReciprocalPremise : Bool
round687UsesNonzeroOutputReciprocalPremise = true

round687IntroducesEstimate : Bool
round687IntroducesEstimate = false

round687UnliftedR568BudgetControlsRateLiftedFull : Bool
round687UnliftedR568BudgetControlsRateLiftedFull = false

round687RateLiftedCutoffUniformSpacetimeBoundClosed : Bool
round687RateLiftedCutoffUniformSpacetimeBoundClosed = false

round687C1Closed : Bool
round687C1Closed = false

round687C2Closed : Bool
round687C2Closed = false

round687IntroducesNewClayLeaf : Bool
round687IntroducesNewClayLeaf = false

round687ClayPromotion : Bool
round687ClayPromotion = false

round687RateLiftedR568ForcingFullIsEightC2CommutatorWorkIsTrue :
  round687RateLiftedR568ForcingFullIsEightC2CommutatorWork ≡ true
round687RateLiftedR568ForcingFullIsEightC2CommutatorWorkIsTrue = refl

round687UsesNonzeroOutputReciprocalPremiseIsTrue :
  round687UsesNonzeroOutputReciprocalPremise ≡ true
round687UsesNonzeroOutputReciprocalPremiseIsTrue = refl

round687IntroducesEstimateIsFalse :
  round687IntroducesEstimate ≡ false
round687IntroducesEstimateIsFalse = refl

round687UnliftedR568BudgetControlsRateLiftedFullIsFalse :
  round687UnliftedR568BudgetControlsRateLiftedFull ≡ false
round687UnliftedR568BudgetControlsRateLiftedFullIsFalse = refl

round687RateLiftedCutoffUniformSpacetimeBoundClosedIsFalse :
  round687RateLiftedCutoffUniformSpacetimeBoundClosed ≡ false
round687RateLiftedCutoffUniformSpacetimeBoundClosedIsFalse = refl

round687C1ClosedIsFalse :
  round687C1Closed ≡ false
round687C1ClosedIsFalse = refl

round687C2ClosedIsFalse :
  round687C2Closed ≡ false
round687C2ClosedIsFalse = refl

round687IntroducesNewClayLeafIsFalse :
  round687IntroducesNewClayLeaf ≡ false
round687IntroducesNewClayLeafIsFalse = refl

round687ClayPromotionIsFalse :
  round687ClayPromotion ≡ false
round687ClayPromotionIsFalse = refl
