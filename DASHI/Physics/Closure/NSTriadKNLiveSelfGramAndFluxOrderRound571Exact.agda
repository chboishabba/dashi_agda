module DASHI.Physics.Closure.NSTriadKNLiveSelfGramAndFluxOrderRound571Exact where

------------------------------------------------------------------------
-- ROUND571 / SOURCE-CONSTRUCT POINTWISE FAVOURABLE SIGNS; ISOLATE INTEGRAL ORDER
--
-- R553 needs two order facts after the reduced identity is integrated:
--
--   0 <= integral selfGram,
--   0 <= terminal selfFlux.
--
-- The pointwise signs are not novel analysis.  SelfGram is twice a self-
-- Hermitian square; selfFlux is twice the positive Cauchy diagonal.  Both are
-- already finite rational facts in R451/R554.  This owner reconstructs those
-- signs on the exact live R556/R564 carriers.
--
-- The only remaining integration-order authority is the standard implication
--
--   (forall t, 0 <= f t) -> 0 <= integral f.
--
-- It is kept explicit because R495 intentionally owns equality/additivity only.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; NonNegative; nonNegative; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNPhysicalDiagonalR298WeldRound451Exact as R451
import DASHI.Physics.Closure.NSTriadKNLiteralDiagonalSumDecompositionRound550Exact as R550
import DASHI.Physics.Closure.NSTriadKNDiagonalSelfFluxToR447Round549Exact as R549
import DASHI.Physics.Closure.NSTriadKNDiagonalSelfFluxEndpointCompilerRound554Exact as R554
import DASHI.Physics.Closure.NSTriadKNLiveR406DiagonalReducedNormalFormRound556Exact as R556
import DASHI.Physics.Closure.NSTriadKNLiveIntegratedDiagonalReducedNormalFormRound557Exact as R557
import DASHI.Physics.Closure.NSTriadKNLiteralSelfFluxDerivativeClosedRound563Exact as R563
import DASHI.Physics.Closure.NSTriadKNLiveGlobalSelfFluxDerivativeRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = Rational.rationalRealField

record NonnegativeIntegrationAuthority571
    (Time : Set)
    (integrateTo : (Time → ℚ) → Time → ℚ) : Set₁ where
  field
    integrateNonnegative571 :
      (f : Time → ℚ) →
      ((time : Time) → 0ℚ ≤ f time) →
      (terminal : Time) →
      0ℚ ≤ integrateTo f terminal

open NonnegativeIntegrationAuthority571 public

twoNonnegative571 : 0ℚ ≤ R291.two
twoNonnegative571 = Rational.addNonnegative ℚP.0≤1 ℚP.0≤1

module LiveOrder
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf :
      (Time → ℚ) → (Time → ℚ) → Set)
    (projectedCrossCalculus :
      R426.ProjectedCrossDerivativeCalculus Time VectorDerivativeOf)
    (vectorAlgebra : R425.VectorDerivativeAlgebra Time VectorDerivativeOf)
    (hermitianCalculus :
      R417.HermitianDerivativeCalculus
        Time VectorDerivativeOf ScalarDerivativeOf)
    (constantCalculus :
      R416.ScalarConstantDerivativeCalculus Time ScalarDerivativeOf)
    (scalarAlgebra : R412.ScalarDerivativeAlgebra Time ScalarDerivativeOf)
    (integration : R495.IntegrationTransportAuthority Time integrateTo)
    (D : R408.LiteralDynamics.LiteralRHSTrajectoryData
      Time initialTime integrateTo VectorDerivativeOf)
    (R : R405.LiteralCutoffSupport.LiteralNonzeroCutoffTrajectory
      Time initialTime integrateTo VectorDerivativeOf
      (R408.LiteralDynamics.literalPhysicalTrajectory
        Time initialTime integrateTo VectorDerivativeOf D))
    (cutoff : Nat) where

  module Literal = R408.LiteralDynamics
    Time initialTime integrateTo VectorDerivativeOf
  module Reduced = R556.LiveReduced
    Time initialTime integrateTo VectorDerivativeOf
  module Integrated = R557.LiveIntegrated
    Time initialTime integrateTo VectorDerivativeOf integration
  module GlobalFlux = R564.LiveGlobalDerivative
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCrossCalculus vectorAlgebra hermitianCalculus
    constantCalculus scalarAlgebra D R cutoff

  T = Literal.literalPhysicalTrajectory D

  module At (time : Time) where
    module Slice = Reduced.At T R cutoff time

    diagonalGramNonnegative :
      (output : Z3.FourierMode) →
      (outputNonzero : Z3.NonZeroMode output) →
      (alpha : Physical.PhysicalTriadIncidence) →
      Physical.k alpha ≡ output →
      let module Diag = R550.LiteralDiagonal
            Slice.PS Slice.S
            (Reduced.Flux.Live.stateViscosityPositive
              T Slice.Slice.support cutoff time)
            cutoff output outputNonzero
      in
      0ℚ ≤ Diag.Diag.diagonalGram alpha
        (Diag.selfPositive alpha _)
    diagonalGramNonnegative output outputNonzero alpha outputExact =
      let
        module Diag = R550.LiteralDiagonal
          Slice.PS Slice.S
          (Reduced.Flux.Live.stateViscosityPositive
            T Slice.Slice.support cutoff time)
          cutoff output outputNonzero
        pair = Diag.Pair.physicalDoubleMixedPair alpha alpha
        crossNN = R451.selfHermitianNonnegative (R291.cellA pair)
        instance
          twoNNI : NonNegative R291.two
          twoNNI = nonNegative twoNonnegative571
          crossNNI : NonNegative
            (DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact.realHermitianCross
              (R291.cellA pair) (R291.cellA pair))
          crossNNI = nonNegative crossNN
          productNNI = ℚP.nonNeg*nonNeg⇒nonNeg R291.two
            (DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact.realHermitianCross
              (R291.cellA pair) (R291.cellA pair))
      in
      ℚP.nonNegative⁻¹ _

    outputSelfGramNonnegative :
      (output : Z3.FourierMode) →
      (outputNonzero : Z3.NonZeroMode output) →
      let module Diag = R550.LiteralDiagonal
            Slice.PS Slice.S
            (Reduced.Flux.Live.stateViscosityPositive
              T Slice.Slice.support cutoff time)
            cutoff output outputNonzero
      in 0ℚ ≤ Diag.literalSelfGramSum
    outputSelfGramNonnegative output outputNonzero =
      let
        module Diag = R550.LiteralDiagonal
          Slice.PS Slice.S
          (Reduced.Flux.Live.stateViscosityPositive
            T Slice.Slice.support cutoff time)
          cutoff output outputNonzero

        go :
          (items : List Physical.PhysicalTriadIncidence) →
          (allOutput :
            (alpha : Physical.PhysicalTriadIncidence) →
            alpha DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact.OccursIn items →
            Physical.k alpha ≡ output) →
          0ℚ ≤ Diag.sumSelfGram items allOutput
        go [] allOutput = ℚP.≤-refl
        go (alpha ∷ rest) allOutput =
          Rational.addNonnegative
            (diagonalGramNonnegative output outputNonzero alpha
              (allOutput alpha
                DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact.here))
            (go rest
              (λ beta member → allOutput beta
                (DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact.there member)))
      in
      go Diag.fibre (Diag.Rate.allElementsHaveOutput cutoff output)

    selectedGlobalSelfGramNonnegative :
      (selected : List Z3.FourierMode) →
      (nonzero : Slice.GR.OutputsNonzero selected) →
      0ℚ ≤ Slice.GR.globalSelfGram cutoff selected nonzero
    selectedGlobalSelfGramNonnegative [] Slice.GR.nonzeroNil = ℚP.≤-refl
    selectedGlobalSelfGramNonnegative (output ∷ rest)
        (Slice.GR.nonzeroCons outputNonzero tailNonzero) =
      Rational.addNonnegative
        (outputSelfGramNonnegative output outputNonzero)
        (selectedGlobalSelfGramNonnegative rest tailNonzero)

    liveSelfGramNonnegative571 :
      0ℚ ≤ Integrated.selfGram T R cutoff time
    liveSelfGramNonnegative571 =
      selectedGlobalSelfGramNonnegative
        Slice.Slice.outputs Slice.canonicalOutputsNonzero

    selectedGlobalSelfFluxNonnegative :
      (selected : List Z3.FourierMode) →
      (allNonzero :
        (output : Z3.FourierMode) →
        output Cube.∈ selected → Z3.NonZeroMode output) →
      0ℚ ≤ R412.sumCurves
        (GlobalFlux.outputFluxCurves selected allNonzero) time
    selectedGlobalSelfFluxNonnegative [] allNonzero = ℚP.≤-refl
    selectedGlobalSelfFluxNonnegative (output ∷ rest) allNonzero =
      let
        outputNN = allNonzero output (Cube.here refl)
        module One = R563.ClosedDerivative
          Time initialTime integrateTo VectorDerivativeOf ScalarDerivativeOf
          projectedCrossCalculus vectorAlgebra hermitianCalculus constantCalculus
          scalarAlgebra D R cutoff output outputNN
        module FluxOut = R549.PhysicalSelfFlux
          (One.Family.PS time) One.Family.S
          (One.Family.viscosityPositiveAt time)
          cutoff output outputNN

        diagonalNN : 0ℚ ≤ FluxOut.Completion.diagonal
        diagonalNN = R554.diagonalFormNonnegative FluxOut.Completion.physicalCells

        scaledNN : 0ℚ ≤ R549.two * FluxOut.Completion.diagonal
        scaledNN =
          let
            instance
              twoNNI : NonNegative R549.two
              twoNNI = nonNegative twoNonnegative571
              diagonalNNI : NonNegative FluxOut.Completion.diagonal
              diagonalNNI = nonNegative diagonalNN
              productNNI = ℚP.nonNeg*nonNeg⇒nonNeg
                R549.two FluxOut.Completion.diagonal
          in ℚP.nonNegative⁻¹ _

        headNN : 0ℚ ≤ One.Family.selfFlux time
        headNN = subst (0ℚ ≤_)
          (sym FluxOut.literalSelfFluxIsTwiceR447Diagonal) scaledNN
      in
      Rational.addNonnegative headNN
        (selectedGlobalSelfFluxNonnegative rest
          (λ selected member → allNonzero selected (Cube.there member)))

    liveGlobalSelfFluxNonnegative571 :
      0ℚ ≤ GlobalFlux.globalSelfFlux time
    liveGlobalSelfFluxNonnegative571 =
      selectedGlobalSelfFluxNonnegative
        GlobalFlux.outputs GlobalFlux.canonicalNonzero

  integratedLiveSelfGramNonnegative571 :
    NonnegativeIntegrationAuthority571 Time integrateTo →
    (terminal : Time) →
    0ℚ ≤ integrateTo (Integrated.selfGram T R cutoff) terminal
  integratedLiveSelfGramNonnegative571 order terminal =
    integrateNonnegative571 order
      (Integrated.selfGram T R cutoff)
      (λ time → At.liveSelfGramNonnegative571 time)
      terminal

round571PointwiseLiveSelfGramNonnegativeClosed : Bool
round571PointwiseLiveSelfGramNonnegativeClosed = true

round571PointwiseLiveGlobalSelfFluxNonnegativeClosed : Bool
round571PointwiseLiveGlobalSelfFluxNonnegativeClosed = true

round571IntegralOrderStillStandardAuthority : Bool
round571IntegralOrderStillStandardAuthority = true

round571NewNavierStokesEstimateIntroduced : Bool
round571NewNavierStokesEstimateIntroduced = false

round571CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round571CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round571ClayPromotion : Bool
round571ClayPromotion = false

round571ClayPromotionIsFalse : round571ClayPromotion ≡ false
round571ClayPromotionIsFalse = refl
