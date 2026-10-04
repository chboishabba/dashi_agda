module DASHI.Physics.Closure.NSTriadKNLiteralOffDiagonalFluxFixedOutputFamilyMaxCutExact where

------------------------------------------------------------------------
-- POSITIVE B7 Q4+E / FIXED-OUTPUT OFF-DIAGONAL R290 DERIVATIVE FAMILY
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (_++_)
open import Data.Rational using (Positive)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNPhysicalTrajectoryRetainedGlobalFluxRound403Exact as R403
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNR418FinitePairFamilyToR409Round422Exact as R422
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact as R290
import DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact as R396
import DASHI.Physics.Closure.NSTriadKNRationalPhysicalPairRatePositivityRound400Exact as R400
import DASHI.Physics.Closure.NSTriadKNFiniteWeightedGramFluxAggregationRound385Exact as R385
import DASHI.Physics.Closure.NSTriadKNLiteralLiveOffDiagonalPairDerivativeMaxCutExact as OnePair

F : C3.RealField _
F = Rational.rationalRealField

module FixedOutputFamily
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (crossCalculus : R426.ProjectedCrossDerivativeCalculus Time DerivativeOf)
    (vectorAlgebra : R425.VectorDerivativeAlgebra Time DerivativeOf)
    (D : R408.LiteralDynamics.LiteralRHSTrajectoryData
      Time initialTime integrateTo DerivativeOf)
    (R : R405.LiteralCutoffSupport.LiteralNonzeroCutoffTrajectory
      Time initialTime integrateTo DerivativeOf
      (R408.LiteralDynamics.literalPhysicalTrajectory
        Time initialTime integrateTo DerivativeOf D))
    (cutoff : Nat)
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output) where

  module Literal = R408.LiteralDynamics
    Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Live = R403.LiveTrajectoryFlux
    Time initialTime integrateTo DerivativeOf

  T = Literal.literalPhysicalTrajectory D
  support = Support.toRetainedSupportRealization T R
  S = Literal.Base.S (Literal.stateTrajectory (Literal.support D))

  fibre : List Physical.PhysicalTriadIncidence
  fibre = Output.physicalOutputFiber cutoff output

  PS : Time → Field30.PhysicalFiniteComplex3GalerkinSystem F
  PS time = Live.physicalSystemAt T support cutoff time

  module Rate0 = R400.PhysicalRate
    (PS initialTime) S (Live.stateViscosityPositive T support cutoff initialTime)

  allOutput :
    (alpha : Physical.PhysicalTriadIncidence) →
    alpha R396.OccursIn fibre → Physical.k alpha ≡ output
  allOutput = Rate0.allElementsHaveOutput cutoff output

  buildHeadData :
    (alpha : Physical.PhysicalTriadIncidence) →
    (alphaOutput : Physical.k alpha ≡ output) →
    (rest : List Physical.PhysicalTriadIncidence) →
    ((beta : Physical.PhysicalTriadIncidence) →
      beta R396.OccursIn rest → Physical.k beta ≡ output) →
    List (R422.PairCurveDerivativeData Time DerivativeOf)
  buildHeadData alpha alphaOutput [] restOutput = []
  buildHeadData alpha alphaOutput (beta ∷ rest) restOutput =
    let
      module One = OnePair.LiteralOffDiagonalPairDerivative
        Time initialTime integrateTo DerivativeOf
        crossCalculus vectorAlgebra D R cutoff output outputNonzero
        alpha beta alphaOutput (restOutput beta R396.here)
    in
    One.literalOffDiagonalPairDerivativeData ∷
      buildHeadData alpha alphaOutput rest
        (λ gamma member → restOutput gamma (R396.there member))

  buildAllData :
    (items : List Physical.PhysicalTriadIncidence) →
    ((alpha : Physical.PhysicalTriadIncidence) →
      alpha R396.OccursIn items → Physical.k alpha ≡ output) →
    List (R422.PairCurveDerivativeData Time DerivativeOf)
  buildAllData [] itemOutput = []
  buildAllData (alpha ∷ rest) itemOutput =
    buildHeadData alpha (itemOutput alpha R396.here) rest
      (λ beta member → itemOutput beta (R396.there member))
    ++ buildAllData rest
      (λ beta member → itemOutput beta (R396.there member))

  pairCurves : List (R422.PairCurveDerivativeData Time DerivativeOf)
  pairCurves = buildAllData fibre allOutput

  sumCurvesAppend :
    (curves more : List (R422.PairCurveDerivativeData Time DerivativeOf)) →
    (time : Time) →
    R412.sumCurves (R422.fluxTerms (curves ++ more)) time
    ≡ R412.sumCurves (R422.fluxTerms curves) time
      + R412.sumCurves (R422.fluxTerms more) time
  sumCurvesAppend [] more time = refl
  sumCurvesAppend (curve ∷ curves) more time
    rewrite sumCurvesAppend curves more time = refl

  sumTangentCurvesAppend :
    (curves more : List (R422.PairCurveDerivativeData Time DerivativeOf)) →
    (time : Time) →
    R412.sumCurves (R422.tangentTerms (curves ++ more)) time
    ≡ R412.sumCurves (R422.tangentTerms curves) time
      + R412.sumCurves (R422.tangentTerms more) time
  sumTangentCurvesAppend [] more time = refl
  sumTangentCurvesAppend (curve ∷ curves) more time
    rewrite sumTangentCurvesAppend curves more time = refl

  sumFluxAppend :
    (left right : List R290.DampedGramPair) →
    R385.sumWeightedFlux (left ++ right)
    ≡ R385.sumWeightedFlux left + R385.sumWeightedFlux right
  sumFluxAppend [] right = refl
  sumFluxAppend (pair ∷ rest) right
    rewrite sumFluxAppend rest right = refl

  sumTangentAppend :
    (left right : List R290.DampedGramPair) →
    R385.sumWeightedFluxTangent (left ++ right)
    ≡ R385.sumWeightedFluxTangent left
      + R385.sumWeightedFluxTangent right
  sumTangentAppend [] right = refl
  sumTangentAppend (pair ∷ rest) right
    rewrite sumTangentAppend rest right = refl

  headFluxExact :
    (time : Time) →
    let module Local = R396.LocalEnumerate (PS time) S in
    (alpha : Physical.PhysicalTriadIncidence) →
    (alphaOutput : Physical.k alpha ≡ output) →
    (rest : List Physical.PhysicalTriadIncidence) →
    (restOutput :
      (beta : Physical.PhysicalTriadIncidence) →
      beta R396.OccursIn rest → Physical.k beta ≡ output) →
    (positive :
      (beta : Physical.PhysicalTriadIncidence) →
      beta R396.OccursIn rest →
      Positive (R291.pairRate (Local.P.physicalDoubleMixedPair alpha beta))) →
    R412.sumCurves
      (R422.fluxTerms (buildHeadData alpha alphaOutput rest restOutput)) time
    ≡ R385.sumWeightedFlux (Local.headR290Pairs alpha rest positive)
  headFluxExact time alpha alphaOutput [] restOutput positive = refl
  headFluxExact time alpha alphaOutput (beta ∷ rest) restOutput positive =
    cong₂ _+_ refl
      (headFluxExact time alpha alphaOutput rest
        (λ gamma member → restOutput gamma (R396.there member))
        (λ gamma member → positive gamma (R396.there member)))

  headTangentExact :
    (time : Time) →
    let module Local = R396.LocalEnumerate (PS time) S in
    (alpha : Physical.PhysicalTriadIncidence) →
    (alphaOutput : Physical.k alpha ≡ output) →
    (rest : List Physical.PhysicalTriadIncidence) →
    (restOutput :
      (beta : Physical.PhysicalTriadIncidence) →
      beta R396.OccursIn rest → Physical.k beta ≡ output) →
    (positive :
      (beta : Physical.PhysicalTriadIncidence) →
      beta R396.OccursIn rest →
      Positive (R291.pairRate (Local.P.physicalDoubleMixedPair alpha beta))) →
    R412.sumCurves
      (R422.tangentTerms (buildHeadData alpha alphaOutput rest restOutput)) time
    ≡ R385.sumWeightedFluxTangent (Local.headR290Pairs alpha rest positive)
  headTangentExact time alpha alphaOutput [] restOutput positive = refl
  headTangentExact time alpha alphaOutput (beta ∷ rest) restOutput positive =
    cong₂ _+_ refl
      (headTangentExact time alpha alphaOutput rest
        (λ gamma member → restOutput gamma (R396.there member))
        (λ gamma member → positive gamma (R396.there member)))

  allFluxExact :
    (time : Time) →
    let
      module Local = R396.LocalEnumerate (PS time) S
      module Rate = R400.PhysicalRate
        (PS time) S (Live.stateViscosityPositive T support cutoff time)
      positive = Rate.physicalOutputFibrePairRatesPositive
        cutoff output outputNonzero
    in
    R412.sumCurves (R422.fluxTerms pairCurves) time
    ≡ R385.sumWeightedFlux (Local.allR290Pairs fibre positive)
  allFluxExact time = go fibre allOutput positive
    where
    module Local = R396.LocalEnumerate (PS time) S
    module Rate = R400.PhysicalRate
      (PS time) S (Live.stateViscosityPositive T support cutoff time)
    positive = Rate.physicalOutputFibrePairRatesPositive cutoff output outputNonzero

    go :
      (items : List Physical.PhysicalTriadIncidence) →
      (itemOutput :
        (alpha : Physical.PhysicalTriadIncidence) →
        alpha R396.OccursIn items → Physical.k alpha ≡ output) →
      (pos : Local.PairRatePositiveOn items) →
      R412.sumCurves (R422.fluxTerms (buildAllData items itemOutput)) time
      ≡ R385.sumWeightedFlux (Local.allR290Pairs items pos)
    go [] itemOutput Local.positiveNil = refl
    go (alpha ∷ rest) itemOutput (Local.positiveCons headPositive tailPositive) =
      trans
        (sumCurvesAppend
          (buildHeadData alpha (itemOutput alpha R396.here) rest
            (λ beta member → itemOutput beta (R396.there member)))
          (buildAllData rest
            (λ beta member → itemOutput beta (R396.there member))) time)
        (trans
          (cong₂ _+_
            (headFluxExact time alpha (itemOutput alpha R396.here) rest
              (λ beta member → itemOutput beta (R396.there member)) headPositive)
            (go rest
              (λ beta member → itemOutput beta (R396.there member)) tailPositive))
          (symEq (sumFluxAppend
            (Local.headR290Pairs alpha rest headPositive)
            (Local.allR290Pairs rest tailPositive))))
      where
      symEq : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
      symEq refl = refl

  allTangentExact :
    (time : Time) →
    let
      module Local = R396.LocalEnumerate (PS time) S
      module Rate = R400.PhysicalRate
        (PS time) S (Live.stateViscosityPositive T support cutoff time)
      positive = Rate.physicalOutputFibrePairRatesPositive
        cutoff output outputNonzero
    in
    R412.sumCurves (R422.tangentTerms pairCurves) time
    ≡ R385.sumWeightedFluxTangent (Local.allR290Pairs fibre positive)
  allTangentExact time = go fibre allOutput positive
    where
    module Local = R396.LocalEnumerate (PS time) S
    module Rate = R400.PhysicalRate
      (PS time) S (Live.stateViscosityPositive T support cutoff time)
    positive = Rate.physicalOutputFibrePairRatesPositive cutoff output outputNonzero

    go :
      (items : List Physical.PhysicalTriadIncidence) →
      (itemOutput :
        (alpha : Physical.PhysicalTriadIncidence) →
        alpha R396.OccursIn items → Physical.k alpha ≡ output) →
      (pos : Local.PairRatePositiveOn items) →
      R412.sumCurves (R422.tangentTerms (buildAllData items itemOutput)) time
      ≡ R385.sumWeightedFluxTangent (Local.allR290Pairs items pos)
    go [] itemOutput Local.positiveNil = refl
    go (alpha ∷ rest) itemOutput (Local.positiveCons headPositive tailPositive) =
      trans
        (sumTangentCurvesAppend
          (buildHeadData alpha (itemOutput alpha R396.here) rest
            (λ beta member → itemOutput beta (R396.there member)))
          (buildAllData rest
            (λ beta member → itemOutput beta (R396.there member))) time)
        (trans
          (cong₂ _+_
            (headTangentExact time alpha (itemOutput alpha R396.here) rest
              (λ beta member → itemOutput beta (R396.there member)) headPositive)
            (go rest
              (λ beta member → itemOutput beta (R396.there member)) tailPositive))
          (symEq (sumTangentAppend
            (Local.headR290Pairs alpha rest headPositive)
            (Local.allR290Pairs rest tailPositive))))
      where
      symEq : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
      symEq refl = refl

roundB7FixedOutputOffDiagonalPairFamilyEnumerated : Bool
roundB7FixedOutputOffDiagonalPairFamilyEnumerated = true

roundB7FixedOutputFluxSumExact : Bool
roundB7FixedOutputFluxSumExact = true

roundB7FixedOutputTangentSumExact : Bool
roundB7FixedOutputTangentSumExact = true

roundB7FixedOutputFamilyIntroducesEstimate : Bool
roundB7FixedOutputFamilyIntroducesEstimate = false
