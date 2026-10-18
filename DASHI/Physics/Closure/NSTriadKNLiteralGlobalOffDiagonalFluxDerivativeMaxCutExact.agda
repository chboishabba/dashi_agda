module DASHI.Physics.Closure.NSTriadKNLiteralGlobalOffDiagonalFluxDerivativeMaxCutExact where

------------------------------------------------------------------------
-- POSITIVE B7 Q4+E / GLOBAL LITERAL OFF-DIAGONAL FLUX DERIVATIVE
--
-- Recurses over the SAME canonical nonzero output list used by R406.  At each
-- output it reuses the fixed-output R396 derivative family and concatenates the
-- exact unordered pair lists.  Hence the final R422 family is definitionally
-- attached to R406's global offDiagonalFlux/offDiagonalFluxTangent carrier.
-- No estimate, cardinality factor, or alternate flux is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (_++_)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNLiteralNonzeroCutoffSupportRound404Exact as R404
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNFixedOutputLiveGlobalFluxRound406Exact as R406
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNR418FinitePairFamilyToR409Round422Exact as R422
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNFiniteWeightedGramFluxAggregationRound385Exact as R385
import DASHI.Physics.Closure.NSTriadKNLiteralOffDiagonalFluxFixedOutputFamilyMaxCutExact as Fibre

F : C3.RealField _
F = Rational.rationalRealField

module GlobalOffDiagonalDerivative
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf : (Time → ℚ) → (Time → ℚ) → Set)
    (projectedCross : R426.ProjectedCrossDerivativeCalculus Time VectorDerivativeOf)
    (vectorAlgebra : R425.VectorDerivativeAlgebra Time VectorDerivativeOf)
    (hermitianCalculus :
      R417.HermitianDerivativeCalculus
        Time VectorDerivativeOf ScalarDerivativeOf)
    (constantCalculus :
      R416.ScalarConstantDerivativeCalculus Time ScalarDerivativeOf)
    (scalarAlgebra :
      R412.ScalarDerivativeAlgebra Time ScalarDerivativeOf)
    (D : R408.LiteralDynamics.LiteralRHSTrajectoryData
      Time initialTime integrateTo VectorDerivativeOf)
    (R : R405.LiteralCutoffSupport.LiteralNonzeroCutoffTrajectory
      Time initialTime integrateTo VectorDerivativeOf
      (R408.LiteralDynamics.literalPhysicalTrajectory
        Time initialTime integrateTo VectorDerivativeOf D))
    (cutoff : Nat) where

  module Literal = R408.LiteralDynamics
    Time initialTime integrateTo VectorDerivativeOf
  module Flux = R406.FixedLiveFlux
    Time initialTime integrateTo VectorDerivativeOf
  module Finite = R422.FiniteFamily
    Time initialTime integrateTo VectorDerivativeOf ScalarDerivativeOf
    hermitianCalculus constantCalculus scalarAlgebra

  T = Literal.literalPhysicalTrajectory D

  outputs : List Z3.FourierMode
  outputs = Canonical.nonzeroCutoffModes cutoff

  buildOutputData :
    (selected : List Z3.FourierMode) →
    ((mode : Z3.FourierMode) →
      mode Cube.∈ selected → mode Cube.∈ outputs) →
    List (R422.PairCurveDerivativeData Time VectorDerivativeOf)
  buildOutputData [] included = []
  buildOutputData (output ∷ rest) included =
    let
      nonzero = R404.nonzeroCutoffMemberNonzero
        (included output (Cube.here refl))
      module One = Fibre.FixedOutputFamily
        Time initialTime integrateTo VectorDerivativeOf
        projectedCross vectorAlgebra D R cutoff output nonzero
    in
    One.pairCurves ++
      buildOutputData rest
        (λ mode member → included mode (Cube.there member))

  pairCurves : List (R422.PairCurveDerivativeData Time VectorDerivativeOf)
  pairCurves = buildOutputData outputs (λ mode member → member)

  sumCurvesAppend :
    (terms more : List (Time → ℚ)) →
    (time : Time) →
    R412.sumCurves (terms ++ more) time
    ≡ R412.sumCurves terms time + R412.sumCurves more time
  sumCurvesAppend [] more time = refl
  sumCurvesAppend (term ∷ terms) more time
    rewrite sumCurvesAppend terms more time = refl

  fluxTermsAppend :
    (left right : List (R422.PairCurveDerivativeData Time VectorDerivativeOf)) →
    R422.fluxTerms (left ++ right)
    ≡ R422.fluxTerms left ++ R422.fluxTerms right
  fluxTermsAppend [] right = refl
  fluxTermsAppend (x ∷ xs) right
    rewrite fluxTermsAppend xs right = refl

  tangentTermsAppend :
    (left right : List (R422.PairCurveDerivativeData Time VectorDerivativeOf)) →
    R422.tangentTerms (left ++ right)
    ≡ R422.tangentTerms left ++ R422.tangentTerms right
  tangentTermsAppend [] right = refl
  tangentTermsAppend (x ∷ xs) right
    rewrite tangentTermsAppend xs right = refl

  sumFluxAppend :
    (left right : List _) →
    R385.sumWeightedFlux (left ++ right)
    ≡ R385.sumWeightedFlux left + R385.sumWeightedFlux right
  sumFluxAppend [] right = refl
  sumFluxAppend (x ∷ xs) right
    rewrite sumFluxAppend xs right = refl

  sumTangentAppend :
    (left right : List _) →
    R385.sumWeightedFluxTangent (left ++ right)
    ≡ R385.sumWeightedFluxTangent left
      + R385.sumWeightedFluxTangent right
  sumTangentAppend [] right = refl
  sumTangentAppend (x ∷ xs) right
    rewrite sumTangentAppend xs right = refl

  fluxSumExactSelected :
    (selected : List Z3.FourierMode) →
    (included :
      (mode : Z3.FourierMode) →
      mode Cube.∈ selected → mode Cube.∈ outputs) →
    (time : Time) →
    let module At = Flux.At T R cutoff time in
    R412.sumCurves
      (R422.fluxTerms (buildOutputData selected included)) time
    ≡ R385.sumWeightedFlux
        (At.Global.globalPairs cutoff selected
          (At.buildCanonicalOutputPositivity selected included))
  fluxSumExactSelected [] included time = refl
  fluxSumExactSelected (output ∷ rest) included time =
    let
      nonzero = R404.nonzeroCutoffMemberNonzero
        (included output (Cube.here refl))
      module One = Fibre.FixedOutputFamily
        Time initialTime integrateTo VectorDerivativeOf
        projectedCross vectorAlgebra D R cutoff output nonzero
      tailIncluded = λ mode member → included mode (Cube.there member)
      module At = Flux.At T R cutoff time
      headPos =
        At.Rate.physicalOutputFibrePairRatesPositive cutoff output nonzero
      tailPos = At.buildCanonicalOutputPositivity rest tailIncluded
    in
    trans
      (congPoint
        (fluxTermsAppend One.pairCurves
          (buildOutputData rest tailIncluded)) time)
      (trans
        (sumCurvesAppend
          (R422.fluxTerms One.pairCurves)
          (R422.fluxTerms (buildOutputData rest tailIncluded)) time)
        (trans
          (cong₂ _+_
            (One.allFluxExact time)
            (fluxSumExactSelected rest tailIncluded time))
          (symEq (sumFluxAppend
            (At.Global.O.outputPairs cutoff output headPos)
            (At.Global.globalPairs cutoff rest tailPos)))))
    where
    congPoint : ∀ {xs ys : List (Time → ℚ)} →
      xs ≡ ys → (time : Time) →
      R412.sumCurves xs time ≡ R412.sumCurves ys time
    congPoint refl time = refl

    symEq : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
    symEq refl = refl

  tangentSumExactSelected :
    (selected : List Z3.FourierMode) →
    (included :
      (mode : Z3.FourierMode) →
      mode Cube.∈ selected → mode Cube.∈ outputs) →
    (time : Time) →
    let module At = Flux.At T R cutoff time in
    R412.sumCurves
      (R422.tangentTerms (buildOutputData selected included)) time
    ≡ R385.sumWeightedFluxTangent
        (At.Global.globalPairs cutoff selected
          (At.buildCanonicalOutputPositivity selected included))
  tangentSumExactSelected [] included time = refl
  tangentSumExactSelected (output ∷ rest) included time =
    let
      nonzero = R404.nonzeroCutoffMemberNonzero
        (included output (Cube.here refl))
      module One = Fibre.FixedOutputFamily
        Time initialTime integrateTo VectorDerivativeOf
        projectedCross vectorAlgebra D R cutoff output nonzero
      tailIncluded = λ mode member → included mode (Cube.there member)
      module At = Flux.At T R cutoff time
      headPos =
        At.Rate.physicalOutputFibrePairRatesPositive cutoff output nonzero
      tailPos = At.buildCanonicalOutputPositivity rest tailIncluded
    in
    trans
      (congPoint
        (tangentTermsAppend One.pairCurves
          (buildOutputData rest tailIncluded)) time)
      (trans
        (sumCurvesAppend
          (R422.tangentTerms One.pairCurves)
          (R422.tangentTerms (buildOutputData rest tailIncluded)) time)
        (trans
          (cong₂ _+_
            (One.allTangentExact time)
            (tangentSumExactSelected rest tailIncluded time))
          (symEq (sumTangentAppend
            (At.Global.O.outputPairs cutoff output headPos)
            (At.Global.globalPairs cutoff rest tailPos)))))
    where
    congPoint : ∀ {xs ys : List (Time → ℚ)} →
      xs ≡ ys → (time : Time) →
      R412.sumCurves xs time ≡ R412.sumCurves ys time
    congPoint refl time = refl

    symEq : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
    symEq refl = refl

  fluxSumIsR406 :
    (time : Time) →
    R412.sumCurves (R422.fluxTerms pairCurves) time
    ≡ Flux.At.offDiagonalFlux T R cutoff time
  fluxSumIsR406 =
    fluxSumExactSelected outputs (λ mode member → member)

  tangentSumIsR406 :
    (time : Time) →
    R412.sumCurves (R422.tangentTerms pairCurves) time
    ≡ Flux.At.offDiagonalFluxTangent T R cutoff time
  tangentSumIsR406 =
    tangentSumExactSelected outputs (λ mode member → member)

  literalR406PairFamily : Finite.LiteralR406PairFamily T R cutoff
  literalR406PairFamily = record
    { Finite.pairCurves = pairCurves
    ; Finite.fluxSumIsR406 = fluxSumIsR406
    ; Finite.tangentSumIsR406 = tangentSumIsR406
    }

  exactR406FluxDerivative :
    Finite.Boundary.FixedOutputFluxDerivative T R cutoff
  exactR406FluxDerivative =
    Finite.literalPairFamilyBuildsR409 T R cutoff literalR406PairFamily

roundB7GlobalOffDiagonalPairFamilyEnumerated : Bool
roundB7GlobalOffDiagonalPairFamilyEnumerated = true

roundB7GlobalFluxDerivativeClosedGivenStandardCalculus : Bool
roundB7GlobalFluxDerivativeClosedGivenStandardCalculus = true

roundB7GlobalOffDiagonalDerivativeIntroducesEstimate : Bool
roundB7GlobalOffDiagonalDerivativeIntroducesEstimate = false

roundB7GlobalFluxDerivativeClosedGivenStandardCalculusIsTrue :
  roundB7GlobalFluxDerivativeClosedGivenStandardCalculus ≡ true
roundB7GlobalFluxDerivativeClosedGivenStandardCalculusIsTrue = refl
