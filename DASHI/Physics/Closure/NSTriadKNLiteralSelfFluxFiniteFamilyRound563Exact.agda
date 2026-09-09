module DASHI.Physics.Closure.NSTriadKNLiteralSelfFluxFiniteFamilyRound563Exact where

------------------------------------------------------------------------
-- ROUND563 / LITERAL FIXED-OUTPUT SELF-PAIR FAMILY -> R559
--
-- R562 constructs one actual self-pair derivative item.  The physical output
-- fibre is a finite, time-independent incidence list, so recurse over that exact
-- list.  The resulting R422 flux/tangent sums are definitionally the R290
-- weighted self-flux and the R549 self-flux-tangent sums on every live slice.
--
-- Positivity proof terms may be constructed through two paths (R561 per item,
-- R550 recursively), but R290 weightedGramFlux / weightedGramFluxTangent do not
-- inspect the resolvent-law proof field.  Hence no proof-irrelevance axiom is
-- needed for the scalar same-object weld.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (cong₂)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact as R396
import DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact as R290
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNR418FinitePairFamilyToR409Round422Exact as R422
import DASHI.Physics.Closure.NSTriadKNLiteralR406DiagonalR290FluxDecompositionRound549Exact as R549
import DASHI.Physics.Closure.NSTriadKNLiteralR406DiagonalSelfGramEnergyControlRound550Exact as R550
import DASHI.Physics.Closure.NSTriadKNSelfFluxFiniteDerivativeReuseRound559Exact as R559
import DASHI.Physics.Closure.NSTriadKNSelfPairFixedResolventTrajectoryRound561Exact as R561
import DASHI.Physics.Closure.NSTriadKNLiteralSelfPairDerivativeItemRound562Exact as R562

F : C3.RealField _
F = Rational.rationalRealField

occursToCube563 :
  ∀ {tau items} → tau R396.OccursIn items → tau Cube.∈ items
occursToCube563 R396.here = Cube.here refl
occursToCube563 (R396.there member) = Cube.there (occursToCube563 member)

outputExact563 :
  (cutoff : Nat) (output : Z3.FourierMode) →
  (tau : Physical.PhysicalTriadIncidence) →
  tau R396.OccursIn Output.physicalOutputFiber cutoff output →
  Physical.k tau ≡ output
outputExact563 cutoff output tau member =
  Output.physicalOutputFiberSound (occursToCube563 member)

module SelfFluxAt
    (physicalSystem :
      DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  module D = R549.Diagonal physicalSystem S

  selfFluxSum563 :
    (items : List Physical.PhysicalTriadIncidence) →
    D.SelfRatePositiveOn549 items → ℚ
  selfFluxSum563 [] D.selfPositiveNil549 = 0ℚ
  selfFluxSum563 (tau ∷ rest) (D.selfPositiveCons549 positive tailPositive) =
    R290.weightedGramFlux (D.selfPair tau positive)
      + selfFluxSum563 rest tailPositive

  selfFluxTangentSum563 :
    (items : List Physical.PhysicalTriadIncidence) →
    D.SelfRatePositiveOn549 items → ℚ
  selfFluxTangentSum563 = D.selfFluxTangentSum549

module LiteralFixedOutputSelfFlux
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf : (Time → ℚ) → (Time → ℚ) → Set)
    (projectedCross : R426.ProjectedCrossDerivativeCalculus Time DerivativeOf)
    (vectorAlgebra : R425.VectorDerivativeAlgebra Time DerivativeOf)
    (hermitianCalculus : R417.HermitianDerivativeCalculus
      Time DerivativeOf ScalarDerivativeOf)
    (scalarScaleCalculus : R416.ScalarConstantDerivativeCalculus
      Time ScalarDerivativeOf)
    (scalarDerivativeAlgebra : R412.ScalarDerivativeAlgebra
      Time ScalarDerivativeOf) where

  module Live = R408.LiteralDynamics
    Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Fixed = R561.FixedSelfPair
    Time initialTime integrateTo DerivativeOf
  module Item = R562.LiteralSelfPairItem
    Time initialTime integrateTo DerivativeOf projectedCross vectorAlgebra
  module Finite = R559.SelfFluxFinite
    Time DerivativeOf ScalarDerivativeOf
    hermitianCalculus scalarScaleCalculus scalarDerivativeAlgebra

  buildPairCurves563 :
    (D : Live.LiteralRHSTrajectoryData) →
    (R : Support.LiteralNonzeroCutoffTrajectory (Fixed.trajectory D)) →
    (S : Helical.HelicalModeScalars F) →
    (cutoff : Nat) →
    (output : Z3.FourierMode) →
    (outputNonzero : Z3.NonZeroMode output) →
    (items : List Physical.PhysicalTriadIncidence) →
    ((tau : Physical.PhysicalTriadIncidence) →
      tau R396.OccursIn items → Physical.k tau ≡ output) →
    List (R422.PairCurveDerivativeData Time DerivativeOf)
  buildPairCurves563 D R S cutoff output outputNonzero [] allOutput = []
  buildPairCurves563 D R S cutoff output outputNonzero (tau ∷ rest) allOutput =
    Item.literalSelfPairDerivativeItem562
      D R S cutoff output outputNonzero tau (allOutput tau R396.here)
    ∷ buildPairCurves563
        D R S cutoff output outputNonzero rest
        (λ selected member → allOutput selected (R396.there member))

  items563 : Nat → Z3.FourierMode → List Physical.PhysicalTriadIncidence
  items563 cutoff output = Output.physicalOutputFiber cutoff output

  pairCurves563 :
    (D : Live.LiteralRHSTrajectoryData) →
    (R : Support.LiteralNonzeroCutoffTrajectory (Fixed.trajectory D)) →
    (S : Helical.HelicalModeScalars F) →
    (cutoff : Nat) →
    (output : Z3.FourierMode) →
    (outputNonzero : Z3.NonZeroMode output) →
    List (R422.PairCurveDerivativeData Time DerivativeOf)
  pairCurves563 D R S cutoff output outputNonzero =
    buildPairCurves563
      D R S cutoff output outputNonzero (items563 cutoff output)
      (outputExact563 cutoff output)

  selfPositiveAt563 :
    (D : Live.LiteralRHSTrajectoryData) →
    (R : Support.LiteralNonzeroCutoffTrajectory (Fixed.trajectory D)) →
    (S : Helical.HelicalModeScalars F) →
    (cutoff : Nat) →
    (output : Z3.FourierMode) →
    (outputNonzero : Z3.NonZeroMode output) →
    (time : Time) →
    let
      PS = Fixed.physicalSystemAt D cutoff time
      module SG = R550.SelfGram
        PS S (Fixed.currentViscosityPositive561 D R cutoff time)
    in
    SG.D.SelfRatePositiveOn549 (items563 cutoff output)
  selfPositiveAt563 D R S cutoff output outputNonzero time =
    let
      PS = Fixed.physicalSystemAt D cutoff time
      module SG = R550.SelfGram
        PS S (Fixed.currentViscosityPositive561 D R cutoff time)
    in
    SG.physicalOutputSelfRatePositive550 cutoff output outputNonzero

  literalSelfFlux563 :
    (D : Live.LiteralRHSTrajectoryData) →
    (R : Support.LiteralNonzeroCutoffTrajectory (Fixed.trajectory D)) →
    (S : Helical.HelicalModeScalars F) →
    (cutoff : Nat) →
    (output : Z3.FourierMode) →
    (outputNonzero : Z3.NonZeroMode output) →
    Time → ℚ
  literalSelfFlux563 D R S cutoff output outputNonzero time =
    let
      PS = Fixed.physicalSystemAt D cutoff time
      module Sum = SelfFluxAt PS S
    in
    Sum.selfFluxSum563
      (items563 cutoff output)
      (selfPositiveAt563 D R S cutoff output outputNonzero time)

  literalSelfFluxTangent563 :
    (D : Live.LiteralRHSTrajectoryData) →
    (R : Support.LiteralNonzeroCutoffTrajectory (Fixed.trajectory D)) →
    (S : Helical.HelicalModeScalars F) →
    (cutoff : Nat) →
    (output : Z3.FourierMode) →
    (outputNonzero : Z3.NonZeroMode output) →
    Time → ℚ
  literalSelfFluxTangent563 D R S cutoff output outputNonzero time =
    let
      PS = Fixed.physicalSystemAt D cutoff time
      module Sum = SelfFluxAt PS S
    in
    Sum.selfFluxTangentSum563
      (items563 cutoff output)
      (selfPositiveAt563 D R S cutoff output outputNonzero time)

  buildFluxSumsExact563 :
    (D : Live.LiteralRHSTrajectoryData) →
    (R : Support.LiteralNonzeroCutoffTrajectory (Fixed.trajectory D)) →
    (S : Helical.HelicalModeScalars F) →
    (cutoff : Nat) →
    (output : Z3.FourierMode) →
    (outputNonzero : Z3.NonZeroMode output) →
    (items : List Physical.PhysicalTriadIncidence) →
    (allOutput :
      (tau : Physical.PhysicalTriadIncidence) →
      tau R396.OccursIn items → Physical.k tau ≡ output) →
    (time : Time) →
    let
      curves = buildPairCurves563
        D R S cutoff output outputNonzero items allOutput
      PS = Fixed.physicalSystemAt D cutoff time
      module SG = R550.SelfGram
        PS S (Fixed.currentViscosityPositive561 D R cutoff time)
      positive = SG.buildSelfRatePositiveOn550
        output outputNonzero items allOutput
      module Sum = SelfFluxAt PS S
    in
    R412.sumCurves (R422.fluxTerms curves) time
      ≡ Sum.selfFluxSum563 items positive
  buildFluxSumsExact563 D R S cutoff output outputNonzero [] allOutput time = refl
  buildFluxSumsExact563
      D R S cutoff output outputNonzero (tau ∷ rest) allOutput time =
    cong₂ _+_ refl
      (buildFluxSumsExact563
        D R S cutoff output outputNonzero rest
        (λ selected member → allOutput selected (R396.there member)) time)

  buildTangentSumsExact563 :
    (D : Live.LiteralRHSTrajectoryData) →
    (R : Support.LiteralNonzeroCutoffTrajectory (Fixed.trajectory D)) →
    (S : Helical.HelicalModeScalars F) →
    (cutoff : Nat) →
    (output : Z3.FourierMode) →
    (outputNonzero : Z3.NonZeroMode output) →
    (items : List Physical.PhysicalTriadIncidence) →
    (allOutput :
      (tau : Physical.PhysicalTriadIncidence) →
      tau R396.OccursIn items → Physical.k tau ≡ output) →
    (time : Time) →
    let
      curves = buildPairCurves563
        D R S cutoff output outputNonzero items allOutput
      PS = Fixed.physicalSystemAt D cutoff time
      module SG = R550.SelfGram
        PS S (Fixed.currentViscosityPositive561 D R cutoff time)
      positive = SG.buildSelfRatePositiveOn550
        output outputNonzero items allOutput
      module Sum = SelfFluxAt PS S
    in
    R412.sumCurves (R422.tangentTerms curves) time
      ≡ Sum.selfFluxTangentSum563 items positive
  buildTangentSumsExact563 D R S cutoff output outputNonzero [] allOutput time = refl
  buildTangentSumsExact563
      D R S cutoff output outputNonzero (tau ∷ rest) allOutput time =
    cong₂ _+_ refl
      (buildTangentSumsExact563
        D R S cutoff output outputNonzero rest
        (λ selected member → allOutput selected (R396.there member)) time)

  literalSelfFluxFamily563 :
    (D : Live.LiteralRHSTrajectoryData) →
    (R : Support.LiteralNonzeroCutoffTrajectory (Fixed.trajectory D)) →
    (S : Helical.HelicalModeScalars F) →
    (cutoff : Nat) →
    (output : Z3.FourierMode) →
    (outputNonzero : Z3.NonZeroMode output) →
    Finite.LiteralSelfFluxPairFamily559
  literalSelfFluxFamily563 D R S cutoff output outputNonzero = record
    { Finite.pairCurves559 = pairCurves563 D R S cutoff output outputNonzero
    ; Finite.selfFlux559 = literalSelfFlux563 D R S cutoff output outputNonzero
    ; Finite.selfFluxTangent559 =
        literalSelfFluxTangent563 D R S cutoff output outputNonzero
    ; Finite.fluxSumIsLiteralSelfFlux559 =
        buildFluxSumsExact563
          D R S cutoff output outputNonzero
          (items563 cutoff output) (outputExact563 cutoff output)
    ; Finite.tangentSumIsLiteralSelfFluxTangent559 =
        buildTangentSumsExact563
          D R S cutoff output outputNonzero
          (items563 cutoff output) (outputExact563 cutoff output)
    }

  literalSelfFluxDerivative563 :
    (D : Live.LiteralRHSTrajectoryData) →
    (R : Support.LiteralNonzeroCutoffTrajectory (Fixed.trajectory D)) →
    (S : Helical.HelicalModeScalars F) →
    (cutoff : Nat) →
    (output : Z3.FourierMode) →
    (outputNonzero : Z3.NonZeroMode output) →
    ScalarDerivativeOf
      (literalSelfFlux563 D R S cutoff output outputNonzero)
      (literalSelfFluxTangent563 D R S cutoff output outputNonzero)
  literalSelfFluxDerivative563 D R S cutoff output outputNonzero =
    Finite.literalSelfFluxFamilyBuildsDerivative559
      (literalSelfFluxFamily563 D R S cutoff output outputNonzero)

round563LiteralPhysicalOutputSelfPairFamilyConstructed : Bool
round563LiteralPhysicalOutputSelfPairFamilyConstructed = true

round563FluxSumSameObjectWeldClosed : Bool
round563FluxSumSameObjectWeldClosed = true

round563TangentSumSameObjectWeldClosed : Bool
round563TangentSumSameObjectWeldClosed = true

round563LiteralSelfFluxDerivativeConstructed : Bool
round563LiteralSelfFluxDerivativeConstructed = true

round563FunctionExtensionalityUsed : Bool
round563FunctionExtensionalityUsed = false

round563R393FTCInhabitantConstructed : Bool
round563R393FTCInhabitantConstructed = false

round563ClayPromotion : Bool
round563ClayPromotion = false

round563LiteralSelfFluxDerivativeConstructedIsTrue :
  round563LiteralSelfFluxDerivativeConstructed ≡ true
round563LiteralSelfFluxDerivativeConstructedIsTrue = refl

round563R393FTCInhabitantConstructedIsFalse :
  round563R393FTCInhabitantConstructed ≡ false
round563R393FTCInhabitantConstructedIsFalse = refl

round563ClayPromotionIsFalse : round563ClayPromotion ≡ false
round563ClayPromotionIsFalse = refl
