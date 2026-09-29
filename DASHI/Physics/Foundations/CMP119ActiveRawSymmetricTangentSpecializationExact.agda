{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119ActiveRawSymmetricTangentSpecializationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteBeta
import DASHI.Physics.YangMills.Balaban1989FiniteModeInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw
import DASHI.Physics.YangMills.BalabanCMP119RawStateFromFiniteBetaHistoryExact as RawHistory
import DASHI.Physics.YangMills.BalabanCMP119RawActiveRegularEDecoderRound248Exact as R248
import DASHI.Physics.YangMills.BalabanTheorem1RegularEContinuationRound247Exact as R247
import DASHI.Physics.YangMills.BalabanCMP119ActiveRawToBC1Round250Exact as R250
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP109Equation51LocalizedHessianRound103Exact as Eq51
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as Canon
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier

record SymmetricActiveRawCMP119BC1Inputs
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {Mode Atom : Set}
    {betaData : FiniteBeta.FiniteModeBetaTrajectoryData trajectory Mode Atom}
    {history : History.FiniteModeInverseSquareTerminalHistoryData
      trajectory Mode Atom betaData}
    {Density Background Fluctuation
      Action WilsonTerm RTerm BoundaryTerm Vacuum : Set}
    (objects : RawHistory.CMP119RawObjectsOverHistory history
      Density Background Fluctuation
      Action WilsonTerm (Background → ℝ) RTerm BoundaryTerm Vacuum)
    (predicates : Raw.CMP119Section2PredicateFamily
      (RawHistory.rawStateFromFiniteBetaHistory objects))
    (decoder : R248.RawELocalizedAnalyticDecoder objects predicates)
    (rawWitness : Raw.ActiveCMP119Section2Witness
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
      {betaData = betaData} {history = history}
      {source = RawHistory.rawStateFromFiniteBetaHistory objects}
      predicates) : Set₂ where
  field
    calculus :
      Finite.SecondVariationLinearity
        Background K.SymmetricTensorComponent4

    equation51 :
      Eq51.CMP109Equation51OnContinuation
        (R250.activeContinuation
          decoder rawWitness K.SymmetricTensorComponent4)
        calculus

    index : R247.ActiveScaleIndex history
    volume : R248.Volume decoder
    analyticDemands : Canon.CMP116FiniteNormalizedAnalyticDemands

open SymmetricActiveRawCMP119BC1Inputs public

asActiveRawCMP119BC1Inputs :
  ∀ {trajectory Mode Atom betaData history
      Density Background Fluctuation Action WilsonTerm RTerm BoundaryTerm Vacuum
      objects predicates decoder rawWitness} →
  SymmetricActiveRawCMP119BC1Inputs
    {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
    {betaData = betaData} {history = history}
    {Density = Density} {Background = Background}
    {Fluctuation = Fluctuation} {Action = Action}
    {WilsonTerm = WilsonTerm} {RTerm = RTerm}
    {BoundaryTerm = BoundaryTerm} {Vacuum = Vacuum}
    objects predicates decoder rawWitness →
  R250.ActiveRawCMP119BC1Inputs objects predicates decoder rawWitness
asActiveRawCMP119BC1Inputs inputs = record
  { R250.ActiveRawCMP119BC1Inputs.Tangent =
      K.SymmetricTensorComponent4
  ; R250.ActiveRawCMP119BC1Inputs.calculus =
      calculus inputs
  ; R250.ActiveRawCMP119BC1Inputs.equation51 =
      equation51 inputs
  ; R250.ActiveRawCMP119BC1Inputs.index =
      index inputs
  ; R250.ActiveRawCMP119BC1Inputs.volume =
      volume inputs
  ; R250.ActiveRawCMP119BC1Inputs.analyticDemands =
      analyticDemands inputs
  }

activeRawTangentIsSymmetricTenSlot :
  ∀ {trajectory Mode Atom betaData history
      Density Background Fluctuation Action WilsonTerm RTerm BoundaryTerm Vacuum
      objects predicates decoder rawWitness}
    (inputs : SymmetricActiveRawCMP119BC1Inputs
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
      {betaData = betaData} {history = history}
      {Density = Density} {Background = Background}
      {Fluctuation = Fluctuation} {Action = Action}
      {WilsonTerm = WilsonTerm} {RTerm = RTerm}
      {BoundaryTerm = BoundaryTerm} {Vacuum = Vacuum}
      objects predicates decoder rawWitness) →
  R250.Tangent (asActiveRawCMP119BC1Inputs inputs)
  ≡ K.SymmetricTensorComponent4
activeRawTangentIsSymmetricTenSlot inputs = refl

finiteActionTangentIsSymmetricTenSlot :
  ∀ {trajectory Mode Atom betaData history
      Density Background Fluctuation Action WilsonTerm RTerm BoundaryTerm Vacuum
      objects predicates decoder rawWitness}
    (inputs : SymmetricActiveRawCMP119BC1Inputs
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
      {betaData = betaData} {history = history}
      {Density = Density} {Background = Background}
      {Fluctuation = Fluctuation} {Action = Action}
      {WilsonTerm = WilsonTerm} {RTerm = RTerm}
      {BoundaryTerm = BoundaryTerm} {Vacuum = Vacuum}
      objects predicates decoder rawWitness) →
  Finite.Tangent
    (Carrier.finiteAction
      (R250.activeRawBC1Carrier
        (asActiveRawCMP119BC1Inputs inputs)))
  ≡ K.SymmetricTensorComponent4
finiteActionTangentIsSymmetricTenSlot inputs = refl

symmetricSlotAsFiniteTangent :
  ∀ {trajectory Mode Atom betaData history
      Density Background Fluctuation Action WilsonTerm RTerm BoundaryTerm Vacuum
      objects predicates decoder rawWitness}
    (inputs : SymmetricActiveRawCMP119BC1Inputs
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
      {betaData = betaData} {history = history}
      {Density = Density} {Background = Background}
      {Fluctuation = Fluctuation} {Action = Action}
      {WilsonTerm = WilsonTerm} {RTerm = RTerm}
      {BoundaryTerm = BoundaryTerm} {Vacuum = Vacuum}
      objects predicates decoder rawWitness) →
  K.SymmetricTensorComponent4 →
  Finite.Tangent
    (Carrier.finiteAction
      (R250.activeRawBC1Carrier
        (asActiveRawCMP119BC1Inputs inputs)))
symmetricSlotAsFiniteTangent inputs component = component

tenSlotToFiniteTangentMapIsDefinitional : Bool
tenSlotToFiniteTangentMapIsDefinitional = true

tenSlotToFiniteTangentMapIsDefinitionalIsTrue :
  tenSlotToFiniteTangentMapIsDefinitional ≡ true
tenSlotToFiniteTangentMapIsDefinitionalIsTrue = refl

tenArbitraryFiniteTangentChoicesStillRequired : Bool
tenArbitraryFiniteTangentChoicesStillRequired = false

tenArbitraryFiniteTangentChoicesStillRequiredIsFalse :
  tenArbitraryFiniteTangentChoicesStillRequired ≡ false
tenArbitraryFiniteTangentChoicesStillRequiredIsFalse = refl
