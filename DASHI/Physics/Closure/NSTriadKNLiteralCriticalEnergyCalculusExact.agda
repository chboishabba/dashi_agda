module DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact where

------------------------------------------------------------------------
-- STRICT B-PHASE S1b / LITERAL CRITICAL-ENERGY CALCULUS COMPILER
--
-- Inputs already owned elsewhere:
--   R408  literal same-object velocity derivative;
--   R417  real-Hermitian product rule;
--   R416  constant-scalar derivative closure;
--   R412  finite-sum derivative algebra;
--   R564  scalar endpoint FTC schema;
--   ModeCarrier  time-independent canonical cutoff mode list without S4.
--
-- This owner composes those ingredients for the exact S0 critical observable.
-- The only new authority surface is ordinary integration linearity for the
-- caller's module-parameter `integrateTo`: congruence, additivity, and constant
-- scaling.  No Navier--Stokes estimate or positivity assumption is introduced.
--
-- The resulting theorem is conditional on the scalar derivative/FTC/integration
-- authorities.  R564 already records that no concrete scalar FTC inhabitant is
-- installed, so unconditional S1 remains fail-closed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _-_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as R30
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffModeCarrierExact as ModeCarrier
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as Fold
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyPointwiseExact as Pointwise

F : C3.RealField _
F = Rational.rationalRealField

half : ℚ
half = + 1 / 2

------------------------------------------------------------------------
-- Ordinary integration linearity, kept explicit because integrateTo is an
-- externally supplied module parameter rather than a definition in this lane.
------------------------------------------------------------------------

record ScalarIntegrationLinearity
    (Time : Set)
    (integrateTo : (Time → ℚ) → Time → ℚ) : Set₁ where
  field
    integrationCongruent :
      ∀ {f g} →
      ((time : Time) → f time ≡ g time) →
      (terminal : Time) →
      integrateTo f terminal ≡ integrateTo g terminal

    integrationAdditive :
      (f g : Time → ℚ) →
      (terminal : Time) →
      integrateTo (λ time → f time + g time) terminal
      ≡ integrateTo f terminal + integrateTo g terminal

    integrationConstantScale :
      (c : ℚ) →
      (f : Time → ℚ) →
      (terminal : Time) →
      integrateTo (λ time → c * f time) terminal
      ≡ c * integrateTo f terminal

open ScalarIntegrationLinearity public

------------------------------------------------------------------------
-- Coordinate identities linking R417's canonical Gram derivative convention to
-- the exact S0 norm/tangent convention.
------------------------------------------------------------------------

halfGramIsNorm :
  (u : C3.Complex3 F) →
  half * (R291.two * R179.realHermitianCross u u)
  ≡ L2.complex3NormSquared u
halfGramIsNorm
    (C3.complex3
      (C3.complex ux uxi) (C3.complex uy uyi) (C3.complex uz uzi)) =
  solve (ux ∷ uxi ∷ uy ∷ uyi ∷ uz ∷ uzi ∷ [])

halfGramTangentIsEnergyTangent :
  (du u : C3.Complex3 F) →
  half *
    (R291.two *
      (R179.realHermitianCross du u + R179.realHermitianCross u du))
  ≡ Fold.two * Fold.realHermitianPairing du u
halfGramTangentIsEnergyTangent
    (C3.complex3
      (C3.complex dx dxi) (C3.complex dy dyi) (C3.complex dz dzi))
    (C3.complex3
      (C3.complex ux uxi) (C3.complex uy uyi) (C3.complex uz uzi)) =
  solve
    ( dx ∷ dxi ∷ dy ∷ dyi ∷ dz ∷ dzi
    ∷ ux ∷ uxi ∷ uy ∷ uyi ∷ uz ∷ uzi ∷ [] )

------------------------------------------------------------------------
-- Conditional compiler.
------------------------------------------------------------------------

module LiteralCriticalEnergyCalculus
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf : (Time → ℚ) → (Time → ℚ) → Set)
    (hermitianCalculus :
      R417.HermitianDerivativeCalculus Time DerivativeOf ScalarDerivativeOf)
    (constantScaleCalculus :
      R416.ScalarConstantDerivativeCalculus Time ScalarDerivativeOf)
    (scalarDerivativeAlgebra :
      R412.ScalarDerivativeAlgebra Time ScalarDerivativeOf)
    (FTC :
      R564.ScalarFundamentalTheorem564
        Time initialTime integrateTo ScalarDerivativeOf)
    (integrationLinearity : ScalarIntegrationLinearity Time integrateTo) where

  module Live = R408.LiteralDynamics
    Time initialTime integrateTo DerivativeOf
  module Modes = ModeCarrier.LiteralModeCarrier
    Time initialTime integrateTo DerivativeOf
  module Obs = Fold.LiteralCriticalObservables
    Time initialTime integrateTo DerivativeOf

  uCurve :
    Live.LiteralRHSTrajectoryData →
    Nat → Z3.FourierMode → Time → C3.Complex3 F
  uCurve D cutoff mode time =
    Audit.velocityAt
      (Live.Base.systemAt
        (Live.stateTrajectory (Live.support D)) cutoff time)
      mode

  duCurve :
    Live.LiteralRHSTrajectoryData →
    Nat → Z3.FourierMode → Time → C3.Complex3 F
  duCurve D cutoff mode time =
    R30.literalViscousQuadraticCoefficient
      (Live.physicalSystemAt (Live.support D) cutoff time)
      mode

  modeEnergyCurve :
    Live.LiteralRHSTrajectoryData →
    Nat → Z3.FourierMode → Time → ℚ
  modeEnergyCurve D cutoff mode time =
    Fold.dyadicCriticalWeight mode
      * L2.complex3NormSquared (uCurve D cutoff mode time)

  modeEnergyTangentCurve :
    Live.LiteralRHSTrajectoryData →
    Nat → Z3.FourierMode → Time → ℚ
  modeEnergyTangentCurve D cutoff mode time =
    Pointwise.modeLiteralEnergyTangent
      (Live.physicalSystemAt (Live.support D) cutoff time)
      mode

  modeEnergyCurveMeaning :
    (D : Live.LiteralRHSTrajectoryData) →
    (cutoff : Nat) (mode : Z3.FourierMode) (time : Time) →
    Fold.dyadicCriticalWeight mode
      * (half *
          (R291.two *
            R179.realHermitianCross
              (uCurve D cutoff mode time)
              (uCurve D cutoff mode time)))
    ≡ modeEnergyCurve D cutoff mode time
  modeEnergyCurveMeaning D cutoff mode time =
    cong (Fold.dyadicCriticalWeight mode *_)
      (halfGramIsNorm (uCurve D cutoff mode time))

  modeEnergyTangentMeaning :
    (D : Live.LiteralRHSTrajectoryData) →
    (cutoff : Nat) (mode : Z3.FourierMode) (time : Time) →
    Fold.dyadicCriticalWeight mode
      * (half *
          (R291.two *
            ( R179.realHermitianCross
                (duCurve D cutoff mode time)
                (uCurve D cutoff mode time)
            + R179.realHermitianCross
                (uCurve D cutoff mode time)
                (duCurve D cutoff mode time))))
    ≡ modeEnergyTangentCurve D cutoff mode time
  modeEnergyTangentMeaning D cutoff mode time =
    cong (Fold.dyadicCriticalWeight mode *_)
      (halfGramTangentIsEnergyTangent
        (duCurve D cutoff mode time)
        (uCurve D cutoff mode time))

  literalModeCriticalEnergyDerivative :
    (D : Live.LiteralRHSTrajectoryData) →
    (cutoff : Nat) (mode : Z3.FourierMode) →
    ScalarDerivativeOf
      (modeEnergyCurve D cutoff mode)
      (modeEnergyTangentCurve D cutoff mode)
  literalModeCriticalEnergyDerivative D cutoff mode =
    R416.transportDerivative constantScaleCalculus
      (modeEnergyCurveMeaning D cutoff mode)
      (modeEnergyTangentMeaning D cutoff mode)
      (R416.constantScaleDerivative constantScaleCalculus
        (Fold.dyadicCriticalWeight mode)
        (R416.constantScaleDerivative constantScaleCalculus half
          (R417.realHermitianGramProductRule hermitianCalculus
            (Live.velocityDerivativeIsLiteralRHS D cutoff mode)
            (Live.velocityDerivativeIsLiteralRHS D cutoff mode))))

  energyCurves :
    Live.LiteralRHSTrajectoryData →
    Nat → List Z3.FourierMode → List (Time → ℚ)
  energyCurves D cutoff [] = []
  energyCurves D cutoff (mode ∷ rest) =
    modeEnergyCurve D cutoff mode ∷ energyCurves D cutoff rest

  tangentCurves :
    Live.LiteralRHSTrajectoryData →
    Nat → List Z3.FourierMode → List (Time → ℚ)
  tangentCurves D cutoff [] = []
  tangentCurves D cutoff (mode ∷ rest) =
    modeEnergyTangentCurve D cutoff mode ∷ tangentCurves D cutoff rest

  allModeEnergyDerivatives :
    (D : Live.LiteralRHSTrajectoryData) →
    (cutoff : Nat) →
    (modes : List Z3.FourierMode) →
    R412.AllDerivatives ScalarDerivativeOf
      (energyCurves D cutoff modes)
      (tangentCurves D cutoff modes)
  allModeEnergyDerivatives D cutoff [] = R412.derivativesNil
  allModeEnergyDerivatives D cutoff (mode ∷ rest) =
    R412.derivativesCons
      (literalModeCriticalEnergyDerivative D cutoff mode)
      (allModeEnergyDerivatives D cutoff rest)

  summedEnergyCurveMeaning :
    (D : Live.LiteralRHSTrajectoryData) →
    (cutoff : Nat) →
    (modes : List Z3.FourierMode) →
    (time : Time) →
    R412.sumCurves (energyCurves D cutoff modes) time
    ≡ Fold.weightedVelocityMass
        Fold.dyadicCriticalWeight
        (Live.Base.systemAt
          (Live.stateTrajectory (Live.support D)) cutoff time)
        modes
  summedEnergyCurveMeaning D cutoff [] time = refl
  summedEnergyCurveMeaning D cutoff (mode ∷ rest) time =
    cong
      (Fold.dyadicCriticalWeight mode
        * L2.complex3NormSquared (uCurve D cutoff mode time) +_)
      (summedEnergyCurveMeaning D cutoff rest time)

  summedTangentCurveMeaning :
    (D : Live.LiteralRHSTrajectoryData) →
    (cutoff : Nat) →
    (modes : List Z3.FourierMode) →
    (time : Time) →
    R412.sumCurves (tangentCurves D cutoff modes) time
    ≡ Pointwise.finiteLiteralEnergyTangent
        (Live.physicalSystemAt (Live.support D) cutoff time)
        modes
  summedTangentCurveMeaning D cutoff [] time = refl
  summedTangentCurveMeaning D cutoff (mode ∷ rest) time =
    cong
      (modeEnergyTangentCurve D cutoff mode time +_)
      (summedTangentCurveMeaning D cutoff rest time)

  fixedModeListEnergyDerivative :
    (D : Live.LiteralRHSTrajectoryData) →
    (cutoff : Nat) →
    ScalarDerivativeOf
      (λ time →
        Fold.weightedVelocityMass
          Fold.dyadicCriticalWeight
          (Live.Base.systemAt
            (Live.stateTrajectory (Live.support D)) cutoff time)
          (Canonical.nonzeroCutoffModes cutoff))
      (λ time →
        Pointwise.finiteLiteralEnergyTangent
          (Live.physicalSystemAt (Live.support D) cutoff time)
          (Canonical.nonzeroCutoffModes cutoff))
  fixedModeListEnergyDerivative D cutoff =
    R412.transportDerivative scalarDerivativeAlgebra
      (summedEnergyCurveMeaning D cutoff (Canonical.nonzeroCutoffModes cutoff))
      (summedTangentCurveMeaning D cutoff (Canonical.nonzeroCutoffModes cutoff))
      (R412.finiteSumDerivative scalarDerivativeAlgebra
        (allModeEnergyDerivatives D cutoff
          (Canonical.nonzeroCutoffModes cutoff)))

  liveCriticalEnergyDerivative :
    (D : Live.LiteralRHSTrajectoryData) →
    (C : Modes.LiteralCutoffModeCarrier (Live.literalPhysicalTrajectory D)) →
    (cutoff : Nat) →
    ScalarDerivativeOf
      (Obs.criticalEnergyAt (Live.literalPhysicalTrajectory D) cutoff)
      (λ time →
        Pointwise.finiteLiteralEnergyTangent
          (Live.physicalSystemAt (Live.support D) cutoff time)
          (Audit.modes
            (Live.Base.systemAt
              (Live.stateTrajectory (Live.support D)) cutoff time)))
  liveCriticalEnergyDerivative D C cutoff =
    R412.transportDerivative scalarDerivativeAlgebra
      (λ time → energyMeaning time)
      (λ time → tangentMeaning time)
      (fixedModeListEnergyDerivative D cutoff)
    where
    energyMeaning :
      (time : Time) →
      Fold.weightedVelocityMass
        Fold.dyadicCriticalWeight
        (Live.Base.systemAt
          (Live.stateTrajectory (Live.support D)) cutoff time)
        (Canonical.nonzeroCutoffModes cutoff)
      ≡ Obs.criticalEnergyAt (Live.literalPhysicalTrajectory D) cutoff time
    energyMeaning time
      rewrite Modes.retainedModesExact C cutoff time = refl

    tangentMeaning :
      (time : Time) →
      Pointwise.finiteLiteralEnergyTangent
        (Live.physicalSystemAt (Live.support D) cutoff time)
        (Canonical.nonzeroCutoffModes cutoff)
      ≡
      Pointwise.finiteLiteralEnergyTangent
        (Live.physicalSystemAt (Live.support D) cutoff time)
        (Audit.modes
          (Live.Base.systemAt
            (Live.stateTrajectory (Live.support D)) cutoff time))
    tangentMeaning time
      rewrite Modes.retainedModesExact C cutoff time = refl

  liveCriticalEnergyTangentSplit :
    (D : Live.LiteralRHSTrajectoryData) →
    (cutoff : Nat) →
    (time : Time) →
    let T = Live.literalPhysicalTrajectory D in
    let P = Live.physicalSystemAt (Live.support D) cutoff time in
    Pointwise.finiteLiteralEnergyTangent P (Audit.modes (R30.finiteSystem P))
    ≡ Obs.productionRateAt T cutoff time
        - (Fold.two * Live.physicalViscosity (Live.support D))
            * Obs.dissipationRateAt T cutoff time
  liveCriticalEnergyTangentSplit D cutoff time
    rewrite Live.viscosityFixed (Live.support D) cutoff time =
    Pointwise.literalLiveModeListCriticalEnergySplit
      (Live.physicalSystemAt (Live.support D) cutoff time)

  integrateScaledDifference :
    (production dissipation : Time → ℚ) →
    (coefficient : ℚ) →
    (terminal : Time) →
    integrateTo
      (λ time → production time - coefficient * dissipation time)
      terminal
    ≡ integrateTo production terminal
        - coefficient * integrateTo dissipation terminal
  integrateScaledDifference production dissipation coefficient terminal =
    let
      asAdditive :
        integrateTo
          (λ time → production time - coefficient * dissipation time)
          terminal
        ≡
        integrateTo
          (λ time → production time + (- coefficient) * dissipation time)
          terminal
      asAdditive = integrationCongruent integrationLinearity
        (λ time → solve (production time ∷ coefficient ∷ dissipation time ∷ []))
        terminal

      split = integrationAdditive integrationLinearity
        production
        (λ time → (- coefficient) * dissipation time)
        terminal

      scale = integrationConstantScale integrationLinearity
        (- coefficient) dissipation terminal
    in
    trans asAdditive
      (trans split
        (trans
          (cong (integrateTo production terminal +_) scale)
          (solve
            ( integrateTo production terminal
            ∷ coefficient
            ∷ integrateTo dissipation terminal
            ∷ [] ))))

  integratedLiteralCriticalEnergyIdentity :
    (D : Live.LiteralRHSTrajectoryData) →
    (C : Modes.LiteralCutoffModeCarrier (Live.literalPhysicalTrajectory D)) →
    (cutoff : Nat) →
    (terminal : Time) →
    let T = Live.literalPhysicalTrajectory D in
    Obs.criticalEnergyAt T cutoff terminal
      + (Fold.two * Live.physicalViscosity (Live.support D))
          * Obs.integratedCriticalDissipation T cutoff terminal
    ≡
    Obs.criticalEnergyAt T cutoff initialTime
      + Obs.integratedCriticalProduction T cutoff terminal
  integratedLiteralCriticalEnergyIdentity D C cutoff terminal =
    let
      T = Live.literalPhysicalTrajectory D
      coefficient = Fold.two * Live.physicalViscosity (Live.support D)
      tangent : Time → ℚ
      tangent time =
        Pointwise.finiteLiteralEnergyTangent
          (Live.physicalSystemAt (Live.support D) cutoff time)
          (Audit.modes
            (Live.Base.systemAt
              (Live.stateTrajectory (Live.support D)) cutoff time))

      tangentDerivative = liveCriticalEnergyDerivative D C cutoff

      endpointFTC :
        integrateTo tangent terminal
        ≡ Obs.criticalEnergyAt T cutoff terminal
            - Obs.criticalEnergyAt T cutoff initialTime
      endpointFTC = R564.scalarEndpointFTC564 FTC tangentDerivative terminal

      tangentMeaning :
        integrateTo tangent terminal
        ≡ Obs.integratedCriticalProduction T cutoff terminal
            - coefficient * Obs.integratedCriticalDissipation T cutoff terminal
      tangentMeaning =
        trans
          (integrationCongruent integrationLinearity
            (liveCriticalEnergyTangentSplit D cutoff)
            terminal)
          (integrateScaledDifference
            (Obs.productionRateAt T cutoff)
            (Obs.dissipationRateAt T cutoff)
            coefficient terminal)

      balance :
        Obs.criticalEnergyAt T cutoff terminal
          - Obs.criticalEnergyAt T cutoff initialTime
        ≡ Obs.integratedCriticalProduction T cutoff terminal
            - coefficient * Obs.integratedCriticalDissipation T cutoff terminal
      balance = trans (sym endpointFTC) tangentMeaning
    in
    trans
      (solve
        ( Obs.criticalEnergyAt T cutoff terminal
        ∷ Obs.criticalEnergyAt T cutoff initialTime
        ∷ coefficient
        ∷ Obs.integratedCriticalDissipation T cutoff terminal
        ∷ [] ))
      (trans
        (cong
          (λ value →
            value
              + Obs.criticalEnergyAt T cutoff initialTime
              + coefficient * Obs.integratedCriticalDissipation T cutoff terminal)
          balance)
        (solve
          ( Obs.criticalEnergyAt T cutoff terminal
          ∷ Obs.criticalEnergyAt T cutoff initialTime
          ∷ Obs.integratedCriticalProduction T cutoff terminal
          ∷ coefficient
          ∷ Obs.integratedCriticalDissipation T cutoff terminal
          ∷ [] )))

literalModeCriticalEnergyDerivativeCompilerClosed : Bool
literalModeCriticalEnergyDerivativeCompilerClosed = true

literalFixedListCriticalEnergyDerivativeCompilerClosed : Bool
literalFixedListCriticalEnergyDerivativeCompilerClosed = true

integratedCriticalEnergyCompilerClosedGivenCalculus : Bool
integratedCriticalEnergyCompilerClosedGivenCalculus = true

concreteScalarFTCInstalled : Bool
concreteScalarFTCInstalled = false

concreteIntegrationLinearityInstalled : Bool
concreteIntegrationLinearityInstalled = false

integratedCriticalEnergyIdentityUnconditionallyClosed : Bool
integratedCriticalEnergyIdentityUnconditionallyClosed = false

literalModeCriticalEnergyDerivativeCompilerClosedIsTrue :
  literalModeCriticalEnergyDerivativeCompilerClosed ≡ true
literalModeCriticalEnergyDerivativeCompilerClosedIsTrue = refl

literalFixedListCriticalEnergyDerivativeCompilerClosedIsTrue :
  literalFixedListCriticalEnergyDerivativeCompilerClosed ≡ true
literalFixedListCriticalEnergyDerivativeCompilerClosedIsTrue = refl

integratedCriticalEnergyCompilerClosedGivenCalculusIsTrue :
  integratedCriticalEnergyCompilerClosedGivenCalculus ≡ true
integratedCriticalEnergyCompilerClosedGivenCalculusIsTrue = refl

concreteScalarFTCInstalledIsFalse : concreteScalarFTCInstalled ≡ false
concreteScalarFTCInstalledIsFalse = refl

concreteIntegrationLinearityInstalledIsFalse :
  concreteIntegrationLinearityInstalled ≡ false
concreteIntegrationLinearityInstalledIsFalse = refl

integratedCriticalEnergyIdentityUnconditionallyClosedIsFalse :
  integratedCriticalEnergyIdentityUnconditionallyClosed ≡ false
integratedCriticalEnergyIdentityUnconditionallyClosedIsFalse = refl
