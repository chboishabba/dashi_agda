module DASHI.Physics.Closure.NSTriadKNDirectIntegratedOrderedOrientedForceBidiExact where

------------------------------------------------------------------------
-- R503 DIRECT INTEGRATED COMPANION <-> ORDERED ORIENTED FORCE KERNEL
--
-- The fibre-level transpose-completion owner proves, without assuming the
-- oriented kernel itself is symmetric,
--
--   DirectFibreCompanion = (1/2) * OrderedOffDiagonal(H)
--
-- where H(alpha,beta) is the single signed channel
--
--   w(alpha,beta) Re <G_alpha,D_beta>.
--
-- This owner lifts that identity over R498's exact selected-output
-- concatenation, then over R499/R500's literal live trajectory and existing
-- integration transport authority.  We keep all factors division-free in the
-- exported theorem:
--
--   4 * integratedDirectCompanion
--     = 2 * integratedOrderedOrientedForce.
--
-- Thus R503's sole analytic field may be searched directly on the signed
-- ordered H kernel.  No norm, absolute value, Cauchy/Schur majorant, Laplace
-- representation, shell count, or new integration axiom enters.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNFibreLocalR378GlobalInstantaneousGramFluxRound398Exact as R398
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNFixedOutputLiveGlobalFluxRound406Exact as R406
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNDirectResolventGlobalCompanionRound498Exact as R498
import DASHI.Physics.Closure.NSTriadKNDirectResolventTrajectoryCompanionRound499Exact as R499
import DASHI.Physics.Closure.NSTriadKNDirectResolventIntegratedCompanionRound500Exact as R500
import DASHI.Physics.Closure.NSTriadKNDirectCompanionOrientedForceTransposeCompletionBidiExact as Oriented
import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNSymmetrizedHalfUnorderedOrderedExact as HalfOrdered
import DASHI.Physics.Closure.NSTriadKNHeatFactorizedPairRemainderRound299Exact as R299

F : C3.RealField _
F = Rational.rationalRealField

two : ℚ
two = R539.two

module GlobalOrdered
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (P : R225.PhysicalFixedOutputHelicityData
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem)
      S L H
      (Audit.velocityAt (Field30.finiteSystem physicalSystem))) where

  module Global = R398.GlobalFluxLocal physicalSystem S L H P
  module Direct = R498.DirectGlobal physicalSystem S L H P
  module O = Oriented.OrientedForce physicalSystem S

  globalOrderedOrientedForce :
    (cutoff : Nat) →
    (outputs : List Z3.FourierMode) →
    Global.OutputFibresPositiveOn cutoff outputs → ℚ
  globalOrderedOrientedForce cutoff [] Global.positiveOutputsNil = 0ℚ
  globalOrderedOrientedForce cutoff (output ∷ outputs)
      (Global.positiveOutputsCons headPositive tailPositive) =
    R539.orderedOffDiagonalSum O.orientedForceCross
      (Output.physicalOutputFiber cutoff output)
    + globalOrderedOrientedForce cutoff outputs tailPositive

  twiceDirectFibreIsOrdered :
    (items : List Physical.PhysicalTriadIncidence) →
    (positive : O.Local.PairRatePositiveOn items) →
    two * O.Fibre.directFibreCompanion items positive
    ≡ R539.orderedOffDiagonalSum O.orientedForceCross items
  twiceDirectFibreIsOrdered items positive =
    let
      ordered = R539.orderedOffDiagonalSum O.orientedForceCross items
    in
    trans
      (cong (two *_) (O.directFibreIsHalfOrderedOrientedForce items positive))
      (solve (ordered ∷ []))

  twiceGlobalDirectIsOrdered :
    (cutoff : Nat) →
    (outputs : List Z3.FourierMode) →
    (positive : Global.OutputFibresPositiveOn cutoff outputs) →
    two * Direct.globalDirectCompanion cutoff outputs positive
    ≡ globalOrderedOrientedForce cutoff outputs positive
  twiceGlobalDirectIsOrdered cutoff [] Global.positiveOutputsNil = solve []
  twiceGlobalDirectIsOrdered cutoff (output ∷ outputs)
      (Global.positiveOutputsCons headPositive tailPositive) =
    let
      fibre = Output.physicalOutputFiber cutoff output
      headDirect = O.Fibre.directFibreCompanion fibre headPositive
      tailDirect = Direct.globalDirectCompanion cutoff outputs tailPositive
    in
    trans
      (solve (headDirect ∷ tailDirect ∷ []))
      (cong₂ _+_
        (twiceDirectFibreIsOrdered fibre headPositive)
        (twiceGlobalDirectIsOrdered cutoff outputs tailPositive))

module LiveOrdered
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Flux = R406.FixedLiveFlux
    Time initialTime integrateTo DerivativeOf
  module Direct = R499.DirectTrajectory
    Time initialTime integrateTo DerivativeOf

  instantaneousOrderedOrientedForce :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  instantaneousOrderedOrientedForce T R cutoff time =
    let
      module At = Flux.At T R cutoff time
      module G = GlobalOrdered
        At.PS
        (Dyn.Base.S (Dyn.forgetDynamics T))
        (Dyn.Base.L (Dyn.forgetDynamics T))
        (Dyn.Base.H (Dyn.forgetDynamics T))
        At.P
    in
    G.globalOrderedOrientedForce
      cutoff At.outputs At.canonicalOutputPositivity

  twiceInstantaneousDirectIsOrdered :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (time : Time) →
    two * Direct.instantaneousDirectCompanion T R cutoff time
    ≡ instantaneousOrderedOrientedForce T R cutoff time
  twiceInstantaneousDirectIsOrdered T R cutoff time =
    let
      module At = Flux.At T R cutoff time
      module G = GlobalOrdered
        At.PS
        (Dyn.Base.S (Dyn.forgetDynamics T))
        (Dyn.Base.L (Dyn.forgetDynamics T))
        (Dyn.Base.H (Dyn.forgetDynamics T))
        At.P
    in
    G.twiceGlobalDirectIsOrdered
      cutoff At.outputs At.canonicalOutputPositivity

module IntegratedOrdered
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (integration : R495.IntegrationTransportAuthority Time integrateTo) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Live = LiveOrdered Time initialTime integrateTo DerivativeOf
  module Direct = R500.IntegratedDirect
    Time initialTime integrateTo DerivativeOf integration

  integratedOrderedOrientedForce :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  integratedOrderedOrientedForce T R cutoff terminal =
    integrateTo (Live.instantaneousOrderedOrientedForce T R cutoff) terminal

  integrateTwo :
    (f : Time → ℚ) →
    (terminal : Time) →
    integrateTo (λ t → two * f t) terminal
    ≡ two * integrateTo f terminal
  integrateTwo f terminal =
    let
      twice : Time → ℚ
      twice t = f t + f t

      pointwise : (t : Time) → two * f t ≡ twice t
      pointwise t = solve (f t ∷ [])

      toCopies :
        integrateTo (λ t → two * f t) terminal
        ≡ integrateTo twice terminal
      toCopies =
        R495.integrateCongruent integration
          (λ t → two * f t) twice pointwise terminal
    in
    trans toCopies
      (trans
        (R495.integrateAdd integration f f terminal)
        (solve (integrateTo f terminal ∷ [])))

  integratedOrderedIsTwiceDirect :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (terminal : Time) →
    integratedOrderedOrientedForce T R cutoff terminal
    ≡ two * Direct.integratedDirectCompanion T R cutoff terminal
  integratedOrderedIsTwiceDirect T R cutoff terminal =
    let
      direct : Time → ℚ
      direct = Direct.Direct.instantaneousDirectCompanion T R cutoff
      ordered : Time → ℚ
      ordered = Live.instantaneousOrderedOrientedForce T R cutoff

      pointwise : (t : Time) → ordered t ≡ two * direct t
      pointwise t = sym (Live.twiceInstantaneousDirectIsOrdered T R cutoff t)

      transport :
        integrateTo ordered terminal
        ≡ integrateTo (λ t → two * direct t) terminal
      transport =
        R495.integrateCongruent integration
          ordered (λ t → two * direct t) pointwise terminal
    in
    trans transport (integrateTwo direct terminal)

  fourIntegratedDirectIsTwoOrdered :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (terminal : Time) →
    R299.four * Direct.integratedDirectCompanion T R cutoff terminal
    ≡ two * integratedOrderedOrientedForce T R cutoff terminal
  fourIntegratedDirectIsTwoOrdered T R cutoff terminal
      rewrite integratedOrderedIsTwiceDirect T R cutoff terminal =
    solve (Direct.integratedDirectCompanion T R cutoff terminal ∷ [])

------------------------------------------------------------------------
-- Status / delayed-lossy-observer boundary.
------------------------------------------------------------------------

r503DirectCompanionRewrittenAsOrderedOrientedKernel : Bool
r503DirectCompanionRewrittenAsOrderedOrientedKernel = true

amplitudeProductRuleHalfIndependentAfterTransposeCompletion : Bool
amplitudeProductRuleHalfIndependentAfterTransposeCompletion = false

normIntroducedBeforeOrderedSignedKernel : Bool
normIntroducedBeforeOrderedSignedKernel = false

absoluteValueIntroducedBeforeOrderedSignedKernel : Bool
absoluteValueIntroducedBeforeOrderedSignedKernel = false

externalSameObjectCompanionReceiptStillRequiredOnDirectRoute : Bool
externalSameObjectCompanionReceiptStillRequiredOnDirectRoute = false

cutoffUniformOrderedOrientedSpacetimeBudgetClosed : Bool
cutoffUniformOrderedOrientedSpacetimeBudgetClosed = false

clayPromotion : Bool
clayPromotion = false

r503DirectCompanionRewrittenAsOrderedOrientedKernelIsTrue :
  r503DirectCompanionRewrittenAsOrderedOrientedKernel ≡ true
r503DirectCompanionRewrittenAsOrderedOrientedKernelIsTrue = refl

externalSameObjectCompanionReceiptStillRequiredOnDirectRouteIsFalse :
  externalSameObjectCompanionReceiptStillRequiredOnDirectRoute ≡ false
externalSameObjectCompanionReceiptStillRequiredOnDirectRouteIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
