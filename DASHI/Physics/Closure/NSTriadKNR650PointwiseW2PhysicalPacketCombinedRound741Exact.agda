{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650PointwiseW2PhysicalPacketCombinedRound741Exact where

------------------------------------------------------------------------
-- ROUND741 / PHYSICAL NORMAL FORM OF POINTWISE W2
--
-- R740 proves pointwise W2 is exactly
--
--   P_N <= (2nu-delta) d_N + 12 C_N.
--
-- R646/R648 identify the left strict surplus
--
--   P_N - (2nu-delta)d_N
--
-- with the literal R98 physical upper-shell packet strict surplus, once the
-- already-required reality/divergence-free/nonlinear-conservation structure
-- is supplied.
--
-- R723 identifies the right side 12 C_N pointwise with its recombined
-- self+external residue.
--
-- Therefore pointwise W2 is equivalent to ONE literal signed inequality:
--
--   physicalPacketStrictSurplus_N(t)
--     <= combinedSelfExternalResidue_N(t).
--
-- No R406 transport, norm, absolute value, or estimate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedEndpointCompilerExact as Endpoint
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffModeCarrierExact as ModeCarrier
import DASHI.Physics.Closure.NSTriadKNR650NestedFourHelicityTriadOrbitRound700Exact as R700
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNLivePhysicalPacketStrictSurplusRound648Exact as R648
import DASHI.Physics.Closure.NSTriadKNR650CombinedSelfExternalSpacetimeRound723Exact as R723
import DASHI.Physics.Closure.NSTriadKNR650PointwiseW2CancellationRound740Exact as R740

F : C3.RealField _
F = Rational.rationalRealField

module PhysicalW2
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf :
      (Time → ℚ) → (Time → ℚ) → Set)
    (projectedCross :
      R426.ProjectedCrossDerivativeCalculus Time VectorDerivativeOf)
    (vectorAlgebra :
      R425.VectorDerivativeAlgebra Time VectorDerivativeOf)
    (zeroCalculus :
      Endpoint.VectorZeroDerivative Time VectorDerivativeOf)
    (hermitianCalculus :
      R417.HermitianDerivativeCalculus
        Time VectorDerivativeOf ScalarDerivativeOf)
    (constantScaleCalculus :
      R416.ScalarConstantDerivativeCalculus
        Time ScalarDerivativeOf)
    (scalarDerivativeAlgebra :
      R412.ScalarDerivativeAlgebra Time ScalarDerivativeOf)
    (FTC :
      R564.ScalarFundamentalTheorem564
        Time initialTime integrateTo ScalarDerivativeOf)
    (integrationLinearity :
      Energy.ScalarIntegrationLinearity Time integrateTo)
    (integrationTransport :
      R495.IntegrationTransportAuthority Time integrateTo)
    (D :
      R408.LiteralDynamics.LiteralRHSTrajectoryData
        Time initialTime integrateTo VectorDerivativeOf)
    (C :
      ModeCarrier.LiteralModeCarrier.LiteralCutoffModeCarrier
        Time initialTime integrateTo VectorDerivativeOf
        (R408.LiteralDynamics.literalPhysicalTrajectory
          Time initialTime integrateTo VectorDerivativeOf D))
    (R :
      R405.LiteralCutoffSupport.LiteralNonzeroCutoffTrajectory
        Time initialTime integrateTo VectorDerivativeOf
        (R408.LiteralDynamics.literalPhysicalTrajectory
          Time initialTime integrateTo VectorDerivativeOf D)) where

  module W2 = R740.PointwiseCancellation
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module K = W2.K

  module Packet = R648.LivePacketSurplus
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity

  module Combined = R723.CombinedSpacetime
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus
    FTC integrationLinearity integrationTransport D

  globalCommutatorIsR723LiveSum :
    (cutoff : Nat) (time : Time) →
    K.P.globalCommutatorAt cutoff time
    ≡
    Combined.Nested.Orbit.sumCommutatorAt cutoff
      (Canonical.nonzeroCutoffModes cutoff)
      time
  globalCommutatorIsR723LiveSum cutoff time = refl

  twelveGlobalCommutatorIsCombined :
    (cutoff : Nat) (time : Time) →
    R700.twelve * K.P.globalCommutatorAt cutoff time
    ≡ Combined.combinedResidueAt cutoff time
  twelveGlobalCommutatorIsCombined cutoff time =
    trans
      (cong
        (R700.twelve *_)
        (globalCommutatorIsR723LiveSum cutoff time))
      (sym (Combined.At.combinedIsTwelveLiveGlobalCommutator cutoff time))

  literalStrictSurplusIsPhysicalPacket :
    (cutoff : Nat) →
    Packet.LivePhysicalPacketStructure D C cutoff →
    (margin : ℚ) →
    (time : Time) →
    K.productionAt cutoff time
      - (K.twoNu - margin) * K.dissipationAt cutoff time
    ≡ Packet.physicalPacketStrictSurplusRate D cutoff margin time
  literalStrictSurplusIsPhysicalPacket cutoff S margin time =
    trans
      (Packet.Radial.literalStrictSurplusRateSameObject
        D cutoff margin time)
      (Packet.radialStrictSurplusIsPhysicalPacketStrictSurplus
        D C cutoff S margin time)

  physicalPacketBelowCombined :
    (cutoff : Nat) →
    Packet.LivePhysicalPacketStructure D C cutoff →
    ℚ → Time → Set
  physicalPacketBelowCombined cutoff S margin time =
    Packet.physicalPacketStrictSurplusRate D cutoff margin time
    ≤ Combined.combinedResidueAt cutoff time

  strictProductionImpliesPhysicalPacketBelowCombined :
    (cutoff : Nat) →
    (S : Packet.LivePhysicalPacketStructure D C cutoff) →
    (margin : ℚ) →
    (time : Time) →
    W2.strictProductionVsCommutator cutoff time margin →
    physicalPacketBelowCombined cutoff S margin time
  strictProductionImpliesPhysicalPacketBelowCombined
      cutoff S margin time h =
    let
      prod = K.productionAt cutoff time
      diss = K.dissipationAt cutoff time
      comm = K.P.globalCommutatorAt cutoff time
      packet =
        Packet.physicalPacketStrictSurplusRate D cutoff margin time
      combined = Combined.combinedResidueAt cutoff time
      coeff = K.twoNu - margin

      shifted :
        prod - coeff * diss
        ≤ R700.twelve * comm
      shifted =
        let
          minusCommon = 0ℚ - coeff * diss
          translated :
            prod + minusCommon
            ≤
            (coeff * diss + R700.twelve * comm) + minusCommon
          translated = ℚP.+-mono-≤ h ℚP.≤-refl
        in
        subst
          (λ lhs → lhs ≤ R700.twelve * comm)
          (solve (prod ∷ diss ∷ coeff ∷ []))
          (subst
            (λ rhs → prod + minusCommon ≤ rhs)
            (solve (diss ∷ coeff ∷ comm ∷ R700.twelve ∷ []))
            translated)
    in
    subst
      (packet ≤_)
      (twelveGlobalCommutatorIsCombined cutoff time)
      (subst
        (λ lhs → lhs ≤ R700.twelve * comm)
        (literalStrictSurplusIsPhysicalPacket cutoff S margin time)
        shifted)

  physicalPacketBelowCombinedImpliesStrictProduction :
    (cutoff : Nat) →
    (S : Packet.LivePhysicalPacketStructure D C cutoff) →
    (margin : ℚ) →
    (time : Time) →
    physicalPacketBelowCombined cutoff S margin time →
    W2.strictProductionVsCommutator cutoff time margin
  physicalPacketBelowCombinedImpliesStrictProduction
      cutoff S margin time h =
    let
      prod = K.productionAt cutoff time
      diss = K.dissipationAt cutoff time
      comm = K.P.globalCommutatorAt cutoff time
      coeff = K.twoNu - margin

      strictSurplus :
        prod - coeff * diss ≤ R700.twelve * comm
      strictSurplus =
        subst
          (λ lhs → lhs ≤ R700.twelve * comm)
          (sym (literalStrictSurplusIsPhysicalPacket cutoff S margin time))
          (subst
            (Packet.physicalPacketStrictSurplusRate
              D cutoff margin time ≤_)
            (sym (twelveGlobalCommutatorIsCombined cutoff time))
            h)

      addBack :
        (prod - coeff * diss) + coeff * diss
        ≤
        R700.twelve * comm + coeff * diss
      addBack = ℚP.+-mono-≤ strictSurplus ℚP.≤-refl
    in
    subst
      (λ lhs → lhs ≤ coeff * diss + R700.twelve * comm)
      (solve (prod ∷ diss ∷ coeff ∷ []))
      (subst
        (λ rhs →
          (prod - coeff * diss) + coeff * diss ≤ rhs)
        (solve (diss ∷ coeff ∷ comm ∷ R700.twelve ∷ []))
        addBack)

  pointwiseW2ImpliesPhysicalPacketBelowCombined :
    (cutoff : Nat) →
    (S : Packet.LivePhysicalPacketStructure D C cutoff) →
    (margin : ℚ) →
    (time : Time) →
    W2.pointwiseW2 cutoff time margin →
    physicalPacketBelowCombined cutoff S margin time
  pointwiseW2ImpliesPhysicalPacketBelowCombined cutoff S margin time h =
    strictProductionImpliesPhysicalPacketBelowCombined
      cutoff S margin time
      (W2.pointwiseW2ImpliesStrictProductionVsCommutator
        cutoff time margin h)

  physicalPacketBelowCombinedImpliesPointwiseW2 :
    (cutoff : Nat) →
    (S : Packet.LivePhysicalPacketStructure D C cutoff) →
    (margin : ℚ) →
    (time : Time) →
    physicalPacketBelowCombined cutoff S margin time →
    W2.pointwiseW2 cutoff time margin
  physicalPacketBelowCombinedImpliesPointwiseW2 cutoff S margin time h =
    W2.strictProductionVsCommutatorImpliesPointwiseW2
      cutoff time margin
      (physicalPacketBelowCombinedImpliesStrictProduction
        cutoff S margin time h)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round741PointwiseW2IsPhysicalPacketBelowCombined : Bool
round741PointwiseW2IsPhysicalPacketBelowCombined = true

round741LeftCarrierIsLiteralR648PhysicalPacketSurplus : Bool
round741LeftCarrierIsLiteralR648PhysicalPacketSurplus = true

round741RightCarrierIsLiteralR723CombinedResidue : Bool
round741RightCarrierIsLiteralR723CombinedResidue = true

round741RequiresR406Transport : Bool
round741RequiresR406Transport = false

round741IntroducesEstimate : Bool
round741IntroducesEstimate = false

round741PhysicalPacketBelowCombinedClosed : Bool
round741PhysicalPacketBelowCombinedClosed = false

round741W2Closed : Bool
round741W2Closed = false

round741ClayPromotion : Bool
round741ClayPromotion = false

round741PointwiseW2IsPhysicalPacketBelowCombinedIsTrue :
  round741PointwiseW2IsPhysicalPacketBelowCombined ≡ true
round741PointwiseW2IsPhysicalPacketBelowCombinedIsTrue = refl

round741LeftCarrierIsLiteralR648PhysicalPacketSurplusIsTrue :
  round741LeftCarrierIsLiteralR648PhysicalPacketSurplus ≡ true
round741LeftCarrierIsLiteralR648PhysicalPacketSurplusIsTrue = refl

round741RightCarrierIsLiteralR723CombinedResidueIsTrue :
  round741RightCarrierIsLiteralR723CombinedResidue ≡ true
round741RightCarrierIsLiteralR723CombinedResidueIsTrue = refl

round741RequiresR406TransportIsFalse :
  round741RequiresR406Transport ≡ false
round741RequiresR406TransportIsFalse = refl

round741IntroducesEstimateIsFalse :
  round741IntroducesEstimate ≡ false
round741IntroducesEstimateIsFalse = refl

round741PhysicalPacketBelowCombinedClosedIsFalse :
  round741PhysicalPacketBelowCombinedClosed ≡ false
round741PhysicalPacketBelowCombinedClosedIsFalse = refl

round741W2ClosedIsFalse :
  round741W2Closed ≡ false
round741W2ClosedIsFalse = refl

round741ClayPromotionIsFalse :
  round741ClayPromotion ≡ false
round741ClayPromotionIsFalse = refl
