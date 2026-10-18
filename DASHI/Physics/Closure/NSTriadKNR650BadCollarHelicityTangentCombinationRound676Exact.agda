{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650BadCollarHelicityTangentCombinationRound676Exact where

------------------------------------------------------------------------
-- ROUND676 / BAD-COLLAR C2 RESIDUAL ON THE COMBINED SIGNED
--              RATE * (4 EXTERNAL-HELICITY - FLUX-TANGENT) CARRIER
--
-- R667 gives on the live fixed output
--
--   16 Q
--     = 4 SelfMismatch
--       + 4 ExternalNetwork
--       - R FluxTangent.
--
-- R675 identifies, on the SAME physical system/output,
--
--   ExternalNetwork
--     = R * ExternalHelicityRows,
--
-- with the R606/R607 rate multiplier preserved exactly.
--
-- Therefore pure rational algebra gives
--
--   16 Q
--     = 4 SelfMismatch
--       + R * (4 ExternalHelicityRows - FluxTangent).
--
-- This is the preferred signed local C2 search coordinate.  In particular,
-- it does NOT split the external-helicity and flux-tangent pieces into
-- separate absolute-value obligations.  Any cancellation between them remains
-- visible under their common physical rate multiplier.
--
-- No estimate, norm, absolute value, positivity replacement, or new Clay leaf
-- is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; Positive; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as R30
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedEndpointCompilerExact as Endpoint
import DASHI.Physics.Closure.NSTriadKNA3CenteredKernelNormalFormExact as Kernel
import DASHI.Physics.Closure.NSTriadKNR650EuclideanCollarRefinementRound656Exact as R656
import DASHI.Physics.Closure.NSTriadKNR650BadCollarMismatchNetworkSplitRound667Exact as R667
import DASHI.Physics.Closure.NSTriadKNR650ExternalNetworkToHelicityRowsRound675Exact as R675

F : C3.RealField _
F = Rational.rationalRealField

module LiveCombined
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
    (scalarScaleCalculus :
      R416.ScalarConstantDerivativeCalculus
        Time ScalarDerivativeOf)
    (FTC :
      R564.ScalarFundamentalTheorem564
        Time initialTime integrateTo ScalarDerivativeOf)
    (integrationLinearity :
      Energy.ScalarIntegrationLinearity Time integrateTo)
    (D :
      R408.LiteralDynamics.LiteralRHSTrajectoryData
        Time initialTime integrateTo VectorDerivativeOf) where

  module N = R667.LiveNetworkSplit
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus scalarScaleCalculus FTC integrationLinearity D

  module Live = R408.LiteralDynamics
    Time initialTime integrateTo VectorDerivativeOf

  module At
      (cutoff : Nat)
      (output : Z3.FourierMode)
      (time : Time)
      (viscosityPositive :
        Positive (R30.viscosity (N.End.physicalSystemAt cutoff time)))
      (outputNonzero : Z3.NonZeroMode output) where

    module Base = N.At
      cutoff output time viscosityPositive outputNonzero

    module Helicity = R675.ExternalHelicityRows675
      (N.End.physicalSystemAt cutoff time)
      N.End.S
      N.C.K.L
      N.C.K.H
      (Live.Base.velocityTransverse N.C.K.state cutoff time)
      output

    residual : ℚ
    residual = Base.residual

    externalHelicityRows : ℚ
    externalHelicityRows =
      Helicity.helicityExternalRows Helicity.fibre

    externalNetworkIsRateWeightedHelicity :
      Base.Split.externalNetworkContribution
      ≡ Base.M.rateTotal * externalHelicityRows
    externalNetworkIsRateWeightedHelicity =
      Helicity.rateWeightedExternalNetworkIsHelicityRows
        Base.M.rateTotal

    sixteenResidualIsSelfPlusRateCombinedSigned :
      (Kernel.four * Kernel.four) * residual
      ≡
      Kernel.four * Base.Split.selfMismatch
        + Base.M.rateTotal
            * (Kernel.four * externalHelicityRows
              - Base.M.fluxTangentFull)
    sixteenResidualIsSelfPlusRateCombinedSigned =
      trans
        Base.sixteenResidualIsSelfExternalMinusFluxTangent
        (trans
          (cong
            (λ external →
              Kernel.four * Base.Split.selfMismatch
                + Kernel.four * external
                - Base.M.rateTotal * Base.M.fluxTangentFull)
            externalNetworkIsRateWeightedHelicity)
          (solve
            ( Base.Split.selfMismatch
            ∷ Base.M.rateTotal
            ∷ externalHelicityRows
            ∷ Base.M.fluxTangentFull
            ∷ Kernel.four
            ∷ [])))

    activeBadCollarCombinedSigned :
      (Kshell : Nat) →
      R656.badCollarPacket Kshell output ≡ true →
      (Kernel.four * Kernel.four) * residual
      ≡
      Kernel.four * Base.Split.selfMismatch
        + Base.M.rateTotal
            * (Kernel.four * externalHelicityRows
              - Base.M.fluxTangentFull)
    activeBadCollarCombinedSigned Kshell active =
      sixteenResidualIsSelfPlusRateCombinedSigned

------------------------------------------------------------------------
-- Status / proof-search firewall.
------------------------------------------------------------------------

round676BadCollarResidualOnCombinedHelicityTangentCarrier : Bool
round676BadCollarResidualOnCombinedHelicityTangentCarrier = true

round676R607RateMultiplierFactoredOutsideCombinedSignedTerm : Bool
round676R607RateMultiplierFactoredOutsideCombinedSignedTerm = true

round676ExternalHelicityAndFluxTangentMustBePaidSeparately : Bool
round676ExternalHelicityAndFluxTangentMustBePaidSeparately = false

round676CombinedSignedHelicityTangentPaymentClosed : Bool
round676CombinedSignedHelicityTangentPaymentClosed = false

round676SelectedSelfMismatchPaymentClosed : Bool
round676SelectedSelfMismatchPaymentClosed = false

round676IntroducesEstimate : Bool
round676IntroducesEstimate = false

round676IntroducesNewClayLeaf : Bool
round676IntroducesNewClayLeaf = false

round676C2Closed : Bool
round676C2Closed = false

round676ClayPromotion : Bool
round676ClayPromotion = false

round676BadCollarResidualOnCombinedHelicityTangentCarrierIsTrue :
  round676BadCollarResidualOnCombinedHelicityTangentCarrier ≡ true
round676BadCollarResidualOnCombinedHelicityTangentCarrierIsTrue = refl

round676R607RateMultiplierFactoredOutsideCombinedSignedTermIsTrue :
  round676R607RateMultiplierFactoredOutsideCombinedSignedTerm ≡ true
round676R607RateMultiplierFactoredOutsideCombinedSignedTermIsTrue = refl

round676ExternalHelicityAndFluxTangentMustBePaidSeparatelyIsFalse :
  round676ExternalHelicityAndFluxTangentMustBePaidSeparately ≡ false
round676ExternalHelicityAndFluxTangentMustBePaidSeparatelyIsFalse = refl

round676CombinedSignedHelicityTangentPaymentClosedIsFalse :
  round676CombinedSignedHelicityTangentPaymentClosed ≡ false
round676CombinedSignedHelicityTangentPaymentClosedIsFalse = refl

round676SelectedSelfMismatchPaymentClosedIsFalse :
  round676SelectedSelfMismatchPaymentClosed ≡ false
round676SelectedSelfMismatchPaymentClosedIsFalse = refl

round676IntroducesEstimateIsFalse :
  round676IntroducesEstimate ≡ false
round676IntroducesEstimateIsFalse = refl

round676IntroducesNewClayLeafIsFalse :
  round676IntroducesNewClayLeaf ≡ false
round676IntroducesNewClayLeafIsFalse = refl

round676C2ClosedIsFalse :
  round676C2Closed ≡ false
round676C2ClosedIsFalse = refl

round676ClayPromotionIsFalse :
  round676ClayPromotion ≡ false
round676ClayPromotionIsFalse = refl
