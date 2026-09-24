{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650HelicityTangentSelfCollapseRound677Exact where

------------------------------------------------------------------------
-- ROUND677 / COMBINED EXTERNAL-HELICITY MINUS TANGENT COLLAPSES TO SELF CHANNEL
--
-- R676 isolates the signed combination
--
--   4 H_ext - FluxTangent.
--
-- Two already-proved exact identities live on the SAME R606/R598 fibre:
--
--   (1)  ForcingFull = SelfForcingFull + ExternalForcingFull       [R606]
--   (2)  4 ForcingFull = 4 SelfKernelWork + FluxTangent           [R598]
--
-- and R675 identifies ExternalForcingFull = H_ext.
--
-- Eliminating ForcingFull gives, exactly,
--
--   4 H_ext - FluxTangent
--     = 4 (SelfKernelWork - SelfForcingFull).
--
-- Thus the external-helicity/tangent combination is NOT an independent
-- analytic channel at this algebraic layer.  It collapses back onto a signed
-- discrepancy entirely inside the selected-self channel.
--
-- No estimate, absolute value, positivity replacement, or new Clay leaf is
-- introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; Positive; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

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
import DASHI.Physics.Closure.NSTriadKNR650BadCollarHelicityTangentCombinationRound676Exact as R676

F : C3.RealField _
F = Rational.rationalRealField

module LiveSelfCollapse
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

  module C = R676.LiveCombined
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus scalarScaleCalculus FTC integrationLinearity D

  module At
      (cutoff : Nat)
      (output : Z3.FourierMode)
      (time : Time)
      (viscosityPositive :
        Positive (R30.viscosity (C.N.End.physicalSystemAt cutoff time)))
      (outputNonzero : Z3.NonZeroMode output) where

    module Base = C.At
      cutoff output time viscosityPositive outputNonzero

    selfForcingFull : ℚ
    selfForcingFull =
      Base.Base.Split.Split.selfForcingFull

    externalForcingFull : ℚ
    externalForcingFull =
      Base.Base.Split.Split.externalForcingFull

    forcingFull : ℚ
    forcingFull =
      Base.Base.Split.Split.forcingFull

    selfKernelWork : ℚ
    selfKernelWork =
      Base.Base.Base.M.selfKernelWork

    fluxTangentFull : ℚ
    fluxTangentFull =
      Base.Base.Base.M.fluxTangentFull

    externalHelicityRows : ℚ
    externalHelicityRows =
      Base.externalHelicityRows

    externalHelicityIsExternalForcing :
      externalHelicityRows ≡ externalForcingFull
    externalHelicityIsExternalForcing =
      sym Base.Helicity.externalForcingFullIsHelicityRows

    forcingSplit :
      forcingFull ≡ selfForcingFull + externalForcingFull
    forcingSplit =
      Base.Base.Split.Split.forcingFullSplitsSelfExternal

    fourForcingIsSelfKernelPlusTangent :
      Kernel.four * forcingFull
      ≡ Kernel.four * selfKernelWork + fluxTangentFull
    fourForcingIsSelfKernelPlusTangent =
      Base.Base.Base.M.fourForcingFullIsFourSelfKernelPlusFlux

    combinedHelicityTangentIsSelfDiscrepancy :
      Kernel.four * externalHelicityRows - fluxTangentFull
      ≡
      Kernel.four * (selfKernelWork - selfForcingFull)
    combinedHelicityTangentIsSelfDiscrepancy =
      trans
        (cong
          (λ ext → Kernel.four * ext - fluxTangentFull)
          externalHelicityIsExternalForcing)
        (let
          Ffull = forcingFull
          Fself = selfForcingFull
          Fext = externalForcingFull
          Wself = selfKernelWork
          T = fluxTangentFull

          splitScaled :
            Kernel.four * Ffull
            ≡ Kernel.four * Fself + Kernel.four * Fext
          splitScaled =
            trans
              (cong (Kernel.four *_) forcingSplit)
              (solve (Kernel.four ∷ Fself ∷ Fext ∷ []))

          extFromFull :
            Kernel.four * Fext
            ≡ Kernel.four * Ffull - Kernel.four * Fself
          extFromFull =
            trans
              (sym
                (solve
                  (Kernel.four ∷ Ffull ∷ Fself ∷ Fext ∷ [])))
              (cong
                (_- Kernel.four * Fself)
                (sym splitScaled))

          fullFromKernel :
            Kernel.four * Ffull
            ≡ Kernel.four * Wself + T
          fullFromKernel =
            fourForcingIsSelfKernelPlusTangent
        in
        trans
          (cong (_- T) extFromFull)
          (trans
            (cong
              (λ fullScaled →
                (fullScaled - Kernel.four * Fself) - T)
              fullFromKernel)
            (solve
              (Kernel.four ∷ Wself ∷ Fself ∷ T ∷ []))))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round677CombinedHelicityTangentCollapsesToSelfDiscrepancy : Bool
round677CombinedHelicityTangentCollapsesToSelfDiscrepancy = true

round677ExternalHelicityNeedsIndependentPaymentAfterCollapse : Bool
round677ExternalHelicityNeedsIndependentPaymentAfterCollapse = false

round677FluxTangentNeedsIndependentPaymentAfterCollapse : Bool
round677FluxTangentNeedsIndependentPaymentAfterCollapse = false

round677SelfKernelMinusSelfForcingPaymentClosed : Bool
round677SelfKernelMinusSelfForcingPaymentClosed = false

round677IntroducesEstimate : Bool
round677IntroducesEstimate = false

round677IntroducesNewClayLeaf : Bool
round677IntroducesNewClayLeaf = false

round677C2Closed : Bool
round677C2Closed = false

round677ClayPromotion : Bool
round677ClayPromotion = false

round677CombinedHelicityTangentCollapsesToSelfDiscrepancyIsTrue :
  round677CombinedHelicityTangentCollapsesToSelfDiscrepancy ≡ true
round677CombinedHelicityTangentCollapsesToSelfDiscrepancyIsTrue = refl

round677ExternalHelicityNeedsIndependentPaymentAfterCollapseIsFalse :
  round677ExternalHelicityNeedsIndependentPaymentAfterCollapse ≡ false
round677ExternalHelicityNeedsIndependentPaymentAfterCollapseIsFalse = refl

round677FluxTangentNeedsIndependentPaymentAfterCollapseIsFalse :
  round677FluxTangentNeedsIndependentPaymentAfterCollapse ≡ false
round677FluxTangentNeedsIndependentPaymentAfterCollapseIsFalse = refl

round677SelfKernelMinusSelfForcingPaymentClosedIsFalse :
  round677SelfKernelMinusSelfForcingPaymentClosed ≡ false
round677SelfKernelMinusSelfForcingPaymentClosedIsFalse = refl

round677IntroducesEstimateIsFalse :
  round677IntroducesEstimate ≡ false
round677IntroducesEstimateIsFalse = refl

round677IntroducesNewClayLeafIsFalse :
  round677IntroducesNewClayLeaf ≡ false
round677IntroducesNewClayLeafIsFalse = refl

round677C2ClosedIsFalse :
  round677C2Closed ≡ false
round677C2ClosedIsFalse = refl

round677ClayPromotionIsFalse :
  round677ClayPromotion ≡ false
round677ClayPromotionIsFalse = refl
