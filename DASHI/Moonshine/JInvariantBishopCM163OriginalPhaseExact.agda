module DASHI.Moonshine.JInvariantBishopCM163OriginalPhaseExact where

-- SOURCE-WRITTEN, UNCOMPILED. Reuse the existing K05 native product,
-- Cayley and parity owners. No new global period/first-zero premise.
open import Data.Integer.Base using (+_)
import Data.Integer.Base as Z
open import Data.Rational.Unnormalised using (_/_)
import Data.Rational.Unnormalised as Q
open import Data.Product.Base using (_,_; proj₁; proj₂)
import Real as R
import RealProperties as P
import DASHI.Analysis.BishopSetoidComplexExact as C
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Series
import DASHI.Analysis.BishopMachinTwoPointCayleyCompositionExact as Two
import DASHI.Analysis.BishopOriginalMachinCayleyEndpointExact as Closed
import DASHI.Analysis.BishopMachinCayleyHalfPhaseToFirstZeroExact as Half
import DASHI.Analysis.BishopMachinCayleyNativeProductFirstZeroExact as Native
import DASHI.Analysis.BishopMachinRationalCayleyToOriginalComplexExact as Bridge
import DASHI.Analysis.BishopImaginaryProductPythagoreanReuseExact as Prod
import DASHI.Physics.YangMills.BalabanBishopSeriesParityAndLimitExact as Parity
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Cut
import DASHI.Moonshine.BishopMachinSetoidComplexInstanceExact as Route
import DASHI.Moonshine.AbelBishopOriginalQParameterExact as QAt
import DASHI.Moonshine.AbelBishopOriginalComplexCarrierWeldExact as Weld
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneRadiusExact as Radius
import DASHI.Moonshine.JInvariantBishopCM163SelectedDiskExact as CM
import DASHI.Foundations.BishopMachinArctanConstructionExact as M

module AtOriginal (inputs : Cut.BishopCutset) where
  T = Route.machinTranscendentals inputs
  pi = M.bishopMachinPi
  exponent : C.BishopComplex
  exponent = C.complex (R.-_ (Radius.qExponentMagnitude pi CM.imag)) (R.-_ pi)

  -- Literal 2*pi*i times the original tau = -2*pi*Im(tau)-i*pi.
  exponentCoordinates : C._≈C_
    (C._*C_ (QAt.originalTwoPiI T) (Weld.toExponential CM.tau))
    exponent
  exponentCoordinates = C.complex-equivalent
    (let open P.ℝ-Solver in
      solve 2 (λ p h →
        (((Κ Q.1ℚᵘ ⊗ Κ Q.0ℚᵘ) ⊖ (Κ Q.0ℚᵘ ⊗ p)) ⊕
         (((Κ Q.1ℚᵘ ⊗ Κ Q.0ℚᵘ) ⊖ (Κ Q.0ℚᵘ ⊗ p)) ⊕ Κ Q.0ℚᵘ))
        ⊗ Κ ((Z.-_ (+ 1)) / 2) ⊖
        (((Κ Q.0ℚᵘ ⊗ Κ Q.0ℚᵘ) ⊕ (Κ Q.1ℚᵘ ⊗ p)) ⊕
         (((Κ Q.0ℚᵘ ⊗ Κ Q.0ℚᵘ) ⊕ (Κ Q.1ℚᵘ ⊗ p)) ⊕ Κ Q.0ℚᵘ))
        ⊗ h ⊜ (⊝ (Κ (+ 2 / 1) ⊗ p ⊗ h)))
        P.≃-refl pi CM.imag)
    (let open P.ℝ-Solver in
      solve 2 (λ p h →
        (((Κ Q.1ℚᵘ ⊗ Κ Q.0ℚᵘ) ⊖ (Κ Q.0ℚᵘ ⊗ p)) ⊕
         (((Κ Q.1ℚᵘ ⊗ Κ Q.0ℚᵘ) ⊖ (Κ Q.0ℚᵘ ⊗ p)) ⊕ Κ Q.0ℚᵘ))
        ⊗ h ⊕
        (((Κ Q.0ℚᵘ ⊗ Κ Q.0ℚᵘ) ⊕ (Κ Q.1ℚᵘ ⊗ p)) ⊕
         (((Κ Q.0ℚᵘ ⊗ Κ Q.0ℚᵘ) ⊕ (Κ Q.1ℚᵘ ⊗ p)) ⊕ Κ Q.0ℚᵘ))
        ⊗ Κ ((Z.-_ (+ 1)) / 2) ⊜ (⊝ p))
        P.≃-refl pi CM.imag)

  product = Native.originalNativeImaginaryExpProduct inputs

  -- The two precise actual atan-Cayley evaluations, not a first-zero,
  -- global sine positivity, arbitrary q phase or pi-period axiom.
  qFromTwoOriginalAtans :
    Two.OriginalAtanFiveCayleyEvaluation inputs →
    Two.OriginalAtan239CayleyEvaluation inputs →
    Series._≈C_ (QAt.originalRound11MachinQAtForSeries inputs CM.tau) CM.q
  qFromTwoOriginalAtans h5 h239 =
    let
      halfPhase = C.≈C-trans
        (Two.nativeCombinedCayleyFromTwoOriginalAtanValues inputs h5 h239)
        Bridge.originalMachinRationalCayleyIsBishopImaginaryUnit
      quarterEq = Half.sourceMachinQuarterEqualityFromCayley inputs product halfPhase
      endpoints = Prod.round11MachinTrigEndpointFromImaginaryProduct inputs product quarterEq
      cosineNeg = P.≃-trans
        (Parity.bishopCosNeg (Cut.round11ParityInputs inputs) pi)
        (proj₂ endpoints)
      sineNeg = P.≃-trans
        (Parity.bishopSinNeg (Cut.round11ParityInputs inputs) pi)
        (P.≃-trans (P.-‿cong (proj₁ endpoints))
          (let open P.ℝ-Solver in solve 0
            ((⊝ Κ Q.0ℚᵘ) ⊜ Κ Q.0ℚᵘ) P.≃-refl))
      phase = C.complex-equivalent
        (P.≃-trans (P.*-congˡ cosineNeg)
          (let open P.ℝ-Solver in solve 1 (λ r →
            r ⊗ (⊝ Κ Q.1ℚᵘ) ⊜ (⊝ r)) P.≃-refl CM.radius))
        (P.≃-trans (P.*-congˡ sineNeg) (P.*-zeroʳ CM.radius))
    in Weld.originalExpEquivalenceToSeries
      (C.≈C-trans (C.expCongruent T exponentCoordinates) phase)

  -- The original configured Round11 series supplies both analytic values.
  qFromOriginalAtans :
    Series._≈C_ (QAt.originalRound11MachinQAtForSeries inputs CM.tau) CM.q
  qFromOriginalAtans = qFromTwoOriginalAtans
    (Closed.originalFive inputs) (Closed.original239 inputs)
