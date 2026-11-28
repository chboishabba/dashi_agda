module DASHI.Moonshine.CM163BishopOriginalQPhaseFromCayleyExact where

-- SOURCE-WRITTEN / NOT NATIVE-CHECKED.
-- Actual Bishop q phase e_B^(2*pi_B*i*tau) =
--       e_B^(-pi_B*sqrt163-i*pi_B) = -e_B^(-pi_B*sqrt163).
-- Conditional ONLY on K05's original exp/atan Cayley source evaluation
-- and the already-owned imaginary exponential product.
-- The real radius and selected negative-real q are existing originals;
-- do not substitute classical Real.pi or a second exponential.
--
-- Unlike a free "phase at the CM point" assumption, this explicitly
-- constructs the phase from the previously known original Machin
-- quarter-angle + 2 arctangent evaluations.
-- Cartesian component map is the same Bishop real, not an isomorphism
-- between different real-number constructions.

open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
open import Data.Product.Base using (_,_; proj₁; proj₂)
import Real as R
open R using (_*_; _≃_)
import RealProperties as P
import DASHI.Analysis.BishopSetoidComplexExact as Setoid
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Series
import DASHI.Analysis.BishopImaginaryProductPythagoreanReuseExact as Product
import DASHI.Physics.YangMills.BalabanBishopSeriesParityAndLimitExact as Parity
import DASHI.Analysis.BishopMachinCayleyHalfPhaseToFirstZeroExact as K05
import DASHI.Analysis.BishopMachinRationalCayleyToOriginalComplexExact as Cayley
import DASHI.Analysis.BishopMachinQuarterPhaseQuadruplicationAlgebraExact as Quad
import DASHI.Moonshine.BishopMachinSetoidComplexInstanceExact as Route
import DASHI.Moonshine.JInvariantBishopCM163SelectedDiskExact as CM
import DASHI.Moonshine.CM163BishopSelectedQScaleTransportExact as Scale
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialSetoidCongruenceExact as ExpCong
import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11

-- The actual Bishop real pair is unchanged: only record wrappers differ.
toSeries : Setoid.BishopComplex → Series.BishopComplex
toSeries z = Series.complex (Setoid.re z) (Setoid.im z)

seriesCongruent : ∀ {x y} → Setoid._≈C_ x y →
  Series._≈C_ (toSeries x) (toSeries y)
seriesCongruent h = Setoid.reEquivalent h , Setoid.imEquivalent h

-- The real exponential is from the existing native Bishop exponential
-- and its original selected q-radius, not a second analytic evaluation.
radiusRead :
  Exp.bishopExp (R.- Scale.fullDiskScale) ≃ CM.radius
radiusRead =
  ExpCong.bishopExpCongruent
    (P.-‿cong (P.≃-symm Scale.exponentToDisk))

module At (inputs : Round11.BishopCutset)
  (product : Product.Round11ImaginaryExpMultiplicative inputs)
  (cayley : K05.OriginalMachinCayleySameObjectEvaluation inputs) where

  quarterEqual :
    R._≃_ (Quad.quarterCos inputs)
      (Quad.quarterSin inputs)
  quarterEqual =
    K05.sourceMachinQuarterEqualityFromCayley inputs product
      (Setoid.≈C-trans cayley
        Cayley.originalMachinRationalCayleyIsBishopImaginaryUnit)

  endpoints :
    (R._≃_ (Product.sinB inputs Machin.bishopMachinPi) R.0ℝ)
    ×
    (R._≃_ (Product.cosB inputs Machin.bishopMachinPi)
      (R.- R.1ℝ))
  endpoints =
    Product.round11MachinTrigEndpointFromImaginaryProduct
      inputs product quarterEqual

  -- Use exact signed algebra: exp(-p)*(-1)=-exp(-p),
  -- exp(-p)*0=0. The two endpoint signs are NOT squared away.
  realPhase :
    (Exp.bishopExp (R.- Scale.fullDiskScale) *
      Product.cosB inputs Machin.bishopMachinPi)
      ≃ (R.- CM.radius)
  realPhase =
    P.≃-trans
      (P.*-congˡ (P.≃-trans
        (Parity.bishopCosNeg (Round11.round11ParityInputs inputs)
          (R.- Machin.bishopMachinPi))
        (proj₂ endpoints)))
      (P.≃-trans
        (let open P.ℝ-Solver in
          solve 1 (λ a → a ⊗ (⊝ Κ (+ 1 / 1)) ⊜ ⊝ a)
            P.≃-refl (Exp.bishopExp (R.- Scale.fullDiskScale)))
        (P.-‿cong radiusRead))

  imaginaryPhase :
    (Exp.bishopExp (R.- Scale.fullDiskScale) *
      Product.sinB inputs Machin.bishopMachinPi)
      ≃ R.0ℝ
  imaginaryPhase =
    P.≃-trans
      (P.*-congˡ
        (P.≃-trans
          (Parity.bishopSinNeg (Round11.round11ParityInputs inputs)
            Machin.bishopMachinPi)
          (P.-‿cong (proj₁ endpoints))))
      (let open P.ℝ-Solver in
        solve 1 (λ a → a ⊗ (⊝ Κ (+ 0 / 1)) ⊜ Κ (+ 0 / 1))
          P.≃-refl (Exp.bishopExp (R.- Scale.fullDiskScale)))

  -- The original complex exponential at the actual tau has exponent
  -- -pi_M*sqrt163-i*pi_M. Scale.halfToFull identifies it with
  -- 2*pi_M*i*((-1+i sqrt163)/2), without invoking foreign pi.
  originalComplexQ : Setoid.BishopComplex
  originalComplexQ =
    Setoid.expC (Route.machinTranscendentals inputs)
      (Setoid.complex (R.- Scale.fullDiskScale)
        Machin.bishopMachinPi)

  -- This is the requested actual same-source selected-q phase.
  originalPhaseSelected :
    Series._≈C_ (toSeries originalComplexQ) CM.q
  originalPhaseSelected = realPhase , imaginaryPhase

-- All original phase multiplication and quarter-angle composition are
-- supplied by old K05 owners. The two atomic arctan series evaluations
-- are the precise remaining SOURCE producer obligations, not the final
-- CM negative-q equality or a generic "pi is classical" assumption.
import DASHI.Analysis.BishopMachinTwoPointCayleyCompositionExact as TwoPoint
import DASHI.Analysis.BishopMachinCayleyNativeProductFirstZeroExact as Native

module FromTwoOriginalAtans
  (inputs : Round11.BishopCutset)
  (five : TwoPoint.OriginalAtanFiveCayleyEvaluation inputs)
  (twoHundredThirtyNine :
    TwoPoint.OriginalAtan239CayleyEvaluation inputs) where

  module Result = At inputs
    (Native.originalNativeImaginaryExpProduct inputs)
    (TwoPoint.nativeCombinedCayleyFromTwoOriginalAtanValues
      inputs five twoHundredThirtyNine)

  originalQ :
    Series._≈C_ (toSeries Result.originalComplexQ) CM.q
  originalQ = Result.originalPhaseSelected
