{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopMachinSelectedImaginaryPhaseWeldExact where

-- SOURCE-WRITTEN; local native typecheck pending.
-- The actual original Bishop Machin/Cayley half-phase and ONE original
-- imaginary exponential product determine e_B^(i*pi_M)=-1.
-- This is the precise imaginary-phase readout needed by the CM163 q
-- bridge; it does NOT identify the Cartesian exp with a distinct
-- analytic exponent or assert the independent complex mixed-product law.
--
-- Proven from original K05-PI source consumers, not an external
-- classical pi identity or an arbitrary sine-zero hypothesis.

import Real as R
import DASHI.Analysis.BishopSetoidComplexExact as C
import DASHI.Analysis.BishopImaginaryProductPythagoreanReuseExact as Product
import DASHI.Analysis.BishopMachinCayleyHalfPhaseToFirstZeroExact as K05
import DASHI.Analysis.BishopMachinQuarterPhaseQuadruplicationAlgebraExact as Quad
import DASHI.Moonshine.BishopMachinSetoidComplexInstanceExact as Route
import DASHI.Foundations.BishopMachinArctanConstructionExact as M
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open import Data.Product.Base using (proj₁; proj₂)

selectedMinusOne : C.BishopComplex
selectedMinusOne = C.complex (R.- R.1ℝ) R.0ℝ

-- Exact original-source consumer: the only PI-dependent analytic input
-- is K05.OriginalMachinCayleySameObjectEvaluation, plus the already
-- specified genuine imaginary exponential product.
machinImaginaryPhase :
  (inputs : Round11.BishopCutset) →
  Product.Round11ImaginaryExpMultiplicative inputs →
  K05.OriginalMachinCayleySameObjectEvaluation inputs →
  C._≈C_
    (C.expC (Route.machinTranscendentals inputs)
      (C.pureImaginary M.bishopMachinPi))
    selectedMinusOne
machinImaginaryPhase inputs product sameObject =
  let
    quarterEqual =
      K05.sourceMachinQuarterEqualityFromCayley inputs product
        (C.≈C-trans sameObject
          K05.CayleyBridge.originalMachinRationalCayleyIsBishopImaginaryUnit)
    endpoints =
      Product.round11MachinTrigEndpointFromImaginaryProduct
        inputs product quarterEqual
  in C.≈C-trans
    (C.expImaginaryIsTrigPair
      (Route.machinTranscendentals inputs) M.bishopMachinPi)
    (C.complex-equivalent (proj₂ endpoints) (proj₁ endpoints))
