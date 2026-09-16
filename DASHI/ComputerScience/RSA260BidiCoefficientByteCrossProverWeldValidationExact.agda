module DASHI.ComputerScience.RSA260BidiCoefficientByteCrossProverWeldValidationExact where

import DASHI.ComputerScience.RSA260BidiCoefficientByteCrossProverWeldExact

------------------------------------------------------------------------
-- RED surface: common 136-byte coefficient carrier.
--
-- The production owner must preserve the distinction between:
--   * runtime coefficient bytes explicitly retained and hash-bound;
--   * Lean source defining the same 17x8 row-byte serialization;
--   * actual kernel-certified cross-prover equality.
------------------------------------------------------------------------

open DASHI.ComputerScience.RSA260BidiCoefficientByteCrossProverWeldExact

validationBoundary : CoefficientByteCrossProverWeldBoundary
validationBoundary = canonicalCoefficientByteCrossProverWeldBoundary
