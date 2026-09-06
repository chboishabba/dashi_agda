module DASHI.Analysis.NonArchimedeanPadicCylinderBorelSourceExact where

------------------------------------------------------------------------
-- P-ADIC RESIDUE CYLINDERS DETERMINE BOREL MEASURES -- SOURCE/LIBRARY RECEIPT
--
-- The last topology seam in probability-measure Gibbs uniqueness is paid by
-- existing Mathlib objects rather than new p-adic analysis.
--
-- Literal source/library chain:
--
--   PadicInt.toZModPow n : Z_p ->+* ZMod (p^n)
--   PadicInt.ker_toZModPow
--       ker(toZModPow n) = span {p^n}
--   PadicInt.norm_le_pow_iff_mem_span_pow
--       metric/valuation neighborhoods <-> p^n-divisibility
--   Metric.nhds_basis_ball
--       metric balls form the neighborhood basis
--   ultrametric balls are clopen
--   Measure.ext_of_generateFrom_of_iUnion
--       finite measures agreeing on a generating pi-system are equal.
--
-- Thus a fiber of toZModPow is a coset of p^n Z_p, hence a residue cylinder / 
-- p-adic ball.  Varying n and the residue gives the clopen cylinder basis, and
-- equality on all such cylinders determines the Borel probability measure.
--
-- Authority firewall:
--   source-library dependency closure != Agda kernel-checking Mathlib.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record PadicCylinderBorelReceipt : Set where
  constructor padicCylinderBorelReceipt
  field
    toZModPowOwned : Bool
    kernelToZModPowOwned : Bool
    normPowDivisibilityBridgeOwned : Bool
    metricBallBasisOwned : Bool
    ultrametricBallsClopenOwned : Bool
    finiteMeasureExtOnGeneratingPiSystemOwned : Bool
    residueFibresArePadicCylinders : Bool
    cylindersDetermineBorelMeasure : Bool
    agdaKernelChecksMathlibChain : Bool

canonicalPadicCylinderBorelReceipt : PadicCylinderBorelReceipt
canonicalPadicCylinderBorelReceipt =
  padicCylinderBorelReceipt
    true true true true true true true true false

residueFibresAreDetermining :
  PadicCylinderBorelReceipt.cylindersDetermineBorelMeasure
    canonicalPadicCylinderBorelReceipt
  ≡ true
residueFibresAreDetermining = refl

crossKernelBoundaryPreserved :
  PadicCylinderBorelReceipt.agdaKernelChecksMathlibChain
    canonicalPadicCylinderBorelReceipt
  ≡ false
crossKernelBoundaryPreserved = refl
