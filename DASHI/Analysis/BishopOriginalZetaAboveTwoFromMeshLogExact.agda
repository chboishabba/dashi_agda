module DASHI.Analysis.BishopOriginalZetaAboveTwoFromMeshLogExact where

------------------------------------------------------------------------
-- P2.01: SOURCE ORIGINAL DIRICHLET ZETA CONSUMES THE ACTUAL
-- TERMINAL NEGATIVE-LOG GAP PROVED BY THE ORIGINAL BISHOP MESH.
--
-- This is not another selected zeta. The exact already-existing
-- FromOriginalNegativeLog construction is instantiated with
-- originalBishopNegativeLogExponentialGap.
--
-- Its region, source terms, uniform Basel bounds and both
-- coordinate limits remain the ORIGINAL source objects.
--
-- The separately configured ZetaHalfPlaneLayer.zetaHalfPlane
-- same-object comparison (P2.03) is not asserted here.
------------------------------------------------------------------------

import DASHI.Analysis.BishopOriginalNegativeLogTerminalFromMeshExact as Log
import DASHI.Analysis.BishopRiemannOriginalZetaAboveTwoExact as Zeta
import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as BC
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

module FromOriginalBishopMeshLog
  (inputs : Round11.Round11BishopCutset)
  where

  module Actual = Zeta.FromOriginalNegativeLog
    inputs Log.originalBishopNegativeLogExponentialGap

  open Actual public

  originalAboveTwoZetaFromCompletedLog :
    (s : BC.BishopComplex) →
    Actual.sourceRegion s →
    BC.BishopComplex
  originalAboveTwoZetaFromCompletedLog =
    Actual.originalZetaAboveTwo
