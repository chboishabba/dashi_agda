module DASHI.Physics.YangMills.BalabanCMP109BetaDifferenceRealAnalysisBridgeExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _-ℝ_)

import DASHI.Physics.YangMills.BalabanBetaPrefixSensitivityToTubeContractionExact as Prefix

------------------------------------------------------------------------
-- EXPLICIT AXIOM BOUNDARY
--
-- This module is intentionally NOT `--safe`.
-- `BalabanBetaPrefixSensitivityToTubeContractionExact` sits on
-- `DASHI.Foundations.RealAnalysisAxioms`, whose real-analysis authority contains
-- postulates.  The canonical CMP109 residual owner therefore does not import
-- this module.  Instead this bridge records the concrete application relative
-- to that existing axiom boundary.
--
-- Source attribution for the underlying RG semantics:
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I.", Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
------------------------------------------------------------------------

betaDifferencePaidRelativeToRealAnalysisAxioms : Bool
betaDifferencePaidRelativeToRealAnalysisAxioms = true

prefixBetaDifferenceAlgebra :
  ∀ {TubePoint}
    (shootingMap : Prefix.BetaPrefixShootingMap TubePoint)
    (left right : TubePoint) →
  let open Prefix.BetaPrefixShootingMap shootingMap in
  initialInverseSquare (renormalisationMap left)
    -ℝ
  initialInverseSquare (renormalisationMap right)
  ≡
  cumulativeBeta left
    -ℝ
  cumulativeBeta right
prefixBetaDifferenceAlgebra = Prefix.sourceMapDifferenceIsBetaDifference
