module DASHI.Wikimedia.IbrahimCannabisContaminantSOTARoadmapRegression where

open import DASHI.Core.Prelude

import DASHI.Wikimedia.IbrahimCannabisContaminantSOTARoadmapExact as SOTA

-- RED surface for the 2026 contaminant/testing roadmap.
-- This module should elaborate only once the SOTA owner exports the
-- route-specific risk, regulatory harmonisation, surveillance and unresolved
-- biopesticide/pyrolysis coordinates below.

sotaBoundary : SOTA.CannabisContaminantSOTABoundary
sotaBoundary = SOTA.canonicalCannabisContaminantSOTABoundary

routeRiskStep : SOTA.SOTAParetoStep
routeRiskStep = SOTA.pareto0

pyrolysisStep : SOTA.SOTAParetoStep
pyrolysisStep = SOTA.pareto1

btResidueStep : SOTA.SOTAParetoStep
btResidueStep = SOTA.pareto2

harmonisationStep : SOTA.SOTAParetoStep
harmonisationStep = SOTA.pareto3
