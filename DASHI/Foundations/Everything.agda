module DASHI.Foundations.Everything where

-- Foundations domain spine.
-- Subdomains own their leaf lists; expand this file by attaching coherent
-- subdomain rollups rather than flattening the whole Foundations directory.

import DASHI.Foundations.UBP.Everything
import DASHI.Foundations.Wette.Everything
import DASHI.Foundations.CoarseFineRefinementEverything
import DASHI.Foundations.BishopSineCosineSetoidCongruenceExact
import DASHI.Foundations.BishopConcreteTrigSeriesConvergenceExact

-- BCH 2026 source-faithfulness case study: finite exact no-gos, typed roots,
-- and an explicitly unpaid SCI/DPRM proof-debt interface.
import DASHI.Foundations.AutoformalisationBCH2026Exact
import DASHI.Foundations.AutoformalisationBCH2026SCIInterface
import DASHI.Foundations.AutoformalisationBCH2026Sources
