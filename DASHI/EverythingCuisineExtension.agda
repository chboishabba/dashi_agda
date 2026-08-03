module DASHI.EverythingCuisineExtension where

------------------------------------------------------------------------
-- Lightweight repository-wide compatibility bridge.
--
-- Importing this module checks that the focused cuisine aggregate can coexist
-- with the repository aggregate without editing the very large generated-style
-- DASHI.Everything import list in this tranche.
------------------------------------------------------------------------

import DASHI.Everything
import DASHI.Culture.Cuisine.Everything
