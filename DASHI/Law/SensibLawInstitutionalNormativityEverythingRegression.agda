module DASHI.Law.SensibLawInstitutionalNormativityEverythingRegression where

open import DASHI.Core.Prelude

import DASHI.Law.SensibLawInstitutionalNormativityEverything

-- Importing the aggregate must resolve every tranche dependency while keeping
-- their namespaces separate.  Missing/renamed owners fail this regression at
-- module loading time.
institutionalNormativityAggregateLoads : ⊤
institutionalNormativityAggregateLoads = tt
