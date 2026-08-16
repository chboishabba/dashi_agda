module DASHI.Moonshine.MatchedDihedralHeckeCrossPollinationEverything where

------------------------------------------------------------------------
-- Focused aggregate for the representation -> quotient -> Hecke seam.
--
-- Existing matched-dihedral branching:
--   V_j | D_(2j+1) = epsilon_j + rho_1 + ... + rho_j.
--
-- New carrier theorem:
--   {0,+/-1,...,+/-j} / (+m ~ -m)
--      = {epsilon_j,rho_1,...,rho_j}.
--
-- Existing quotient-Hecke descent then derives the observable commuting square
-- from correspondence congruence.  The remaining mathematical producer is the
-- actual level-dependent fine weight/Brandt correspondence and its arithmetic
-- identification, not generic quotient algebra.
------------------------------------------------------------------------

import DASHI.Foundations.MatchedDihedralSO3RestrictionExact
import DASHI.Moonshine.HeckeCorrespondenceQuotientDescentExact
import DASHI.Moonshine.IndexedLevelHeckeQuotientDescentExact
import DASHI.Moonshine.MatchedDihedralWeightHeckeQuotientExact
import DASHI.Moonshine.MatchedDihedralWeightHeckeRegression
import Ontology.Hecke.CorrespondenceRepresentation
import Ontology.Hecke.LevelCorrespondenceRepresentation
import Ontology.Hecke.IndexedLevelCorrespondenceRepresentation
import Ontology.Hecke.QuotientRepresentation
