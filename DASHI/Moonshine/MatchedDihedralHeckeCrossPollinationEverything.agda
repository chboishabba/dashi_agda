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
-- The indexed lift places these quotients at their actual natural levels
-- p=2*j+1, so non-Ogg odd controls such as 9 and 15 inhabit the same operator
-- family.  Existing quotient-Hecke descent then derives the observable
-- commuting square from correspondence congruence.
--
-- The remaining mathematical producer is the actual level-dependent fine
-- weight/Brandt correspondence plus its arithmetic identification, not generic
-- quotient or indexing algebra.
------------------------------------------------------------------------

import DASHI.Foundations.MatchedDihedralSO3RestrictionExact
import DASHI.Moonshine.HeckeCorrespondenceQuotientDescentExact
import DASHI.Moonshine.IndexedLevelHeckeQuotientDescentExact
import DASHI.Moonshine.MatchedDihedralWeightHeckeQuotientExact
import DASHI.Moonshine.MatchedDihedralIndexedLevelHeckeQuotientExact
import DASHI.Moonshine.MatchedDihedralWeightHeckeRegression
import Ontology.Hecke.CorrespondenceRepresentation
import Ontology.Hecke.LevelCorrespondenceRepresentation
import Ontology.Hecke.IndexedLevelCorrespondenceRepresentation
import Ontology.Hecke.QuotientRepresentation
