module DASHI.Base369Ternary27StratifiedFibreEverythingRound16 where

import DASHI.Base369Ternary27StratifiedFibreEverythingRound15

-- Correct the central-fixed phase frontier: the nontrivial phases carry the
-- 729-dimensional Stone-von-Neumann type; the fixed phase factors through the
-- abelian extraspecial quotient E/Z(E)=F3^12 and requires its own character /
-- inertia-orbit decomposition.
import DASHI.Moonshine.Monster3BFixedPhaseAbelianQuotientCorrectionBidiExact

-- Global exponent refactor:
--   10*3^9 = 3*(10*3^2)*3^6 = 3*90*729 = 196830,
-- with the outer 3 certified at character level by the C3 regular bulk.
import DASHI.Moonshine.Base369Monster3BGlobalNineToOnePlusTwoPlusSixBidiExact

-- Once an actual 12+78 multiplicity split is supplied, compile it onto the
-- already-generated Completed10 x T^2 coordinates of the same Fin90 object.
import DASHI.Moonshine.Base369Monster3BMultiplicityProductVsTwelveSeventyEightCompilerExact

import DASHI.Moonshine.Base369Monster3BRepresentationBidiSearchRound16Exact
