module DASHI.Base369Monster3BCornerTritSquareEverything where

-- Extend the existing Base369/Monster focused aggregate with the Round-12
-- geometric carrier tranche.  Keeping this as a focused root avoids rewriting
-- older aggregate history while making the new dependency surface explicit.

import DASHI.Base369Ternary27StratifiedFibreEverything

-- Literal 8-corner geometry of one 3x3x3 ternary cube.
import DASHI.Foundations.Base369Ternary27CornerEightExact

-- Replace anonymous 10x9 addresses by Completed10 x literal T^2.
import DASHI.Moonshine.Base369CompletedTenTritSquareMultiplicityBidiExact

-- Upgrade the pointed 729 decomposition from Fin8 to literal cube corners,
-- then replace both nine-state sheets by the same literal T^2 carrier.
import DASHI.Moonshine.Base369Pointed729CornerCubeBidiExact
import DASHI.Moonshine.Base369Pointed729CornerTritSquareBidiExact

-- Make 3^8 = 3^6 * 3^2 a two-sided coordinate-carrier theorem using the
-- existing Heisenberg X6 and Base369 TritSquare carriers.
import DASHI.Moonshine.Base369MonsterThreeLocalEightToSixPlusTwoCarrierBidiExact

-- Search frontier and focused validation.
import DASHI.Moonshine.Base369Monster3BRepresentationBidiSearchRound12Exact
import DASHI.Base369Monster3BCornerTritSquareValidation
