module DASHI.Moonshine.AristotleMathParityEverything where

------------------------------------------------------------------------
-- Direct theorem-producing Aristotle mathematics parity aggregate.
--
-- Source custody/parity accounting remains in
-- DASHI.Interop.AristotleMathSourceParityExact.  This aggregate imports the
-- mathematical realizations themselves and deliberately does not treat nearby
-- DASHI results as source parity unless the parity ledger names them.
------------------------------------------------------------------------

import DASHI.Interop.AristotleMathSourceParityExact
import DASHI.Arithmetic.AristotleArithmeticEverything
import DASHI.Moonshine.AristotleHeckeRecurrenceCoreExact
import DASHI.Moonshine.AristotleHeckeGeneralPrimePowerDecompositionExact
import DASHI.Moonshine.AristotleHeckeWordsSourceParityExact
import DASHI.Moonshine.AristotleDeltaWordT2T3FiniteParityExact
import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact
import DASHI.Moonshine.RamanujanTauHecke23Exact
import DASHI.Moonshine.Hecke23AntiparallelExact
import DASHI.Analysis.FiniteRealQSeriesReflectionExact
import DASHI.Moonshine.EisensteinDiscriminantWeight12Exact
