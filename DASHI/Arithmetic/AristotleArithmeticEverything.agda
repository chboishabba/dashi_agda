module DASHI.Arithmetic.AristotleArithmeticEverything where

------------------------------------------------------------------------
-- Aggregate surface for the direct arithmetic content imported from the
-- Aristotle development.  These are theorem-producing finite/arithmetic
-- modules rather than receipt-only bridges.
--
-- The source/parity manifest is imported first so this aggregate remains
-- explicitly tied to the pinned upstream mathematics snapshot rather than
-- silently treating nearby DASHI theorems as source parity.
------------------------------------------------------------------------

import DASHI.Interop.AristotleMathSourceParityExact
import DASHI.Arithmetic.DecimalDigitalRootNonaryExact
import DASHI.Arithmetic.FibonacciNonaryPeriodExact
import DASHI.Arithmetic.PrimeModSixSieveExact
import DASHI.Arithmetic.SixWheelSieveCountExact
import DASHI.Arithmetic.SixWheelCRTExact
import DASHI.Arithmetic.FinitePrimeProductSieveExact
