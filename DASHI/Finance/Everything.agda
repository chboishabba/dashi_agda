module DASHI.Finance.Everything where

import DASHI.Finance.TemporalMarketFibreExact
import DASHI.Finance.PointInTimeUniverseFibreExact
import DASHI.Finance.DeepStatArbFibrePipelineExact
import DASHI.Finance.MarketBraidCrossPollinationExact
import DASHI.Finance.UniverseLeakageResidualDependencyExact
import DASHI.Finance.DashiTradeFibreBridgeExact
import DASHI.Finance.TradeRealizationSharpeAuthorityExact

-- Canonical trading-control semantics. Earlier BAN/action experiments remain
-- in the branch as historical development artifacts but are deliberately not
-- imported by this aggregate.
import DASHI.Finance.TradingAdmissibleOptionConeSupersessionExact

-- Stable candidate transition first; exposure/turnover/size are observations
-- of that transition. Admissibility requires the whole state-indexed
-- precondition fabric plus an irreducible joint-compatibility receipt.
import DASHI.Finance.TradingJointPreconditionFabricExact

-- Published NASDAQ/LOBSTER tape states exercise the same fabric without
-- manufacturing factor, portfolio or authority evidence absent from the tape.
import DASHI.Finance.RealTapeJointPreconditionSanityExact
