module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound53LiteralFederbushCouplingValidation where

------------------------------------------------------------------------
-- ROUND 53 FOCUSED VALIDATION ROOT
--
-- This root does not promote any Clay endpoint.  It narrows the preferred G1
-- route to one source-convention dictionary:
--
--   printed equation-(0.11) J_j T_j
--     = J_+(Y_j) Ad_{exp Y_j}
--     = J_-(Y_j)
--     = literal source-radius inverse-dexp polynomial
--     -> col(J_-(Y_j)-I) < 1/4
--     -> normalized 4/3 inverse.
--
-- The finite/rational transport after the literal equality is now theorem
-- consumption.  What remains physical is the sign/trivialization identity and
-- the actual Bishop coefficient realization at |Y| <= 1/12.
--
-- On the RG side this root retains the source-oriented finite history:
-- beta split -> beta >= 0 -> terminal inverse threshold -> small coupling.
-- The inverse-square rational order dictionary and the actual finite-lattice
-- beta estimates stay visible as separate leaves.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound52SourceRGFederbushValidation as R52
import DASHI.Physics.YangMills.BalabanCMP109LiteralFederbushCancellationDictionaryExact as Literal
import DASHI.Physics.YangMills.BalabanCMP109FederbushDexpTransportCancellationExact as Dexp
import DASHI.Physics.YangMills.BalabanCMP109PrincipalLogSourceRadiusDefectExact as Source
import DASHI.Physics.YangMills.Balaban1989BetaSplitTerminalHistoryExact as BetaTerminal
import DASHI.Physics.YangMills.Balaban1989TerminalInverseThresholdHistoryExact as Terminal

literalFederbushCancellationDictionaryLevel =
  Literal.cmp109LiteralFederbushCancellationDictionaryLevel

literalFederbushSourceRadiusDefectTransportLevel =
  Literal.cmp109LiteralFederbushSourceRadiusDefectTransportLevel

literalFederbushConventionIdentificationLevel =
  Literal.cmp109LiteralFederbushConventionIdentificationLevel

reducedDexpTransportCancellationLevel =
  Dexp.cmp109FederbushDexpTransportCancellationLevel

physicalDexpTransportIdentificationLevel =
  Dexp.cmp109FederbushPhysicalDexpTransportIdentificationLevel

sourceRadiusMatrixQuarterLevel =
  Source.cmp109PrincipalLogSourceRadiusQuarterLevel

sourceRadiusBishopCoefficientLevel =
  Source.cmp109PrincipalLogSourceRadiusBishopCoefficientLevel

betaSplitTerminalHistoryLevel =
  BetaTerminal.balabanBetaSplitTerminalHistoryLevel

terminalThresholdPropagationLevel =
  Terminal.balabanTerminalInverseThresholdPropagationLevel

terminalThresholdSmallCouplingLevel =
  Terminal.balabanTerminalThresholdToSmallCouplingHistoryLevel

rationalInverseSquareOrderDictionaryLevel =
  Terminal.balabanRationalInverseSquareOrderDictionaryLevel
