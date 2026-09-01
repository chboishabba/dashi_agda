{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119Round191Validation where

import DASHI.Physics.YangMills.BalabanCMP98RawUnitPathHomomorphismRound189Exact as R189
import DASHI.Physics.YangMills.BalabanCMP98ClayBoundarySupersessionRound190Exact as R190
import DASHI.Physics.YangMills.BalabanCMP98BidiWallRound191Exact as R191
import DASHI.Physics.YangMills.BalabanCMP98Path13PhysicalPeriodicRealizationRound192Exact as R192
import DASHI.Physics.YangMills.BalabanCMP98Path13Equation119SourceRound193Exact as R193

round189PathHomomorphism = R189.cmp98RawUnitPathHomomorphismRound189Level
round190BoundarySupersession = R190.cmp98ClayBoundarySupersessionRound190Level
round191WallAudit = R191.cmp98BidiWallAuditRound191Level

-- Historical Round191 source wall: arbitrary-period physical realization.
-- R192/R193 show that this stronger requirement is unnecessary on the literal
-- source-scale lane: Eq.(119) can be specialized at n=12 / L=13.
round191HistoricalGenericSourceWall =
  R191.literalArbitraryPeriodicSelectedBackgroundProducerRound191Level

round192Path13PhysicalRealization =
  R192.cmp98Path13PhysicalPeriodicRealizationRound192Level

round192Path13CarrierSameObject =
  R192.cmp98Path13PhysicalCarrierSameObjectRound192Level

round193Path13Equation119Source =
  R193.cmp98Path13Equation119SourceRound193Level

round193PhysicalRealizationDerived =
  R193.cmp98Path13RealizationDerivedRound193Level

-- Current source leaves after specialization.
round193OperatorSourceSemantics =
  R193.literalCMP98Path13OperatorSourceSemanticsRound193Level

round193SelectedBackgroundCutWeld =
  R193.literalCMP98Path13SelectedBackgroundCutWeldRound193Level

-- Terminal theorem-bearing wall remains unchanged by the source specialization.
round191TerminalWall = R191.literalTerminalClayCompositionTheoremRound191Level
