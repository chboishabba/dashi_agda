{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119Round191Validation where

import DASHI.Physics.YangMills.BalabanCMP98RawUnitPathHomomorphismRound189Exact as R189
import DASHI.Physics.YangMills.BalabanCMP98ClayBoundarySupersessionRound190Exact as R190
import DASHI.Physics.YangMills.BalabanCMP98BidiWallRound191Exact as R191
import DASHI.Physics.YangMills.BalabanCMP98Path13PhysicalPeriodicRealizationRound192Exact as R192
import DASHI.Physics.YangMills.BalabanCMP98Path13Equation119SourceRound193Exact as R193
import DASHI.Physics.YangMills.BalabanRootedCoarseAnchoredOrbitSectionRound194Exact as R194
import DASHI.Physics.YangMills.BalabanCMP109RootedEquation012OrbitSectionRound195Exact as R195

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

round193OperatorSourceSemantics =
  R193.literalCMP98Path13OperatorSourceSemanticsRound193Level

round193SelectedBackgroundCutWeld =
  R193.literalCMP98Path13SelectedBackgroundCutWeldRound193Level

-- Configuration-space cross-pollination.  R194 composes the actual rooted orbit
-- section with generic coarse-anchored block-average covariance; R195 then uses
-- the stronger source-exact CMP109 equation-(0.12) invariance theorem.
round194RootedCoarseAnchoredOrbitSection =
  R194.cmp98RootedCoarseAnchoredOrbitSectionRound194Level

round194RootedOrbitUniqueness =
  R194.cmp98RootedCoarseAnchoredOrbitUniquenessRound194Level

round195RootedEquation012OrbitSection =
  R195.cmp109RootedEquation012OrbitSectionRound195Level

round195RootedEquation012MapPreservation =
  R195.cmp109RootedEquation012MapPreservationRound195Level

-- Current nonlinear same-object leaves.  These are operation-identification
-- seams, not new gauge-section or block-average theorems.
round195GaugeActionPhysical =
  R195.literalCMP109Equation012GaugeActionPhysicalRound195Level

round195CoarseEndpointsAreRoot =
  R195.literalCMP109Equation012CoarseEndpointsAreRootRound195Level

round195IdentityIsPhysicalUnit =
  R195.literalCMP109Equation012IdentityIsPhysicalUnitRound195Level

-- Terminal theorem-bearing wall remains unchanged by the source/configuration
-- specialization.  Status-ledger booleans do not inhabit this theorem field.
round191TerminalWall = R191.literalTerminalClayCompositionTheoremRound191Level
