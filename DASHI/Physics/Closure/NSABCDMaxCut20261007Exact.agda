module DASHI.Physics.Closure.NSABCDMaxCut20261007Exact where

------------------------------------------------------------------------
-- NAVIER--STOKES A/B/C/D / AUTHORITATIVE MAX-CUT / 2026-10-07
--
-- A and B remain independent internal theorem-development programmes.
-- C and D are released-proof source-audit/publication lanes: their official
-- coordinate alignment is already closed and an independent DASHI Agda
-- reconstruction is not a prerequisite for that audit.
--
-- A retains the public A1 -> A2 -> A3 architecture but exposes the actual
-- physical subleaves.  B imports the post-#1039 pure-analysis board.  C/D are
-- frozen against accidental reclassification as internal theorem-discovery.
--
-- Current-head source freshness is also explicit: the OpenAI release advanced
-- beyond the originally pinned comparator commit, but the C/D comparator
-- theorem statements stayed stable, so the official-coordinate audit does not
-- reopen merely because the proof implementation changed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSClayFacingAPureAnalysisFrontier20261007Exact as A
import DASHI.Physics.Closure.NSClayFacingBPureAnalysisFrontier20261005Exact as B
import DASHI.Physics.Closure.NSClayFacingCDReleasedAuditFrontier20261007Exact as CD

data ABCDLane : Set where
  laneA laneB laneC laneD : ABCDLane

data LaneMode : Set where
  internalTheoremDevelopment : LaneMode
  releasedProofAudit : LaneMode

laneMode : ABCDLane → LaneMode
laneMode laneA = internalTheoremDevelopment
laneMode laneB = internalTheoremDevelopment
laneMode laneC = releasedProofAudit
laneMode laneD = releasedProofAudit

------------------------------------------------------------------------
-- A: internal whole-space positive route.
------------------------------------------------------------------------

aCurrentHighestInformationLeaf : A.APureLeaf
aCurrentHighestInformationLeaf = A.currentHighestInformationALeaf

aCompilerStackClosed : Bool
aCompilerStackClosed = A.aCompilerStackClosed

aInternalFrontierClosed : Bool
aInternalFrontierClosed = A.aInternalFrontierClosed

------------------------------------------------------------------------
-- B: internal periodic positive route.
------------------------------------------------------------------------

bCurrentHighestInformationLeaf : B.PureBAnalyticLeaf
bCurrentHighestInformationLeaf = B.currentHighestInformationLeaf

bRepresentationProgrammeFrozen : Bool
bRepresentationProgrammeFrozen = true

bPureAnalysisFrontierClosed : Bool
bPureAnalysisFrontierClosed = B.pureAnalysisFrontierClosed

bR823ShouldReopen : Bool
bR823ShouldReopen = B.r823ShouldReopen

------------------------------------------------------------------------
-- C/D: released source/formal-proof audit routes.
------------------------------------------------------------------------

cOfficialSourceAuditClosed : Bool
cOfficialSourceAuditClosed = CD.cOfficialCoordinateAuditClosed

dOfficialSourceAuditClosed : Bool
dOfficialSourceAuditClosed = CD.dOfficialCoordinateAuditClosed

cCurrentReleasedHeadStatementStable : Bool
cCurrentReleasedHeadStatementStable = CD.cCurrentReleasedHeadStatementStable

dCurrentReleasedHeadStatementStable : Bool
dCurrentReleasedHeadStatementStable = CD.dCurrentReleasedHeadStatementStable

cdCurrentHeadRequiresReopeningCoordinateAudit : Bool
cdCurrentHeadRequiresReopeningCoordinateAudit =
  CD.currentReleasedHeadRequiresReopeningCoordinateAudit

cdIndependentReconstructionGatesAudit : Bool
cdIndependentReconstructionGatesAudit = CD.independentDASHIReconstructionGatesAudit

cdInternalTheoremDiscoveryLane : Bool
cdInternalTheoremDiscoveryLane = CD.cDInternalTheoremDiscoveryLane

------------------------------------------------------------------------
-- Global routing / trust boundary.
------------------------------------------------------------------------

internalAClosed : Bool
internalAClosed = A.aInternalFrontierClosed

internalBClosed : Bool
internalBClosed = B.pureAnalysisFrontierClosed

releasedCSourceAuditClosed : Bool
releasedCSourceAuditClosed = CD.cOfficialCoordinateAuditClosed

releasedDSourceAuditClosed : Bool
releasedDSourceAuditClosed = CD.dOfficialCoordinateAuditClosed

clayPromotion : Bool
clayPromotion = false

bRepresentationProgrammeFrozenIsTrue :
  bRepresentationProgrammeFrozen ≡ true
bRepresentationProgrammeFrozenIsTrue = refl

cCurrentReleasedHeadStatementStableIsTrue :
  cCurrentReleasedHeadStatementStable ≡ true
cCurrentReleasedHeadStatementStableIsTrue = refl

dCurrentReleasedHeadStatementStableIsTrue :
  dCurrentReleasedHeadStatementStable ≡ true
dCurrentReleasedHeadStatementStableIsTrue = refl

cdCurrentHeadRequiresReopeningCoordinateAuditIsFalse :
  cdCurrentHeadRequiresReopeningCoordinateAudit ≡ false
cdCurrentHeadRequiresReopeningCoordinateAuditIsFalse = refl

cdIndependentReconstructionGatesAuditIsFalse :
  cdIndependentReconstructionGatesAudit ≡ false
cdIndependentReconstructionGatesAuditIsFalse = refl

cdInternalTheoremDiscoveryLaneIsFalse :
  cdInternalTheoremDiscoveryLane ≡ false
cdInternalTheoremDiscoveryLaneIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
