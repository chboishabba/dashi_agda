module DASHI.Moonshine.CM163BishopHecke41OriginalGlobalAcceptanceExact where

-- SINGLE ORIGINAL-CARRIER ACCEPTANCE TARGET. SOURCE-WRITTEN / UNRUN.
-- The concrete native gates are forced ONLY here and in their existing
-- finite acceptance owners. No residual, orbit cover, Euler equality,
-- symmetry or period is a parameter of this terminal module.
open import Agda.Builtin.Nat using (Nat)
import Real as R
import DASHI.Foundations.BishopConcreteElementaryCutsetExact as Concrete
import DASHI.Foundations.BishopChudnovskyNativePeriodProductExact as Period
import DASHI.Foundations.BishopChudnovskyNativeRealExact as Chud
import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
import DASHI.Foundations.BishopChudnovskyRawCoordinateWeldExact as Raw
import DASHI.Foundations.BishopChudnovskySignedCrossReflectionExact as Expanded
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Moonshine.CM163BishopHecke41ActualOrbitCoverExact as Cover
import DASHI.Moonshine.CM163BishopHecke41GlobalMatrixRigidityExact as Global
import DASHI.Moonshine.CM163BishopHecke41NativeFiniteAcceptanceExact as Finite
import DASHI.Moonshine.CM163BishopHecke41AllIntegerNodesAcceptanceExact as Nodes
import DASHI.Moonshine.CM163BishopHecke41OriginalRayClosureExact as Ray

module O = Cover.At Concrete.concreteCutset
module G = Global.At Concrete.concreteCutset
module F = Finite.At Concrete.concreteCutset
module E = Ray.At Concrete.concreteCutset

diagonalZero : ∀ p → C._≈C_ (E.H.R.d p) A.zeroC
diagonalZero = O.diagonalZero F.unitChecked F.diagonalChecked

sliceZero : ∀ p → C._≈C_ (E.H.R.s p) A.zeroC
sliceZero = O.sliceZero F.unitChecked F.sliceChecked

symmetry : E.M.TwoPointSymmetry
symmetry = G.twoPointSymmetry Nodes.unit Nodes.nodes Nodes.symmetry

module Closed = E.Original symmetry diagonalZero sliceZero

period : Period.NativePeriod
period = Closed.period

sameReal : R._≃_ Chud.chudnovskyReal Machin.bishopMachinPi
sameReal = Period.periodToSameReal period

allRaw : ∀ k → Raw.RawCross k
allRaw = Closed.allRaw

allExpanded : ∀ k → Expanded.ExpandedCross k
allExpanded = Period.periodToExpanded period
