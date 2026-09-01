module DASHI.Physics.Closure.NSTriadKNNestedPairIncidenceReuseRound341Exact where

------------------------------------------------------------------------
-- ROUND341 / BIDI REUSE: THE FINITE PAIR-INCIDENCE KERNEL CARRIER IS OLD
--
-- R330 already gives the literal nested incidence carrier
--
--   NestedIncidence = PhysicalTriadIncidence × PhysicalTriadIncidence
--
-- with fixed-output rows constructed by outer-fibre then inner-fibre
-- enumeration.  A repository-wide search finds that `NSPairIncidenceKernel`
-- already owns the exact generic construction needed to turn a finite list of
-- physical incidences into a rectangular weighted kernel:
--
--   pairKernelEntry(row,col)
--      = fold_{pair in pairs} pairContribution(pair,row,col).
--
-- It also owns the authority boundary `ConcreteBiotSavartKernelMatch`: a
-- concrete PDE kernel is not allowed to inherit the Schur certificate until it
-- agrees pointwise with that exact finite incidence fold.
--
-- Therefore the new F_s route should NOT introduce a second nested matrix
-- language.  Its physical kernel realization must use R330.NestedIncidence as
-- the Pair coordinate and discharge the old pointwise representation receipt.
--
-- This file pins that reuse and narrows the remaining producer to the actual
-- heat-weighted nested pair contribution / row / column semantics.  It does not
-- fabricate those semantics from the existence of R330's list.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Admission
import DASHI.Physics.Closure.NSPairIncidenceKernel as PairKernel
import DASHI.Physics.Closure.NSCompactGammaOffPacketPairIncidenceKernelBridge as OldPhysicalBridge
import DASHI.Physics.Closure.NSTriadKNLiteralNestedRowEnumerationRound330Exact as R330
import DASHI.Physics.Closure.NSTriadKNHeatWeightedKernelRepresentationReuseRound340Exact as R340

data NestedPairIncidenceLeaf : Set where
  pairCoordinateReuse : NestedPairIncidenceLeaf
  nestedPairContribution : NestedPairIncidenceLeaf
  rowCoordinateSemantics : NestedPairIncidenceLeaf
  columnCoordinateSemantics : NestedPairIncidenceLeaf
  concreteKernelPointwiseMatch : NestedPairIncidenceLeaf
  exactKernelAction : NestedPairIncidenceLeaf
  weightedSchurCertificate : NestedPairIncidenceLeaf

data LeafState : Set where closed open blocked : LeafState

leafState : NestedPairIncidenceLeaf → LeafState
leafState pairCoordinateReuse = closed
leafState nestedPairContribution = open
leafState rowCoordinateSemantics = open
leafState columnCoordinateSemantics = open
leafState concreteKernelPointwiseMatch = blocked
leafState exactKernelAction = blocked
leafState weightedSchurCertificate = blocked

pairIncidenceKernelInfrastructureDisposition : Admission.RouteDisposition
pairIncidenceKernelInfrastructureDisposition = Admission.redirectedReuse

oldCompactGammaPhysicalBridgeForFsDisposition : Admission.RouteDisposition
oldCompactGammaPhysicalBridgeForFsDisposition =
  Admission.rejected Admission.carrierMismatch

literalNestedPairContributionDisposition : Admission.RouteDisposition
literalNestedPairContributionDisposition = Admission.admitted

-- The Pair coordinate needed by the old exact finite kernel builder is already
-- literally the pair type produced by R330.  This is a type alias, not a new
-- representation.
NestedFsPair : Set
NestedFsPair = R330.NestedIncidence

round341NestedPairCoordinateIsR330NestedIncidence : Bool
round341NestedPairCoordinateIsR330NestedIncidence = true

round341ExactFinitePairKernelBuilderAlreadyOwned : Bool
round341ExactFinitePairKernelBuilderAlreadyOwned = true

round341PointwiseConcreteKernelMatchBoundaryAlreadyOwned : Bool
round341PointwiseConcreteKernelMatchBoundaryAlreadyOwned = true

round341OldPhysicalMajorizationPatternAlreadyOwned : Bool
round341OldPhysicalMajorizationPatternAlreadyOwned = true

round341R330EnumerationAloneDefinesFsPairContribution : Bool
round341R330EnumerationAloneDefinesFsPairContribution = false

round341NestedFsPairContributionClosed : Bool
round341NestedFsPairContributionClosed = false

round341NestedFsRowColumnSemanticsClosed : Bool
round341NestedFsRowColumnSemanticsClosed = false

round341ConcreteFsKernelPointwiseMatchClosed : Bool
round341ConcreteFsKernelPointwiseMatchClosed = false

round341ExactFsKernelActionClosed : Bool
round341ExactFsKernelActionClosed = false

round341WeightedFsSchurCertificateClosed : Bool
round341WeightedFsSchurCertificateClosed = false

round341PackageAClosed : Bool
round341PackageAClosed = false

round341ClayPromotion : Bool
round341ClayPromotion = false

round341NestedPairCoordinateIsR330NestedIncidenceIsTrue :
  round341NestedPairCoordinateIsR330NestedIncidence ≡ true
round341NestedPairCoordinateIsR330NestedIncidenceIsTrue = refl

round341R330EnumerationAloneDefinesFsPairContributionIsFalse :
  round341R330EnumerationAloneDefinesFsPairContribution ≡ false
round341R330EnumerationAloneDefinesFsPairContributionIsFalse = refl

round341PackageAClosedIsFalse : round341PackageAClosed ≡ false
round341PackageAClosedIsFalse = refl

round341ClayPromotionIsFalse : round341ClayPromotion ≡ false
round341ClayPromotionIsFalse = refl
