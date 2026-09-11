module DASHI.Wikimedia.IbrahimMonster3BPrimarySupplementKernelClass20SnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.IbrahimMonster3BDiagonalC3QuotientOrientationSnowballExact as Orientation

------------------------------------------------------------------------
-- PRIMARY SUPPLEMENT KERNEL COORDINATE
--
-- Barraclough--Wilson's published/author-hosted supplementary table package
-- contains the quotient maps from the main table
--
--   3^1+12:6.Suz.2
--
-- to both N(3B) and 6.Suz.2.  Reading the maps in their native main-table
-- ordering gives the exact historical coordinate:
--
--   main class 20 -> identity in N(3B)
--   main class 20 -> class 6 in 6.Suz.2.
--
-- This is an EXTERNAL TABLE COORDINATE, independently regression-checked by
-- scripts/check_monster_3b_suzuki_main_quotient_match.sh against the semantic
-- GAP recovery of the unique nonidentity size-two order-three quotient-kernel
-- class.  The coordinate does NOT by itself identify whether Bray--Wilson's
-- diagonal generator is t1*t2 or t1*t2^-1.
------------------------------------------------------------------------

barracloughWilsonPaper : Attribution.AttributedSource
barracloughWilsonPaper = Attribution.mkDOISource
  "R. W. Barraclough; R. A. Wilson"
  "The Character Table of a Maximal Subgroup of the Monster"
  "LMS Journal of Computation and Mathematics 10, 161-175"
  "2007"
  "10.1112/S1461157000001352"
  "https://doi.org/10.1112/S1461157000001352"
  Attribution.academicArticleSource
  "primary mathematical source for the main table, N(3B) table and quotient/fusion construction"
  Attribution.publicAttribution

barracloughWilsonSupplement : Attribution.AttributedSource
barracloughWilsonSupplement = Attribution.mkNoDOISource
  "R. W. Barraclough; R. A. Wilson"
  "N3BetcTables supplementary character tables and quotient maps"
  "author-hosted supplementary data attached to the 2007 character-table work"
  "2007"
  "https://www.rwb.me.uk/table/index.html"
  (Attribution.namedSourceKind "primary supplementary computational data")
  "primary external identity for qGtoN3B, qGto6s2 and the main-table class ordering; no separate DOI asserted for the supplement"
  Attribution.publicAttribution

paperAttribution = Snowball.canonicalSourceRoleSnowballReceipt barracloughWilsonPaper
supplementAttribution = Snowball.canonicalSourceRoleSnowballReceipt barracloughWilsonSupplement

paperDOI : String
paperDOI = "10.1112/S1461157000001352"

record PrimarySupplementKernelCoordinate : Set where
  constructor primary-supplement-kernel-coordinate
  field
    mainTableIdentity : String
    n3bTableIdentity : String
    outerTableIdentity : String
    nonidentityKernelClassPosition : Nat
    kernelClassN3BImage : Nat
    kernelClassOuterImage : Nat
    coordinateSourceRole : String
open PrimarySupplementKernelCoordinate public

canonicalPrimarySupplementKernelCoordinate : PrimarySupplementKernelCoordinate
canonicalPrimarySupplementKernelCoordinate = primary-supplement-kernel-coordinate
  "3^1+12:6.Suz.2"
  "3^1+12.2.Suz.2 / MN3B"
  "6.Suz.2"
  20
  1
  6
  "primary Barraclough-Wilson supplementary quotient-map coordinate"

------------------------------------------------------------------------
-- Acquisition mirror is transport only.
------------------------------------------------------------------------

record SupplementAcquisitionState : Set where
  constructor supplement-acquisition-state
  field
    primaryAuthorHostedIdentityLocated : Bool
    acquisitionMirrorLocated : Bool
    mirrorCreatesPrimaryAuthority : Bool
    mirrorCreatesDiagonalKernelName : Bool
open SupplementAcquisitionState public

canonicalSupplementAcquisitionState : SupplementAcquisitionState
canonicalSupplementAcquisitionState = supplement-acquisition-state
  true true false false

------------------------------------------------------------------------
-- QID / Dewey / OEIS remain typed navigation coordinates only.
------------------------------------------------------------------------

record KernelCoordinateExternalCoordinates : Set where
  constructor kernel-coordinate-external-coordinates
  field
    groupRepresentationQid : String
    representationCharacterQid : String
    finiteGroupQid : String
    groupRepresentationDewey : String
    finiteGroupDewey : String
    groupSpecificQid : String
    oeisCoordinate : String
    oeisHasKernelIdentityAuthority : Bool
open KernelCoordinateExternalCoordinates public

canonicalKernelCoordinateExternalCoordinates : KernelCoordinateExternalCoordinates
canonicalKernelCoordinateExternalCoordinates = kernel-coordinate-external-coordinates
  "Q1055807"
  "Q600043"
  "Q1057968"
  "512.22"
  "512.23"
  "unresolved rather than guessed for this exact main-table quotient object"
  "not applicable: class-20 quotient identity is character-table/group data, not an integer-sequence fact"
  false

------------------------------------------------------------------------
-- WrongType / non-promotion boundaries.
------------------------------------------------------------------------

data ClassTwentyCreatesDiagonalKernelName : Set where
data OuterClassSixCreatesDiagonalKernelName : Set where
data QuotientCoordinateCreatesZetaOrientation : Set where
data QidCreatesQuotientProof : Set where
data DeweyCreatesQuotientProof : Set where
data OeisCreatesQuotientProof : Set where

classTwentyDoesNotNameDiagonal : ClassTwentyCreatesDiagonalKernelName → ⊥
classTwentyDoesNotNameDiagonal ()

outerClassSixDoesNotNameDiagonal : OuterClassSixCreatesDiagonalKernelName → ⊥
outerClassSixDoesNotNameDiagonal ()

quotientCoordinateDoesNotOrientZeta : QuotientCoordinateCreatesZetaOrientation → ⊥
quotientCoordinateDoesNotOrientZeta ()

qidDoesNotCreateProof : QidCreatesQuotientProof → ⊥
qidDoesNotCreateProof ()

deweyDoesNotCreateProof : DeweyCreatesQuotientProof → ⊥
deweyDoesNotCreateProof ()

oeisDoesNotCreateProof : OeisCreatesQuotientProof → ⊥
oeisDoesNotCreateProof ()

------------------------------------------------------------------------
-- Exact frontier.
------------------------------------------------------------------------

record PrimarySupplementKernelFrontier : Set where
  constructor primary-supplement-kernel-frontier
  field
    paperDOIPaid : Bool
    primarySupplementIdentityPaid : Bool
    mainClassTwentyCoordinatePaid : Bool
    classTwentyMapsToN3BIdentityPaid : Bool
    classTwentyMapsToOuterClassSixPaid : Bool
    semanticGAPKernelSelectorWritten : Bool
    exactCoordinateRegressionWritten : Bool
    exactCoordinateRegressionExecuted : Bool
    classTwentyEqualsT1TimesT2Paid : Bool
    classTwentyEqualsT1TimesT2InversePaid : Bool
    invariantDiagonalKernelNamePaid : Bool
    nextResidual : String
open PrimarySupplementKernelFrontier public

currentPrimarySupplementKernelFrontier : PrimarySupplementKernelFrontier
currentPrimarySupplementKernelFrontier = primary-supplement-kernel-frontier
  true true true true true true true
  false false false false
  "execute the Suzuki/main quotient matcher and require its semantic kernel recovery to reproduce primary supplement main class 20 with outer image class 6. Then pay exactly one remaining invariant identity: crosswalk main class 20 to Bray-Wilson's explicit diagonal kernel <t1*t2> or <t1*t2^-1> using the published standard-generator word discriminator or an exact same-object class-coordinate derivation. Do not infer that name from class number 20, outer class 6, modular 12+/- labels, QID, Dewey, OEIS or ATLAS names."

orientationFrontier : Orientation.DiagonalOrientationFrontier
orientationFrontier = Orientation.currentDiagonalOrientationFrontier
