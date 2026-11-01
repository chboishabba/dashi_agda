module DASHI.Wikimedia.IbrahimMonster3BInertiaPhaseResolutionProducerSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Moonshine.Monster3BCentralCharacterInertiaExact as Inertia
import DASHI.Moonshine.Base369Monster3BMultiplicityInertiaTwelveSeventyEightBidiExact as Split

------------------------------------------------------------------------
-- PHASE-RESOLVED INERTIA PRODUCER
--
-- The new GAP producer restricts the source-backed paired-phase MN3B
-- constituents from N(3B)=3^(1+12).2.Suz.2 to the centralizer/inertia subgroup
-- C_G(z)=3^(1+12).2.Suz.  It then classifies inertia irreducibles by the chosen
-- central singleton class as zeta or zeta^2 and fails closed unless the zeta
-- multiplicity degrees are exactly 12 and 78.
--
-- Source presence is NOT execution payment.
------------------------------------------------------------------------

barracloughWilson : Attribution.AttributedSource
barracloughWilson = Attribution.mkDOISource
  "R. W. Barraclough; R. A. Wilson"
  "The Character Table of a Maximal Subgroup of the Monster"
  "LMS Journal of Computation and Mathematics 10, 161-175"
  "2007"
  "10.1112/S1461157000001352"
  "https://doi.org/10.1112/S1461157000001352"
  Attribution.academicArticleSource
  "primary normalizer character-table provenance; supports the paired-phase restriction context but does not constitute the local producer run"
  Attribution.publicAttribution

isaacs : Attribution.AttributedSource
isaacs = Attribution.mkNoDOISource
  "I. M. Isaacs"
  "Character Theory of Finite Groups"
  "Academic Press / Dover reprint"
  "1976 / 1994"
  "https://archive.org/details/charactertheoryo0000isaa"
  Attribution.academicBookSource
  "Clifford-theory provenance for restriction from a group to the inertia subgroup; no DOI asserted"
  Attribution.publicAttribution

ctbllib : Attribution.AttributedSource
ctbllib = Attribution.mkNoDOISource
  "Thomas Breuer and CTblLib contributors"
  "The GAP Character Table Library"
  "GAP package documentation"
  "current producer dependency"
  "https://www.gap-system.org/Packages/ctbllib.html"
  (Attribution.namedSourceKind "software documentation")
  "computational source for character tables and class fusions; package availability does not imply successful producer execution"
  Attribution.publicAttribution

barracloughWilsonAttribution = Snowball.canonicalSourceRoleSnowballReceipt barracloughWilson
isaacsAttribution = Snowball.canonicalSourceRoleSnowballReceipt isaacs
ctbllibAttribution = Snowball.canonicalSourceRoleSnowballReceipt ctbllib

record InertiaExternalCoordinates : Set where
  constructor inertia-external-coordinates
  field
    groupRepresentationQid : String
    representationCharacterQid : String
    finiteGroupQid : String
    groupRepresentationDewey : String
    finiteGroupDewey : String
    oeisCoordinate : String
    oeisProvidesPhaseResolution : Bool
open InertiaExternalCoordinates public

canonicalInertiaExternalCoordinates : InertiaExternalCoordinates
canonicalInertiaExternalCoordinates = inertia-external-coordinates
  "Q1055807" "Q600043" "Q1057968"
  "512.22" "512.23"
  "A005052 remains only the independent numerical coordinate 90=10*3^2"
  false

record PhaseResolutionProducerReceipt : Set where
  constructor phase-resolution-producer-receipt
  field
    producerPath : String
    fullNormalizerTable : String
    inertiaTableTarget : String
    centralClassMustSplitTwoSingletons : Bool
    uniqueFusionRequired : Bool
    pairedConstituentsRestricted : Bool
    centralCharacterClassifiesZetaVsZetaSquared : Bool
    phaseDegreesMustReconstructNormalizerDegree : Bool
    zetaDegreesMustBeDivisibleBy729 : Bool
    requiredMultiplicityDegrees : String
    producerSourceWritten : Bool
    producerExecutionObserved : Bool
    generatedReceiptImported : Bool
open PhaseResolutionProducerReceipt public

currentPhaseResolutionProducerReceipt : PhaseResolutionProducerReceipt
currentPhaseResolutionProducerReceipt = phase-resolution-producer-receipt
  "scripts/monster_3b_inertia_phase_resolution.g"
  "MN3B = 3^(1+12).2.Suz.2"
  "3^(1+12).2.Suz"
  true true true true true true
  "[12,78]"
  true false false

------------------------------------------------------------------------
-- Consumer alignment.
------------------------------------------------------------------------

inertiaBoundary : Inertia.CentralCharacterInertiaBoundary
inertiaBoundary = Inertia.canonicalCentralCharacterInertiaBoundary

multiplicityBoundary : Split.MultiplicityInertiaTwelveSeventyEightBoundary
multiplicityBoundary = Split.canonicalMultiplicityInertiaTwelveSeventyEightBoundary

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ProducerSourceCreatesRunReceipt : Set where
data PairDegreeCreatesPhaseOrientation : Set where
data TwelveSeventyEightCreatesSameActionIntertwiner : Set where

data CTblLibTableNameCreatesActualMonsterAction : Set where

producerSourceDoesNotCreateRun : ProducerSourceCreatesRunReceipt → ⊥
producerSourceDoesNotCreateRun ()

pairDegreeDoesNotCreatePhaseOrientation : PairDegreeCreatesPhaseOrientation → ⊥
pairDegreeDoesNotCreatePhaseOrientation ()

twelveSeventyEightDoesNotCreateIntertwiner : TwelveSeventyEightCreatesSameActionIntertwiner → ⊥
twelveSeventyEightDoesNotCreateIntertwiner ()

ctbllibNameDoesNotCreateActualAction : CTblLibTableNameCreatesActualMonsterAction → ⊥
ctbllibNameDoesNotCreateActualAction ()

record InertiaPhaseResolutionFrontier : Set where
  constructor inertia-phase-resolution-frontier
  field
    genericInertiaPreservationAlreadyProved : Bool
    normalizerPairedTwelveSeventyEightProducerAlreadyWritten : Bool
    phaseResolutionProducerNowWritten : Bool
    producerExecutionPaid : Bool
    chosenZetaSectorSameObjectPaid : Bool
    actualMultiplicityInertiaActionPaid : Bool
    actualTwelveSeventyEightSameActionSplitPaid : Bool
    nextResidual : String
open InertiaPhaseResolutionFrontier public

currentInertiaPhaseResolutionFrontier : InertiaPhaseResolutionFrontier
currentInertiaPhaseResolutionFrontier = inertia-phase-resolution-frontier
  true true true false false false false
  "execute the fail-closed inertia producer. If CTblLib supplies the inertia table/fusion and the run returns phase-resolved [12,78], content-address the JSON and generated Agda receipt. Then weld the chosen singleton central class to the actual z in the AtlasRep group before constructing ActualMonster3BPhaseResolvedSector; only after that attach the same inertia action to Fin 90 and invoke the existing 12+78 recognition compiler."
