module DASHI.Governance.LombardiBCCIHistoricalFixtureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Governance.EvidenceGradedGenealogyCore as Genealogy
import DASHI.Governance.MontefioreRothschildAustralianGoldSourceAtlasExact as Sources
import DASHI.Governance.LombardiNarrativeStructureAdapterExact as Lombardi

data BCCINode : Set where
  bcci : BCCINode
  icic : BCCINode
  firstAmerican : BCCINode
  firstAmericanHolding : BCCINode
  nomineeShareholders : BCCINode
  senateInvestigation : BCCINode
  lombardiArtwork : BCCINode

data BCCIRelation : Set where
  nomineeFinancing : BCCIRelation
  concealedControl : BCCIRelation
  investigativeFinding : BCCIRelation
  artisticRepresentation : BCCIRelation

record BCCIEdge : Set where
  constructor bcci-edge
  field
    source target : BCCINode
    relation : BCCIRelation
    grade : Genealogy.EvidenceGrade
    sourceIdentity : Sources.SourceIdentity
    boundedFinding : String
    historicalReceiptPaid : Bool
open BCCIEdge public

icicNomineeFinancing : BCCIEdge
icicNomineeFinancing = bcci-edge icic nomineeShareholders nomineeFinancing Genealogy.gradeA
  Sources.senateBCCIAffair
  "The Senate BCCI investigation documents ICIC-related nominee/financing arrangements at the bounded scope stated by the report."
  true

bcciFirstAmericanControl : BCCIEdge
bcciFirstAmericanControl = bcci-edge bcci firstAmerican concealedControl Genealogy.gradeA
  Sources.senateBCCIAffair
  "The Senate investigation reports concealed BCCI control in the First American structure; this is an investigative historical receipt independent of Lombardi's artwork."
  true

lombardiBCCIRepresentation : BCCIEdge
lombardiBCCIRepresentation = bcci-edge lombardiArtwork bcci artisticRepresentation Genealogy.gradeE
  Sources.whitneyLombardiBCCI
  "Whitney catalogue authority pays the existence and narrative-structure character of Lombardi's BCCI artwork, not the underlying banking facts."
  false

data ArtworkCreatesBCCIHistoricalReceipt : Set where
data SharedNarrativeAdapterCreatesAustralianBCCIHistoricalEdge : Set where

artworkDoesNotCreateBCCIHistoricalReceipt : ArtworkCreatesBCCIHistoricalReceipt → ⊥
artworkDoesNotCreateBCCIHistoricalReceipt ()

sharedNarrativeAdapterDoesNotCreateAustralianBCCIHistoricalEdge :
  SharedNarrativeAdapterCreatesAustralianBCCIHistoricalEdge → ⊥
sharedNarrativeAdapterDoesNotCreateAustralianBCCIHistoricalEdge ()

record BCCIFixtureBoundary : Set where
  constructor bcci-fixture-boundary
  field
    senateNomineeFindingPaid : Bool
    senateConcealedControlFindingPaid : Bool
    lombardiArtworkAuthorityPaid : Bool
    artworkAlonePaysHistoricalReceipt : Bool
    bcciAustralianColonialFinanceBridgePaid : Bool
open BCCIFixtureBoundary public

canonicalBCCIFixtureBoundary : BCCIFixtureBoundary
canonicalBCCIFixtureBoundary = bcci-fixture-boundary true true true false false
