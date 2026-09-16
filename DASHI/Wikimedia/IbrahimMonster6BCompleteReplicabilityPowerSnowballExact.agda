module DASHI.Wikimedia.IbrahimMonster6BCompleteReplicabilityPowerSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.IbrahimMonster3BOEIS6BPowerNormalizationBridgeExact as Power
import DASHI.Wikimedia.IbrahimMonster236BMcKayThompsonNormalizationInvariantOEISExact as Normalization

------------------------------------------------------------------------
-- MONSTER 6B COMPLETE REPLICABILITY / POWER-MAP SNOWBALL
--
-- The important upgrade over coefficient matching is that classical Monster
-- McKay-Thompson functions are completely replicable.  Replicates are tied to
-- Adams operations, hence to powers of the Monster element.  Combined with the
-- independently paid ATLAS class-power surface 6B^2 -> 3B and 6B^3 -> 2B,
-- this relates the whole normalized 6B series to the normalized 3B and 2B
-- replicate targets.
--
-- This remains a class-function/modular-function statement.  It does not by
-- itself identify a literal repo VOA action, a selected basis, or the N(3B)
-- multiplicity-space representation.
------------------------------------------------------------------------

fordMcKayNorton : Attribution.AttributedSource
fordMcKayNorton = Attribution.mkDOISource
  "David Ford; John McKay; Simon P. Norton"
  "More on replicable functions"
  "Communications in Algebra 22(13), 5175-5193"
  "1994"
  "10.1080/00927879408825127"
  "https://doi.org/10.1080/00927879408825127"
  Attribution.academicArticleSource
  "primary replicability source; pays the replicable-function formalism and Monster-class replication tables, not a DASHI same-object VOA action"
  Attribution.publicAttribution

fordMcKayNortonAttribution = Snowball.canonicalSourceRoleSnowballReceipt fordMcKayNorton

ganter : Attribution.AttributedSource
ganter = Attribution.mkDOISource
  "Nora Ganter"
  "Hecke operators in equivariant elliptic cohomology and generalized Moonshine"
  "Groups and Symmetries, CRM Proceedings and Lecture Notes 47, 173-209"
  "2009"
  "10.1090/crmp/047/12"
  "https://doi.org/10.1090/crmp/047/12"
  Attribution.academicArticleSource
  "source for the Adams-operation/power-operation formulation of McKay-Thompson replicability; not authority for Monster 3B multiplicity-space identification"
  Attribution.publicAttribution

ganterAttribution = Snowball.canonicalSourceRoleSnowballReceipt ganter

ganterArxiv : String
ganterArxiv = "arXiv:0706.2898"

------------------------------------------------------------------------
-- Exact normalized OEIS manifestations used as sequence coordinates.
------------------------------------------------------------------------

record NormalizedMcKayThompsonCoordinate : Set where
  constructor normalized-mckay-thompson-coordinate
  field
    monsterClass : String
    oeisId : String
    leadingTerm : String
    qOneCoefficient : Nat
    qTwoCoefficient : String
open NormalizedMcKayThompsonCoordinate public

sixBNormalizedCoordinate : NormalizedMcKayThompsonCoordinate
sixBNormalizedCoordinate = normalized-mckay-thompson-coordinate
  "6B" "A007255" "q^-1 with q^0=0" 78 "364"

threeBNormalizedCoordinate : NormalizedMcKayThompsonCoordinate
threeBNormalizedCoordinate = normalized-mckay-thompson-coordinate
  "3B" "A007244" "q^-1 with q^0=0" 54 "-76"

twoBNormalizedCoordinate : NormalizedMcKayThompsonCoordinate
twoBNormalizedCoordinate = normalized-mckay-thompson-coordinate
  "2B" "A007246" "q^-1 with q^0=0" 276 "-2048"

------------------------------------------------------------------------
-- Whole-series replicate targets.
------------------------------------------------------------------------

record Monster6BReplicabilityPowerReceipt : Set where
  constructor monster-6b-replicability-power-receipt
  field
    sourceFunction : NormalizedMcKayThompsonCoordinate
    secondReplicateTarget : NormalizedMcKayThompsonCoordinate
    thirdReplicateTarget : NormalizedMcKayThompsonCoordinate
    sourceClassPowerBoundary : Power.Monster6BPowerNormalizationFrontier
    normalizationBoundary : Normalization.NormalizationInvariantOEISFrontier
    completeReplicabilityPaidBySource : Bool
    adamsOperationFormulationPaidBySource : Bool
    secondReplicateIsThreeB : Bool
    thirdReplicateIsTwoB : Bool
    replicabilityExtendsPastWeightTwoTrace : Bool
    literalVOASameObjectPaid : Bool
    n3BMultiplicityIntertwinerPaid : Bool
open Monster6BReplicabilityPowerReceipt public

canonicalMonster6BReplicabilityPowerReceipt : Monster6BReplicabilityPowerReceipt
canonicalMonster6BReplicabilityPowerReceipt = monster-6b-replicability-power-receipt
  sixBNormalizedCoordinate
  threeBNormalizedCoordinate
  twoBNormalizedCoordinate
  Power.currentMonster6BPowerNormalizationFrontier
  Normalization.currentNormalizationInvariantOEISFrontier
  true true true true true false false

------------------------------------------------------------------------
-- WrongType / non-promotion firewalls.
------------------------------------------------------------------------

data ReplicabilityCreatesLiteralVOASameObject : Set where
data ReplicateTargetCreatesMultiplicityIntertwiner : Set where
data OEISSeriesIdentityCreatesATLASPowerMap : Set where
data QOneTraceCreatesCompleteReplicability : Set where

replicabilityDoesNotCreateLiteralVOASameObject :
  ReplicabilityCreatesLiteralVOASameObject → ⊥
replicabilityDoesNotCreateLiteralVOASameObject ()

replicateTargetDoesNotCreateMultiplicityIntertwiner :
  ReplicateTargetCreatesMultiplicityIntertwiner → ⊥
replicateTargetDoesNotCreateMultiplicityIntertwiner ()

oeisSeriesIdentityDoesNotCreateATLASPowerMap :
  OEISSeriesIdentityCreatesATLASPowerMap → ⊥
oeisSeriesIdentityDoesNotCreateATLASPowerMap ()

qOneTraceDoesNotCreateCompleteReplicability :
  QOneTraceCreatesCompleteReplicability → ⊥
qOneTraceDoesNotCreateCompleteReplicability ()

------------------------------------------------------------------------
-- Pareto frontier.
------------------------------------------------------------------------

record Monster6BReplicabilityFrontier : Set where
  constructor monster-6b-replicability-frontier
  field
    normalized6BOEISLocated : Bool
    normalized3BOEISLocated : Bool
    normalized2BOEISLocated : Bool
    sixBSquareToThreeBClassPowerPaidUpstream : Bool
    sixBCubeToTwoBClassPowerPaidUpstream : Bool
    completeReplicabilitySourcePaid : Bool
    secondReplicateThreeBPaidAtClassFunctionLevel : Bool
    thirdReplicateTwoBPaidAtClassFunctionLevel : Bool
    higherPositiveDegreeRelationAvailableInPrinciple : Bool
    literalSelected6BVOAActionWeldPaid : Bool
    n3BMultiplicitySpaceWeldPaid : Bool
    nextResidual : String
open Monster6BReplicabilityFrontier public

currentMonster6BReplicabilityFrontier : Monster6BReplicabilityFrontier
currentMonster6BReplicabilityFrontier = monster-6b-replicability-frontier
  true true true true true true true true true false false
  "use complete replicability as the theorem-bearing whole-series relation behind the 6B -> 3B and 6B -> 2B power family, rather than matching isolated OEIS coefficients. The next same-object leaf is to attach one literal selected Monster 6B element to the graded VOA action and prove its square/cube are the already selected 3B/2B actions; only then can the replicate identities be promoted to same-action graded-trace receipts. No OEIS or replicability statement alone identifies the N(3B) 12+78 multiplicity representation."
