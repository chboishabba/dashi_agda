module DASHI.Biology.Agriculture.AustralianAcaciaPioneerDisturbanceTrajectoryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Environment.LESResearchCrossPollinationExact as LES

andersen1993DOI : String
andersen1993DOI = "10.1111/j.1526-100X.1993.tb00022.x"

bradyNoske2010DOI : String
bradyNoske2010DOI = "10.1111/j.1526-100X.2008.00511.x"

andersen1993 : Attribution.AttributedSource
andersen1993 = Attribution.mkDOISource
  "Alan N. Andersen"
  "Ants as Indicators of Restoration Success at a Uranium Mine in Tropical Australia"
  "Restoration Ecology 1:156-167"
  "1993" andersen1993DOI "https://doi.org/10.1111/j.1526-100X.1993.tb00022.x"
  Attribution.academicArticleSource
  "Tropical Australian mine-rehabilitation chronosequence. Fast-growing Acacia dominated many revegetated sites; ant succession could stall while richness/composition remained unlike controls. A prescribed-burn site that broke Acacia dominance showed broader plant establishment. Retained as disturbance-regime/pioneer-release evidence, not a universal prescription to burn or suppress Acacia."
  Attribution.publicAttribution

bradyNoske2010 : Attribution.AttributedSource
bradyNoske2010 = Attribution.mkDOISource
  "Christopher J. Brady; Richard A. Noske"
  "Succession in Bird and Plant Communities over a 24-Year Chronosequence of Mine Rehabilitation in the Australian Monsoon Tropics"
  "Restoration Ecology 18:855-864"
  "2010" bradyNoske2010DOI "https://doi.org/10.1111/j.1526-100X.2008.00511.x"
  Attribution.academicArticleSource
  "Gove bauxite-mine rehabilitation chronosequence spanning 2-24 years. Short-lived Acacia dominated early stages and eucalypts later; bird richness/abundance approached off-mine values in the oldest rehabilitation while community composition remained distinct. Fire exclusion is retained as a candidate trajectory coordinate."
  Attribution.publicAttribution

data PioneerTrajectoryWorld : Set where
  earlyAcaciaLaterRelease : PioneerTrajectoryWorld
  earlyAcaciaSuccessionStalled : PioneerTrajectoryWorld

data PioneerTrajectoryTask : Set where
  longTermCommunityTrajectoryTask : PioneerTrajectoryTask

data EarlyPioneerToken : Set where
  earlyAcaciaEstablished : EarlyPioneerToken

earlyPioneerProjection : PioneerTrajectoryWorld → EarlyPioneerToken
earlyPioneerProjection _ = earlyAcaciaEstablished

longTermCommunityRecovery : PioneerTrajectoryTask → PioneerTrajectoryWorld → Bool
longTermCommunityRecovery longTermCommunityTrajectoryTask earlyAcaciaLaterRelease = true
longTermCommunityRecovery longTermCommunityTrajectoryTask earlyAcaciaSuccessionStalled = false

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

earlyPioneerNotTrajectorySufficient :
  LES.TaskFactorisation earlyPioneerProjection longTermCommunityRecovery → ⊥
earlyPioneerNotTrajectorySufficient factor =
  trueNotFalse
    (LES.sameRepresentationSameTaskOutput
      factor longTermCommunityTrajectoryTask
      {earlyAcaciaLaterRelease} {earlyAcaciaSuccessionStalled} refl)

record PioneerTrajectoryBoundary : Set where
  constructor pioneer-trajectory-boundary
  field
    pioneerEstablishmentImpliesSuccessfulSuccessionalRelease : Bool
    acaciaDominanceImpliesLaterCommunityRecovery : Bool
    referenceLikeRichnessImpliesReferenceLikeComposition : Bool
    disturbanceFireRegimeMustRemainIndexed : Bool
    proximityToColonisationSourcesMustRemainIndexed : Bool
    vegetationStructureAndFaunalCompositionRemainSeparate : Bool
    prescribedBurnObservationCreatesUniversalFirePrescription : Bool
    chronosequenceCreatesExactSingleSiteTrajectory : Bool
    pioneerRoleCreatesDeploymentAuthority : Bool
open PioneerTrajectoryBoundary public

canonicalPioneerTrajectoryBoundary : PioneerTrajectoryBoundary
canonicalPioneerTrajectoryBoundary = pioneer-trajectory-boundary
  false false false true true true false false false

attributionRule : String
attributionRule =
  "Andersen 1993 (DOI 10.1111/j.1526-100X.1993.tb00022.x) owns its Ranger uranium-mine ant/vegetation succession and prescribed-burn observations. Brady & Noske 2010 (DOI 10.1111/j.1526-100X.2008.00511.x) owns its Gove 24-year bird/woody-plant chronosequence observations. DASHI owns only the finite early-pioneer/long-term-trajectory TaskFactorisation collision and no-promotion boundary. Neither source establishes a universal fire regime, universal Acacia-removal rule, or exact longitudinal trajectory from chronosequence age alone."
