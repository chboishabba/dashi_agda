module DASHI.Physics.CondensedMatter.FlatBandTwistronicsFe5GeTe2CrossPollinationExact where

------------------------------------------------------------------------
-- FLAT-BAND CROSS-POLLINATION:
--   magic-angle / registration-engineered graphene
--   versus
--   interaction-driven Fe5GeTe2
--
-- Shared theorem shape:
--
--   distinct microscopic/effective states
--      -> same selected coarse observable
--      -> a later/refined consumer can distinguish them
--      -> the coarse observable alone is insufficient for that consumer.
--
-- Physical mechanisms remain explicitly distinct.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Moonshine.TwistronicsRelativeRegistrationComparatorExact as Twist
import DASHI.Moonshine.TwistronicsRegistrationControlFutureSplitExact as Control
import DASHI.Physics.CondensedMatter.FlatBandObservableFibreExact as Flat
import DASHI.Physics.CondensedMatter.GaoFe5GeTe2FlatBandChargeOrderSourceReplayExact as Fe
import DASHI.Physics.CondensedMatter.GaoFe5GeTe2FigureReplayExact as Figure
import DASHI.Physics.CondensedMatter.ThreeFoldBandFoldingExact as Fold

data FlatBandRoute : Set where
  magicAngleRegistrationRoute : FlatBandRoute
  interactionDrivenFe5GeTe2Route : FlatBandRoute

routesAreDistinct :
  magicAngleRegistrationRoute ≡ interactionDrivenFe5GeTe2Route -> ⊥
routesAreDistinct ()

record SharedFlatBandArchitecture : Set where
  constructor shared-flat-band-architecture
  field
    route : FlatBandRoute
    flatteningCreatesOrExposesCoarseFibre : Bool
    correlatedOrOrderedConsumerCanRequireRefinement : Bool
    mechanismIsImportedFromOtherRoute : Bool
    sameObjectIdentificationAcrossMaterials : Bool

open SharedFlatBandArchitecture public

magicAngleArchitecture : SharedFlatBandArchitecture
magicAngleArchitecture =
  shared-flat-band-architecture
    magicAngleRegistrationRoute
    true
    true
    false
    false

fe5gete2Architecture : SharedFlatBandArchitecture
fe5gete2Architecture =
  shared-flat-band-architecture
    interactionDrivenFe5GeTe2Route
    true
    true
    false
    false

record GrapheneFe5GeTe2CrossPollinationBoundary : Set where
  constructor graphene-fe5gete2-cross-pollination-boundary
  field
    bistritzerMacDonaldMagicAngleSourceRetained : Bool
    caoCorrelatedPhaseSourcesRetained : Bool
    huInSituRegistrationControlSourceRetained : Bool
    gaoFe5GeTe2PrimarySourceRetained : Bool
    jiangMagicAngleChargeOrderPrecedentRetained : Bool
    sharedObservableFibreTheoremShapeUsed : Bool
    sharedConsumerRefinementTheoremShapeUsed : Bool
    twistAngleIdentifiedWithFeInteractionStrength : Bool
    grapheneFlatBandIdentifiedWithFeFlatBandSameObject : Bool
    grapheneCorrelatedPhaseIdentifiedWithFeChargeOrder : Bool
    kondoLikeInterpretationTransferredToGraphene : Bool
    sqrt3R30OrderTransferredToGraphene : Bool

canonicalGrapheneFe5GeTe2CrossPollinationBoundary :
  GrapheneFe5GeTe2CrossPollinationBoundary
canonicalGrapheneFe5GeTe2CrossPollinationBoundary =
  graphene-fe5gete2-cross-pollination-boundary
    true true true true
    true
    true true
    false false false false false

------------------------------------------------------------------------
-- Existing 1.1-degree graphene machinery is consumed, not duplicated.
------------------------------------------------------------------------

existingMagicAngleSourceAtlas :
  Attribution.AttributedSourceAtlas
existingMagicAngleSourceAtlas =
  Twist.twistronicsSourceAtlas

existingInSituControlReceipt :
  Control.ExternalTwistControlReceipt
existingInSituControlReceipt =
  Control.canonicalExternalTwistControlReceipt

existingFe5GeTe2Replay :
  Fe.Fe5GeTe2SourceReplay
existingFe5GeTe2Replay =
  Fe.canonicalFe5GeTe2SourceReplay

existingFe5GeTe2FigureReplay :
  Figure.Fe5GeTe2FigureReplay
existingFe5GeTe2FigureReplay =
  Figure.canonicalFe5GeTe2FigureReplay

existingThreeFoldSurface :
  Fold.ThreeFoldPresentation (Fin 3) Fold.OneFoldedPoint
existingThreeFoldSurface =
  Fold.canonicalThreeFoldPresentation

------------------------------------------------------------------------
-- Generic capstone: if an exactly flat pair is split by a phase/order
-- observer, energy alone cannot be a sufficient code for that observer.
--
-- This theorem is mechanism-neutral and therefore reusable by either lane
-- only after that lane supplies its own witness.
------------------------------------------------------------------------

flatPairSplitByOrderRequiresMoreThanEnergy :
  {Momentum Energy Order : Set} ->
  (band : Flat.BandSystem Momentum Energy) ->
  (orderObserver : Momentum -> Order) ->
  Flat.FlatBandPhaseSplitWitness band orderObserver ->
  Flat.PhaseDescendsThroughEnergy band orderObserver ->
  ⊥
flatPairSplitByOrderRequiresMoreThanEnergy =
  Flat.flatBandPhaseSplitRefutesEnergyOnlyDescent

record WitnessStatusBoundary : Set where
  constructor witness-status-boundary
  field
    genericEnergyFibreObstructionProved : Bool
    grapheneExactFlatPairOrderSplitWitnessConstructedHere : Bool
    fe5gete2ExactFlatPairChargeOrderSplitWitnessConstructedHere : Bool
    sourceReportsAutomaticallyBecomeExactWitnesses : Bool

canonicalWitnessStatusBoundary : WitnessStatusBoundary
canonicalWitnessStatusBoundary =
  witness-status-boundary
    true
    false
    false
    false
