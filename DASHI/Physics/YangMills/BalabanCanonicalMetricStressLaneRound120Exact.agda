{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCanonicalMetricStressLaneRound120Exact where

------------------------------------------------------------------------
-- ROUND120: ONE SOURCE-EXACT METRIC-STRESS LANE FROM FINITE CMP116 TO CLAY
--
-- Round119 ties the Round106 canonical metric first variation to the exact
-- CMP119 insertion selected by one Round114 coordinate.  Round115 compiles that
-- same coordinate to the source telescope, Hilbert data, and literal Clay
-- stress derivative endpoint.  This file exposes the combined lane without
-- identifying carriers that genuinely live at different stages/topologies.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (_≤_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityFirstVariationRound105Exact as First
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanCanonicalMetricSelectedStressRound119Exact as R119
import DASHI.Physics.YangMills.BalabanLiteralStressCoordinateRound114Exact as R114
import DASHI.Physics.YangMills.BalabanLiteralStressCompletionRound115Exact as R115
import DASHI.Physics.YangMills.BalabanNormalizedStressInsertionRound116Exact as R116
import DASHI.Physics.YangMills.BalabanStressSameObjectProvenanceRound110Exact as R110
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanContinuumScaleLocalObservableCauchyExact as Scale
import DASHI.Physics.YangMills.BalabanTopDownSummableRGIncrementExact as Sum
import DASHI.Physics.YangMills.BalabanCMP119CompatibleLocalExpectationFlowExact as Source
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanMarkedSourceCoefficientEnergyHilbertCompilerExact as Hilbert
import DASHI.Physics.YangMills.BalabanMarkedSourceNuclearCompositeFieldExact as Marked
import DASHI.Physics.YangMills.BalabanMarkedSourceCompositeStressFieldExact as StressMarked
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record CanonicalMetricLiteralStressLane
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    {Y : Top.LiteralYangMillsConstruction C S}
    {group : Top.CompactSimpleGroup C}
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    (domain : Domain.CanonicalMetricSourceDomain Scale Volume activity)
    (representation : StressRep.CanonicalMetricStressRepresentation domain) : Set₁ where
  field
    coordinate : R114.LiteralStressCoordinate Y group
    metricSelectedStress :
      R119.CanonicalMetricSelectedStressWeld
        domain representation coordinate
open CanonicalMetricLiteralStressLane public

compiledCoordinate :
  ∀ {C S Y group Scale Volume activity domain representation} →
  CanonicalMetricLiteralStressLane
    {C = C} {S = S} {Y = Y} {group = group}
    {Scale = Scale} {Volume = Volume} {activity = activity}
    domain representation →
  R115.CompiledLiteralStressCompletion
    (coordinate
      {domain = domain} {representation = representation})
compiledCoordinate lane = R115.compileLiteralStressCoordinate (coordinate lane)

finiteMetricVariationIsSelectedCMP119Insertion :
  ∀ {C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    (lane : CanonicalMetricLiteralStressLane
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation) →
  ∀ background perturbation →
  Domain.AdmissibleMetricPerturbation domain perturbation →
  let weld = metricSelectedStress lane
      insertion =
        R119.R118.normalizedInsertion
          (R119.asRound118CanonicalMetricWeld weld)
          background perturbation
  in
  R119.R118.readoutToRational (R119.asRound118CanonicalMetricWeld weld)
    (StressRep.firstVariationReadout representation
      (First.substitutedFirstVariation activity background
        (Domain.metricPerturbationToBackgroundTangent
          domain background perturbation)))
  ≡ R116.cmp119StressInsertionNumerator insertion
finiteMetricVariationIsSelectedCMP119Insertion lane =
  R119.canonicalMetricVariationIsExactSelectedCMP119StressInsertion
    (metricSelectedStress lane)

selectedStressCauchyModulus :
  ∀ {C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    (lane : CanonicalMetricLiteralStressLane
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation) →
  ∀ start count →
  let compiled = R115.compileLiteralStressCoordinate (coordinate lane)
      provenance = R115.provenance compiled
  in
  R109.stressDifference (R110.sourceCauchy provenance) start count
  ≤ Scale.coefficient
      (Sum.commonMajorant
        (Source.sourceCompatibleSameFamilyIncrement
          (R109.source (R110.sourceCauchy provenance))
          (R109.smallHistory (R110.sourceCauchy provenance))
          (R109.stressInsertion (R110.sourceCauchy provenance))))
      * (Geo.half * Geo.halfPower start)
selectedStressCauchyModulus lane =
  R115.compiledStressCauchyModulus (coordinate lane)

selectedStressFiniteHilbertData :
  ∀ {C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    (lane : CanonicalMetricLiteralStressLane
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation) →
  Nat → Hilbert.FiniteMarkedSourceHilbertData
selectedStressFiniteHilbertData lane =
  R115.compiledStressFiniteHilbertData (coordinate lane)

selectedStressCompletionIsLiteralClayStressDerivative :
  ∀ {C S Y group Scale Volume activity}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    (lane : CanonicalMetricLiteralStressLane
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation) →
  let selected = coordinate lane
      completion = R114.asMarkedCompletion selected (R114.coordinate selected)
      sources = R109.completedSources completion
      stressData = StressMarked.stressData sources
  in
  R114.cmp119CompletedResponse selected
  ≡ Marked.sourceDerivative stressData (Top.stressTensor Y group)
selectedStressCompletionIsLiteralClayStressDerivative lane =
  R115.compiledStressCompletionIsLiteralClayStressDerivative (coordinate lane)

canonicalMetricLiteralStressLaneCompilerLevel : ProofLevel
canonicalMetricLiteralStressLaneCompilerLevel = machineChecked

-- One physical source-exact instantiation now feeds the whole finite-to-continuum
-- stress lane.  No independent Cauchy, Hilbert, or endpoint theorem remains.
literalCanonicalMetricStressLaneInstantiationLevel : ProofLevel
literalCanonicalMetricStressLaneInstantiationLevel = conditional
