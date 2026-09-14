module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFRETObserverAxisExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseRateObserverAdequacyExact as Rate

------------------------------------------------------------------------
-- ADENYLATE-KINASE FRET OBSERVER-AXIS REFINEMENT
--
-- Li, Liu & Ji 2015 explicitly compare two single-molecule FRET experiments on
-- ligand-free E. coli AdK.  Henzler-Wildman et al. label Lys145/Ile52, a
-- LID--NMP axis, and report an open-state major population.  Hanson et al. label
-- Ala127/Ala194, a LID--CORE axis, and report a closed-state-favoured
-- interpretation.  The source itself points to the different labelling axes as
-- relevant to the different population readouts.
--
-- This owner does not decide which experiment is globally "right".  It pays a
-- narrower information theorem: erasing observer-axis identity is unsafe for a
-- population-interpretation query; retaining the axis repairs that collision.
------------------------------------------------------------------------

data FRETAxis : Set where
  lidNmpAxis : FRETAxis
  lidCoreAxis : FRETAxis

data FRETWorld : Set where
  henzlerWildmanWorld : FRETWorld
  hansonWorld : FRETWorld

data AxisErasedObservation : Set where
  sameProteinSameApoContext : AxisErasedObservation

data PopulationQuery : Set where
  proteinIdentityQuery : PopulationQuery
  dominantPopulationQuery : PopulationQuery

data PopulationAnswer : Set where
  sameAdKAnswer : PopulationAnswer
  openMajorAnswer : PopulationAnswer
  closedFavouredAnswer : PopulationAnswer

axisErasedProjection : FRETWorld → AxisErasedObservation
axisErasedProjection world = sameProteinSameApoContext

populationAnswer : PopulationQuery → FRETWorld → PopulationAnswer
populationAnswer proteinIdentityQuery world = sameAdKAnswer
populationAnswer dominantPopulationQuery henzlerWildmanWorld = openMajorAnswer
populationAnswer dominantPopulationQuery hansonWorld = closedFavouredAnswer

populationSemantics : Query.QuerySemantics FRETWorld PopulationQuery PopulationAnswer
populationSemantics = Query.querySemantics populationAnswer

proteinIdentityAdequateAfterAxisErasure :
  Query.AdequateFor axisErasedProjection populationSemantics proteinIdentityQuery
proteinIdentityAdequateAfterAxisErasure =
  Query.factorsForQuery
    (λ observation → sameAdKAnswer)
    (λ { henzlerWildmanWorld → refl ; hansonWorld → refl })

populationInterpretationDefectAfterAxisErasure :
  Query.QueryAdequacyDefect
    axisErasedProjection
    populationSemantics
    dominantPopulationQuery
populationInterpretationDefectAfterAxisErasure =
  Query.queryAdequacyDefect
    henzlerWildmanWorld
    hansonWorld
    refl
    (λ ())

axisErasedPopulationInterpretationNotAdequate :
  Query.AdequateFor
    axisErasedProjection
    populationSemantics
    dominantPopulationQuery
  → ⊥
axisErasedPopulationInterpretationNotAdequate =
  Query.queryAdequacyDefectBlocksFactorisation
    populationInterpretationDefectAfterAxisErasure

------------------------------------------------------------------------
-- Constructive repair: retain which geometric axis the FRET pair observes.
------------------------------------------------------------------------

record AxisAwareObservation : Set where
  constructor axis-aware-observation
  field
    coarseProteinContext : AxisErasedObservation
    fretAxis : FRETAxis
open AxisAwareObservation public

axisAwareProjection : FRETWorld → AxisAwareObservation
axisAwareProjection henzlerWildmanWorld =
  axis-aware-observation sameProteinSameApoContext lidNmpAxis
axisAwareProjection hansonWorld =
  axis-aware-observation sameProteinSameApoContext lidCoreAxis

axisAwarePopulationAnswer : AxisAwareObservation → PopulationAnswer
axisAwarePopulationAnswer
  (axis-aware-observation sameProteinSameApoContext lidNmpAxis) = openMajorAnswer
axisAwarePopulationAnswer
  (axis-aware-observation sameProteinSameApoContext lidCoreAxis) = closedFavouredAnswer

axisAwarePopulationInterpretationAdequate :
  Query.AdequateFor axisAwareProjection populationSemantics dominantPopulationQuery
axisAwarePopulationInterpretationAdequate =
  Query.factorsForQuery
    axisAwarePopulationAnswer
    (λ { henzlerWildmanWorld → refl ; hansonWorld → refl })

------------------------------------------------------------------------
-- Source coordinates.
------------------------------------------------------------------------

record FRETExperimentCoordinate : Set where
  constructor fret-experiment-coordinate
  field
    label : String
    doi : String
    pmid : String
    pmcid : String
    qid : String
    uniprot : String
    residuePair : String
    domainAxis : String
    sourceInterpretation : String
    dewey : String
    directLink : String
    oeis : String
    sourceRole : String
open FRETExperimentCoordinate public

henzlerWildman2007FRET : FRETExperimentCoordinate
henzlerWildman2007FRET =
  fret-experiment-coordinate
    "Henzler-Wildman et al. 2007, Intrinsic motions along an enzymatic reaction trajectory"
    "10.1038/nature06410"
    "18026068"
    "PMCID unresolved in inspected source snapshot"
    "source-article QID unresolved in inspected sources; adenylate kinase Q356240"
    "P69441"
    "Lys145 / Ile52"
    "LID / NMP"
    "ligand-free open state is the major population in the comparison reported by Li-Liu-Ji 2015"
    "exact article-level Dewey unresolved"
    "https://doi.org/10.1038/nature06410"
    "not an integer-sequence object; no same-object OEIS coordinate"
    "primary single-molecule FRET experiment; imported here only for its labelled observation axis and source-bounded population interpretation"

hanson2007FRET : FRETExperimentCoordinate
hanson2007FRET =
  fret-experiment-coordinate
    "Hanson et al. 2007, Illuminating the mechanistic roles of enzyme conformational dynamics"
    "10.1073/pnas.0708600104"
    "17989222"
    "PMC2084295"
    "source-article QID unresolved in inspected sources; adenylate kinase Q356240"
    "P69441"
    "Ala127 / Ala194"
    "LID / CORE"
    "ligand-free equilibrated conformation is reported as favouring the closed state in the Li-Liu-Ji comparison"
    "exact article-level Dewey unresolved"
    "https://doi.org/10.1073/pnas.0708600104"
    "not an integer-sequence object; no same-object OEIS coordinate"
    "primary high-resolution single-molecule FRET experiment; imported here only for its labelled observation axis and source-bounded population interpretation"

liLiuJi2015ObserverComparison : FRETExperimentCoordinate
liLiuJi2015ObserverComparison =
  fret-experiment-coordinate
    "Li, Liu and Ji 2015 observer-axis comparison of prior AdK FRET experiments"
    "10.1016/j.bpj.2015.06.059"
    "26244746"
    "PMC4572606"
    "source-article QID unresolved in inspected sources; adenylate kinase Q356240"
    "P69441"
    "compares Lys145/Ile52 against Ala127/Ala194"
    "compares LID/NMP against LID/CORE"
    "attributes the different one-dimensional population readouts to different labelling positions / geometric observations without declaring either axis a complete conformation observer"
    "exact article-level Dewey unresolved"
    "https://pmc.ncbi.nlm.nih.gov/articles/PMC4572606/"
    "not an integer-sequence object; no same-object OEIS coordinate"
    "secondary comparison source within the AdK dynamics study; pays the explicit axis distinction and comparison, not authority over the original experimental measurements"

------------------------------------------------------------------------
-- Existing rate-observer donor: same lesson at a different information layer.
------------------------------------------------------------------------

rateObserverAdequacyDonor : Rate.AdKRateObserverBoundary
rateObserverAdequacyDonor = Rate.canonicalAdKRateObserverBoundary

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record AdKFRETObserverBoundary : Set where
  constructor adk-fret-observer-boundary
  field
    lidNmpAxisSourcePaid : Bool
    lidNmpAxisSourcePaidIsTrue : lidNmpAxisSourcePaid ≡ true

    lidCoreAxisSourcePaid : Bool
    lidCoreAxisSourcePaidIsTrue : lidCoreAxisSourcePaid ≡ true

    lidNmpExperimentOpenMajor : Bool
    lidNmpExperimentOpenMajorIsTrue : lidNmpExperimentOpenMajor ≡ true

    lidCoreExperimentClosedFavoured : Bool
    lidCoreExperimentClosedFavouredIsTrue : lidCoreExperimentClosedFavoured ≡ true

    axisIdentityRequiredForInterpretation : Bool
    axisIdentityRequiredForInterpretationIsTrue :
      axisIdentityRequiredForInterpretation ≡ true

    multiAxisObservationStrictlyRicherThanAxisErasedObservation : Bool
    multiAxisObservationStrictlyRicherThanAxisErasedObservationIsTrue :
      multiAxisObservationStrictlyRicherThanAxisErasedObservation ≡ true

    oneFRETAxisDeterminesFullConformation : Bool
    oneFRETAxisDeterminesFullConformationIsFalse :
      oneFRETAxisDeterminesFullConformation ≡ false

    differentLabelAxesAreInterchangeable : Bool
    differentLabelAxesAreInterchangeableIsFalse :
      differentLabelAxesAreInterchangeable ≡ false

    populationDifferenceProvesExperimentalContradiction : Bool
    populationDifferenceProvesExperimentalContradictionIsFalse :
      populationDifferenceProvesExperimentalContradiction ≡ false

    sourceComparisonProvesFullThreeDimensionalPopulation : Bool
    sourceComparisonProvesFullThreeDimensionalPopulationIsFalse :
      sourceComparisonProvesFullThreeDimensionalPopulation ≡ false

    fretDistanceEqualsCompleteProteinState : Bool
    fretDistanceEqualsCompleteProteinStateIsFalse :
      fretDistanceEqualsCompleteProteinState ≡ false

canonicalAdKFRETObserverBoundary : AdKFRETObserverBoundary
canonicalAdKFRETObserverBoundary =
  adk-fret-observer-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
