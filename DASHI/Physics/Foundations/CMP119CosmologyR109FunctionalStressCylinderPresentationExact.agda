{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyR109FunctionalStressCylinderPresentationExact where

------------------------------------------------------------------------
-- E2/E4 FUNCTIONAL PRESENTATION OF THE ABSTRACT ROUND109 INSERTION PAIR.
--
-- The previous max-cut removed an arbitrary meaning predicate but still chose
-- a cylinder observable independently and then declared equality to that chosen
-- observable.  That relation is tautological and does not encode a presentation
-- of the abstract source insertion.
--
-- Here the physical presentation datum is instead one FUNCTION
--
--   ordinaryObservableOfPair : source-native pair -> Configuration -> R.
--
-- The selected stress observable is definitionally the image of the literal
-- Round109 stressInsertion under that function.  There is no second observable
-- choice.  Published OS positive-time/gauge admissibility is required only for
-- this selected image.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.CMP119CosmologyR109WilsonAdmissibleStressCylinderExact as WilsonPinned
import DASHI.Physics.YangMills.BalabanCMP119CompatibleLocalExpectationFlowExact as Source
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanClayOSWilsonReflectionPositivityExact as WilsonOS
import DASHI.Physics.YangMills.BalabanStressSameObjectProvenanceRound110Exact as R110
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as LocalC
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119Round109ConcreteLocalCExact as Round109

record FunctionalR109StressCylinderPresentation
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (group : Top.CompactSimpleGroup C)
    {G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient Hilbert Vector Hamiltonian Algebra
     Scale Volume Root ContinuumFamily Core
     sequenceLimit limitLaws quotient division osS osInputs reconstruction}
    (localC :
      LocalC.PinnedCMP119ConcreteLocalCInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient (Top.StressTensor C)
        Hilbert Vector Hamiltonian Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = osS}
        osInputs reconstruction group)
    : Set₂ where
  field
    provenance : R110.LiteralStressSameObjectProvenance Y group

    round109 :
      Round109.Round109ConcreteLocalCStressWeld Y group localC

    completionMatches :
      R110.markedCompletion provenance
      ≡ Round109.completion round109

    publishedOS :
      WilsonOS.WilsonReflectionPositivityData
        (Configuration → ℝ) ℝ

    ordinaryObservableOfPair :
      Source.SourceNativeOrdinaryCharacteristicPair
        (R109.source (R110.sourceCauchy provenance)) →
      Configuration → ℝ

    selectedPositiveTime :
      WilsonOS.PositiveTimeObservable publishedOS
        (ordinaryObservableOfPair
          (R109.stressInsertion (R110.sourceCauchy provenance)))

    selectedGaugeInvariant :
      WilsonOS.GaugeInvariant publishedOS
        (ordinaryObservableOfPair
          (R109.stressInsertion (R110.sourceCauchy provenance)))

open FunctionalR109StressCylinderPresentation public

selectedStressObservable :
  ∀ {C S Y group
      G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division osS osInputs reconstruction
      localC} →
  FunctionalR109StressCylinderPresentation
    {C = C} {S = S} Y group
    {G = G} {X = X} {Configuration = Configuration}
    {Position = Position} {CurvaturePolynomial = CurvaturePolynomial}
    {LocalOperator = LocalOperator} {OPECoefficient = OPECoefficient}
    {Hilbert = Hilbert} {Vector = Vector}
    {Hamiltonian = Hamiltonian} {Algebra = Algebra}
    {Scale = Scale} {Volume = Volume} {Root = Root}
    {ContinuumFamily = ContinuumFamily} {Core = Core}
    {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
    {quotient = quotient} {division = division}
    {osS = osS} {osInputs = osInputs} {reconstruction = reconstruction}
    localC →
  Configuration → ℝ
selectedStressObservable presentation =
  ordinaryObservableOfPair presentation
    (R109.stressInsertion (R110.sourceCauchy (provenance presentation)))

asWilsonAdmissibleR109StressCylinderPresentation :
  ∀ {C S Y group
      G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division osS osInputs reconstruction
      localC} →
  FunctionalR109StressCylinderPresentation
    {C = C} {S = S} Y group
    {G = G} {X = X} {Configuration = Configuration}
    {Position = Position} {CurvaturePolynomial = CurvaturePolynomial}
    {LocalOperator = LocalOperator} {OPECoefficient = OPECoefficient}
    {Hilbert = Hilbert} {Vector = Vector}
    {Hamiltonian = Hamiltonian} {Algebra = Algebra}
    {Scale = Scale} {Volume = Volume} {Root = Root}
    {ContinuumFamily = ContinuumFamily} {Core = Core}
    {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
    {quotient = quotient} {division = division}
    {osS = osS} {osInputs = osInputs} {reconstruction = reconstruction}
    localC →
  WilsonPinned.WilsonAdmissibleR109StressCylinderPresentation
    {C = C} {S = S} Y group
    {G = G} {X = X} {Configuration = Configuration}
    {Position = Position} {CurvaturePolynomial = CurvaturePolynomial}
    {LocalOperator = LocalOperator} {OPECoefficient = OPECoefficient}
    {Hilbert = Hilbert} {Vector = Vector}
    {Hamiltonian = Hamiltonian} {Algebra = Algebra}
    {Scale = Scale} {Volume = Volume} {Root = Root}
    {ContinuumFamily = ContinuumFamily} {Core = Core}
    {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
    {quotient = quotient} {division = division}
    {osS = osS} {osInputs = osInputs} {reconstruction = reconstruction}
    localC
asWilsonAdmissibleR109StressCylinderPresentation presentation = record
  { WilsonPinned.WilsonAdmissibleR109StressCylinderPresentation.provenance =
      provenance presentation
  ; WilsonPinned.WilsonAdmissibleR109StressCylinderPresentation.round109 =
      round109 presentation
  ; WilsonPinned.WilsonAdmissibleR109StressCylinderPresentation.completionMatches =
      completionMatches presentation
  ; WilsonPinned.WilsonAdmissibleR109StressCylinderPresentation.publishedOS =
      publishedOS presentation
  ; WilsonPinned.WilsonAdmissibleR109StressCylinderPresentation.stressInsertionObservable =
      selectedStressObservable presentation
  ; WilsonPinned.WilsonAdmissibleR109StressCylinderPresentation.stressInsertionPositiveTime =
      selectedPositiveTime presentation
  ; WilsonPinned.WilsonAdmissibleR109StressCylinderPresentation.stressInsertionGaugeInvariant =
      selectedGaugeInvariant presentation
  }

selectedObservableIsDefinedFromSelectedR109Insertion : Bool
selectedObservableIsDefinedFromSelectedR109Insertion = true

independentSelectedCylinderObservableStillPresentationData : Bool
independentSelectedCylinderObservableStillPresentationData = false

remainingE2E4PresentationDatumIsOrdinaryPairToObservableMap : Bool
remainingE2E4PresentationDatumIsOrdinaryPairToObservableMap = true
