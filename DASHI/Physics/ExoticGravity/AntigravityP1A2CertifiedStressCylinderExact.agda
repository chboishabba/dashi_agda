{-# OPTIONS --safe #-}
module DASHI.Physics.ExoticGravity.AntigravityP1A2CertifiedStressCylinderExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.CMP119CosmologyA2LocalCWilsonPresentationCompilerExact as A2
import DASHI.Physics.Foundations.CMP119CosmologyR109FunctionalStressCylinderPresentationExact as Functional
import DASHI.Physics.Foundations.CMP119CosmologyMarkedStressE2PinnedOSAlgebraExact as E2
import DASHI.Physics.YangMills.BalabanCMP119CompatibleLocalExpectationFlowExact as Source
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanClayOSWilsonReflectionPositivityExact as WilsonOS
import DASHI.Physics.YangMills.BalabanStressSameObjectProvenanceRound110Exact as R110
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as LocalC
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119Round109ConcreteLocalCExact as Round109
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119WilsonSourceOS2Exact as WilsonSource
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as OSSystem

------------------------------------------------------------------------
-- A2 CERTIFIED SOURCE SEMANTICS
--
-- Current master already chooses the canonical Local-C encoded stress cylinder
-- and proves its Wilson positive-time / gauge admissibility.  The remaining
-- physical source statement is not another observable choice: it is one
-- evaluator for the opaque Round109 pair whose SELECTED pair-image is exactly
-- that canonical Local-C observable.
--
-- Once this same-object equality is supplied, Wilson admissibility transports
-- automatically and we obtain the functional Round109 presentation with no
-- independent E2/E4 presentation choices.
------------------------------------------------------------------------

module _
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
    (provenance : R110.LiteralStressSameObjectProvenance Y group)
    (round109 : Round109.Round109ConcreteLocalCStressWeld Y group localC)
    (completionMatches :
      R110.markedCompletion provenance ≡ Round109.completion round109)
    (stressEncoding :
      E2.PinnedLocalCStressCylinderEmbedding
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
        localC)
    (wilsonApplication :
      WilsonSource.LiteralCMP119WilsonRPApplication
        Configuration
        (OSSystem.family osInputs group)
        (OSSystem.observableAlgebra osInputs))
  where

  canonicalLocalCStressObservable : Configuration → ℝ
  canonicalLocalCStressObservable =
    E2.encodeStress stressEncoding (LocalC.stressTensor localC)

  record CertifiedA2PairObservableSemantics : Set₁ where
    field
      ordinaryObservableOfPair :
        Source.SourceNativeOrdinaryCharacteristicPair
          (R109.source (R110.sourceCauchy provenance)) →
        Configuration → ℝ

      selectedPairImageIsCanonicalLocalCStressObservable :
        ordinaryObservableOfPair
          (R109.stressInsertion (R110.sourceCauchy provenance))
        ≡ canonicalLocalCStressObservable

  open CertifiedA2PairObservableSemantics public

  compileCertifiedFunctionalPresentation :
    CertifiedA2PairObservableSemantics →
    Functional.FunctionalR109StressCylinderPresentation
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
  compileCertifiedFunctionalPresentation semantics = record
    { Functional.FunctionalR109StressCylinderPresentation.provenance = provenance
    ; Functional.FunctionalR109StressCylinderPresentation.round109 = round109
    ; Functional.FunctionalR109StressCylinderPresentation.completionMatches = completionMatches
    ; Functional.FunctionalR109StressCylinderPresentation.publishedOS =
        WilsonSource.published wilsonApplication
    ; Functional.FunctionalR109StressCylinderPresentation.ordinaryObservableOfPair =
        ordinaryObservableOfPair semantics
    ; Functional.FunctionalR109StressCylinderPresentation.selectedPositiveTime =
        subst
          (WilsonOS.PositiveTimeObservable
            (WilsonSource.published wilsonApplication))
          (sym (selectedPairImageIsCanonicalLocalCStressObservable semantics))
          (WilsonSource.positiveTimeMeaning
            wilsonApplication canonicalLocalCStressObservable)
    ; Functional.FunctionalR109StressCylinderPresentation.selectedGaugeInvariant =
        subst
          (WilsonOS.GaugeInvariant
            (WilsonSource.published wilsonApplication))
          (sym (selectedPairImageIsCanonicalLocalCStressObservable semantics))
          (WilsonSource.positiveTimeGaugeInvariant
            wilsonApplication canonicalLocalCStressObservable)
    }

observableChoiceCompilerOwned : Bool
observableChoiceCompilerOwned = true

positiveTimeCompilerOwnedAfterSameObjectWeld : Bool
positiveTimeCompilerOwnedAfterSameObjectWeld = true

gaugeInvarianceCompilerOwnedAfterSameObjectWeld : Bool
gaugeInvarianceCompilerOwnedAfterSameObjectWeld = true

pairEvaluatorSameObjectSemanticsStillRequired : Bool
pairEvaluatorSameObjectSemanticsStillRequired = true
