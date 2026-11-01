{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyR109WilsonAdmissibleStressCylinderExact where

------------------------------------------------------------------------
-- SHARPER E2/E4 PRESENTATION: PIN ADMISSIBILITY TO THE PUBLISHED OS SURFACE.
--
-- `LiteralR109StressCylinderPresentation` eliminated the arbitrary observable-
-- meaning predicate, but still allowed the presentation itself to invent two
-- predicates called `PositiveTimeSupported` and `GaugeInvariantObservable`.
-- That is unnecessary representational freedom.
--
-- The repository already has the source-facing Menotti--Pelissetto / Wilson OS
-- surface `WilsonReflectionPositivityData`, with the exact predicates
--
--   PositiveTimeObservable : Observable -> Set
--   GaugeInvariant         : Observable -> Set.
--
-- This owner pins the selected R109 stress observable to those predicates.
-- It does NOT assert that the selected observable is admissible; those two
-- proofs remain the genuine physical E2/E4 presentation obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.CMP119CosmologyR109LiteralStressCylinderMaxCutExact as Old
import DASHI.Physics.YangMills.BalabanClayOSWilsonReflectionPositivityExact as WilsonOS
import DASHI.Physics.YangMills.BalabanStressSameObjectProvenanceRound110Exact as R110
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as LocalC
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119Round109ConcreteLocalCExact as Round109

record WilsonAdmissibleR109StressCylinderPresentation
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

    stressInsertionObservable : Configuration → ℝ

    stressInsertionPositiveTime :
      WilsonOS.PositiveTimeObservable publishedOS stressInsertionObservable

    stressInsertionGaugeInvariant :
      WilsonOS.GaugeInvariant publishedOS stressInsertionObservable

open WilsonAdmissibleR109StressCylinderPresentation public

asLiteralR109StressCylinderPresentation :
  ∀ {C S Y group
      G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division osS osInputs reconstruction
      localC} →
  WilsonAdmissibleR109StressCylinderPresentation
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
  Old.LiteralR109StressCylinderPresentation
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
asLiteralR109StressCylinderPresentation presentation = record
  { Old.LiteralR109StressCylinderPresentation.provenance =
      provenance presentation
  ; Old.LiteralR109StressCylinderPresentation.round109 =
      round109 presentation
  ; Old.LiteralR109StressCylinderPresentation.completionMatches =
      completionMatches presentation
  ; Old.LiteralR109StressCylinderPresentation.stressInsertionObservable =
      stressInsertionObservable presentation
  ; Old.LiteralR109StressCylinderPresentation.PositiveTimeSupported =
      WilsonOS.PositiveTimeObservable (publishedOS presentation)
  ; Old.LiteralR109StressCylinderPresentation.GaugeInvariantObservable =
      WilsonOS.GaugeInvariant (publishedOS presentation)
  ; Old.LiteralR109StressCylinderPresentation.stressInsertionPositiveTime =
      stressInsertionPositiveTime presentation
  ; Old.LiteralR109StressCylinderPresentation.stressInsertionGaugeInvariant =
      stressInsertionGaugeInvariant presentation
  }

publishedOSAdmissibilityPredicatesArePinned : Bool
publishedOSAdmissibilityPredicatesArePinned = true

arbitraryPositiveTimePredicateStillPresentationData : Bool
arbitraryPositiveTimePredicateStillPresentationData = false

arbitraryGaugeInvariantPredicateStillPresentationData : Bool
arbitraryGaugeInvariantPredicateStillPresentationData = false

remainingE2E4PhysicalProofsArePublishedPositiveTimeAndGaugeAdmissibility : Bool
remainingE2E4PhysicalProofsArePublishedPositiveTimeAndGaugeAdmissibility = true
