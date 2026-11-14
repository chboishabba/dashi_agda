module DASHI.Wikimedia.IbrahimFiniteFigureBasinCertificateExact where

open import DASHI.Core.Prelude

import DASHI.Wikimedia.IbrahimPublishedSevenNodeFunnelExact as Figure
import DASHI.Wikimedia.IbrahimFiniteOrbitRevisionWeldExact as Orbit
import DASHI.Wikimedia.IbrahimGeneralFiniteCertificateKernelExact as General
import DASHI.Wikimedia.IbrahimFinitePigeonholeProducerExact as Pigeonhole
import DASHI.Wikimedia.WikipediaFirstLinkNetworkExact as FLN

------------------------------------------------------------------------
-- IBRAHIM SEVEN-NODE FIGURE: EXHAUSTIVE FINITE ORBIT CERTIFICATE
--
-- External historical example:
-- Mark Ibrahim, Christopher M. Danforth, Peter Sheridan Dodds,
-- "Connecting every bit of knowledge: The structure of Wikipedia's
-- First Link Network", Journal of Computational Science 19 (2017),
-- 21-30. DOI 10.1016/j.jocs.2016.12.001.
-- Author manuscript Figures 2-4: A -> B -> C -> A, D -> C,
-- E -> C, F -> E, G -> E.
--
-- The following total seven-case certificate is a NEW DASHI
-- reconstruction of that paper figure. It is NOT a proof of a
-- 4.7-million-node corpus, parser fidelity, or a general algorithm
-- that creates a cycle certificate from any finite graph.
------------------------------------------------------------------------

data InFigureList (node : Figure.FigureNode) :
  List Figure.FigureNode → Set where
  here : ∀ {xs} → InFigureList node (node ∷ xs)
  there : ∀ {other xs} →
    InFigureList node xs → InFigureList node (other ∷ xs)

figureEnumerationCoversEveryNode :
  (node : Figure.FigureNode) →
  InFigureList node Figure.allStarts
figureEnumerationCoversEveryNode Figure.a = here
figureEnumerationCoversEveryNode Figure.b = there here
figureEnumerationCoversEveryNode Figure.c = there (there here)
figureEnumerationCoversEveryNode Figure.d = there (there (there here))
figureEnumerationCoversEveryNode Figure.e = there (there (there (there here)))
figureEnumerationCoversEveryNode Figure.f =
  there (there (there (there (there here))))
figureEnumerationCoversEveryNode Figure.g =
  there (there (there (there (there (there here)))))

-- All seven starts reach the SAME explicit period-3 cycle at C.
-- Entry hops are (2, 1, 0, 1, 1, 2, 2) in A..G order.
figureEventuallyC :
  (node : Figure.FigureNode) →
  Orbit.EventualCycle Figure.figureFirstLink node
figureEventuallyC Figure.a =
  Orbit.eventualCycle 2 2 Figure.c refl refl
figureEventuallyC Figure.b =
  Orbit.eventualCycle 1 2 Figure.c refl refl
figureEventuallyC Figure.c =
  Orbit.eventualCycle 0 2 Figure.c refl refl
figureEventuallyC Figure.d =
  Orbit.eventualCycle 1 2 Figure.c refl refl
figureEventuallyC Figure.e =
  Orbit.eventualCycle 1 2 Figure.c refl refl
figureEventuallyC Figure.f =
  Orbit.eventualCycle 2 2 Figure.c refl refl
figureEventuallyC Figure.g =
  Orbit.eventualCycle 2 2 Figure.c refl refl

figureBasinRepresentativeAlwaysC :
  (node : Figure.FigureNode) →
  Orbit.representative (figureEventuallyC node) ≡ Figure.c
figureBasinRepresentativeAlwaysC Figure.a = refl
figureBasinRepresentativeAlwaysC Figure.b = refl
figureBasinRepresentativeAlwaysC Figure.c = refl
figureBasinRepresentativeAlwaysC Figure.d = refl
figureBasinRepresentativeAlwaysC Figure.e = refl
figureBasinRepresentativeAlwaysC Figure.f = refl
figureBasinRepresentativeAlwaysC Figure.g = refl

figureEveryEntryCertificateSound :
  (node : Figure.FigureNode) →
  Orbit.iterate Figure.figureFirstLink
    (Orbit.entryHops (figureEventuallyC node)) node
    ≡ Figure.c
figureEveryEntryCertificateSound node =
  trans (Orbit.entered (figureEventuallyC node))
        (figureBasinRepresentativeAlwaysC node)

figureEveryCycleCertificateCloses :
  (node : Figure.FigureNode) →
  Orbit.iterate Figure.figureFirstLink
    (suc (Orbit.periodTail (figureEventuallyC node)))
    (Orbit.representative (figureEventuallyC node))
  ≡ Orbit.representative (figureEventuallyC node)
figureEveryCycleCertificateCloses node =
  Orbit.closed (figureEventuallyC node)

figureSameBasinForEveryPair :
  (left right : Figure.FigureNode) →
  Orbit.representative (figureEventuallyC left) ≡
  Orbit.representative (figureEventuallyC right)
figureSameBasinForEveryPair left right =
  trans (figureBasinRepresentativeAlwaysC left)
    (sym (figureBasinRepresentativeAlwaysC right))

------------------------------------------------------------------------
-- Same original manuscript Figure 2-4 through the GENERAL certificate
-- interface. The old seven-case witnesses now instantiate a reusable
-- all-node finite classifier, not a second independent graph theory.
------------------------------------------------------------------------

figureGeneralCarrier :
  General.CompleteFiniteCarrier Figure.FigureNode
figureGeneralCarrier =
  General.completeFiniteCarrier Figure.allStarts cover
  where
    cover :
      (node : Figure.FigureNode) →
      General.Listed node Figure.allStarts
    cover Figure.a = General.listedHere
    cover Figure.b = General.listedThere General.listedHere
    cover Figure.c =
      General.listedThere (General.listedThere General.listedHere)
    cover Figure.d =
      General.listedThere
        (General.listedThere (General.listedThere General.listedHere))
    cover Figure.e =
      General.listedThere
        (General.listedThere
          (General.listedThere (General.listedThere General.listedHere)))
    cover Figure.f =
      General.listedThere
        (General.listedThere
          (General.listedThere
            (General.listedThere
              (General.listedThere General.listedHere))))
    cover Figure.g =
      General.listedThere
        (General.listedThere
          (General.listedThere
            (General.listedThere
              (General.listedThere
                (General.listedThere General.listedHere)))))

figureGeneralRepeatWitnesses :
  General.FiniteOrbitRepeatCertificate Figure.figureFirstLink
figureGeneralRepeatWitnesses =
  General.finiteOrbitRepeatCertificate
    (λ node → General.eventualCycleToCollision (figureEventuallyC node))

figureGeneralCensus :
  General.VerifiedFiniteFirstLinkCensus Figure.figureFirstLink
figureGeneralCensus =
  General.finiteFirstLinkOrbitClassifies
    Figure.figureFirstLink
    figureGeneralCarrier
    figureGeneralRepeatWitnesses

-- Independent of the hand-enumerated seven orbit repeat witnesses:
-- the generic finite pigeonhole producer now derives them solely from
-- the already established exhaustive manuscript figure carrier.
figurePigeonholeCensus :
  General.VerifiedFiniteFirstLinkCensus Figure.figureFirstLink
figurePigeonholeCensus =
  Pigeonhole.finiteFirstLinkOrbitClassifiesAutomatically
    Figure.figureFirstLink figureGeneralCarrier

figurePigeonholeEveryStartHasCycle :
  (node : Figure.FigureNode) →
  Orbit.EventualCycle Figure.figureFirstLink node
figurePigeonholeEveryStartHasCycle =
  Pigeonhole.allFiniteStartsEventuallyCycle
    Figure.figureFirstLink figureGeneralCarrier

figureGeneralCensusEntrySound :
  (node : Figure.FigureNode) →
  Orbit.iterate Figure.figureFirstLink
    (Orbit.entryHops (General.eventCycle figureGeneralCensus node)) node
  ≡ Orbit.representative (General.eventCycle figureGeneralCensus node)
figureGeneralCensusEntrySound =
  General.terminalCensusMatchesCertificate figureGeneralCensus

------------------------------------------------------------------------
-- Explicit scope boundary: the enumeration is of the 7-node
-- manuscript fixture, not a class of historical Wikipedia pages.
------------------------------------------------------------------------

data FigureEnumerationProvesHistoricalCorpusExhaustive : Set where
data FigureCycleProvesContemporaryWikipediaInvariant : Set where

figureEnumerationDoesNotExhaustHistoricalCorpus :
  FigureEnumerationProvesHistoricalCorpusExhaustive → ⊥
figureEnumerationDoesNotExhaustHistoricalCorpus ()

figureCycleDoesNotProveCurrentInvariant :
  FigureCycleProvesContemporaryWikipediaInvariant → ⊥
figureCycleDoesNotProveCurrentInvariant ()
