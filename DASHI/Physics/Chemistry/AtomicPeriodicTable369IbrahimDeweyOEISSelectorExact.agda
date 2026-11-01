module DASHI.Physics.Chemistry.AtomicPeriodicTable369IbrahimDeweyOEISSelectorExact where

open import DASHI.Core.Prelude

import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim
import DASHI.Physics.Chemistry.AtomicPeriodicTable369IbrahimDeweyTraversalExact as Prior
import DASHI.Physics.Chemistry.AtomicPeriodicTable369MadelungExactSelector as Selector
import DASHI.Physics.Chemistry.AtomicPeriodicTable369MadelungSelectorBoundaryExact as Boundary

------------------------------------------------------------------------
-- Ibrahim/Dewey/OEIS continuation after the first periodic-table walk.
--
-- The previous traversal reached orbital representation, Aufbau/period-length
-- coordinates, and the physical scale frontier.  The OEIS snowball identifies
-- A167268 as the finer-grained successive-subshell target.  This owner makes
-- the new route explicit:
--
--   periodic-table constructor
--      -> exact structural Madelung selector
--      -> OEIS A167268
--      -> Aufbau principle Q585745 / Gold Book AT06996
--      -> historical Madelung/Klechkovskii/Allen-Knight source chain.
--
-- As elsewhere, navigation does not import proof authority.
------------------------------------------------------------------------

exactSelectorCoordinate : Ibrahim.DashiKnowledgeCoordinate
exactSelectorCoordinate =
  Ibrahim.dashi-knowledge-coordinate
    "DASHI/Physics/Chemistry/AtomicPeriodicTable369MadelungExactSelector.agda"
    "generic lexicographic (n+l,n) structural selector and A167268 capacity-prefix generator"
    "539.7 / 546.8 topic coordinates; exact Dewey unresolved"
    "Aufbau Q585745 semantic coordinate"
    "PR #886; current selector repair"

janetSequenceCoordinate : Ibrahim.DashiKnowledgeCoordinate
janetSequenceCoordinate =
  Ibrahim.dashi-knowledge-coordinate
    "external integer-sequence coordinate"
    "OEIS A167268: capacities of successively filled electronic subshells"
    "Dewey unresolved"
    "QID unresolved; OEIS A167268"
    "https://oeis.org/A167268"

aufbauCoordinate : Ibrahim.DashiKnowledgeCoordinate
aufbauCoordinate =
  Ibrahim.dashi-knowledge-coordinate
    "external semantic / terminology coordinate"
    "Aufbau principle / building-up principle"
    "Dewey unresolved in inspected semantic item"
    "Q585745; IUPAC Gold Book AT06996"
    "https://www.wikidata.org/wiki/Q585745"

madelungHistoricalCoordinate : Ibrahim.DashiKnowledgeCoordinate
madelungHistoricalCoordinate =
  Ibrahim.dashi-knowledge-coordinate
    "Erwin Madelung, Die Mathematischen Hilfsmittel des Physikers, 1936 edition"
    "historical n+l,n rule lineage"
    "Dewey unresolved"
    "author Erwin Madelung Q72626"
    "DOI 10.1007/978-3-662-02177-4 (Springer archive e-book object for the 1936 edition)"

klechkovskiiCoordinate : Ibrahim.DashiKnowledgeCoordinate
klechkovskiiCoordinate =
  Ibrahim.dashi-knowledge-coordinate
    "V. M. Klechkovskii, Justification of the Rule for Successive Filling of (n + l) Groups"
    "historical primary physical-rule source"
    "Dewey unresolved"
    "QID unresolved"
    "JETP 14(2), 334 (1962); direct JETP source; DOI unresolved in inspected source"

allenKnightCoordinate : Ibrahim.DashiKnowledgeCoordinate
allenKnightCoordinate =
  Ibrahim.dashi-knowledge-coordinate
    "Allen and Knight, The Lowdin challenge"
    "modern analytic source on origin/limits of the Madelung rule"
    "Dewey unresolved"
    "QID unresolved"
    "DOI 10.1002/qua.965"

historicalProxyCoordinate : Ibrahim.DashiKnowledgeCoordinate
historicalProxyCoordinate =
  Ibrahim.dashi-knowledge-coordinate
    "DASHI Atom archive n+alpha*l toy selector"
    "retained historical finite producer with alpha-sensitive crossings"
    "539.7 / 546.8 topic coordinates only"
    "QID unassigned"
    "archive thread 25ec0d2e654f33ea6f524f816b4c465e86ef21cf"

------------------------------------------------------------------------
-- Typed route edges.
------------------------------------------------------------------------

periodicTableToExactSelector : Ibrahim.DashiFirstLinkEdge
periodicTableToExactSelector =
  Ibrahim.dashi-first-link-edge
    Prior.periodicTableCoordinate
    exactSelectorCoordinate
    Ibrahim.dependsOn
    Ibrahim.canonicalDashiFirstLinkPolicy
    "periodic-table period/closure construction needs an explicit filling-order selector once principal-shell capacity is distinguished from period length"
    true

exactSelectorToA167268 : Ibrahim.DashiFirstLinkEdge
exactSelectorToA167268 =
  Ibrahim.dashi-first-link-edge
    exactSelectorCoordinate
    janetSequenceCoordinate
    Ibrahim.externallyIdentifiedBy
    Ibrahim.canonicalDashiFirstLinkPolicy
    "the selector's generated capacity prefixes coincide with the OEIS A167268 successive-subshell capacity coordinate"
    true

A167268ToAufbau : Ibrahim.DashiFirstLinkEdge
A167268ToAufbau =
  Ibrahim.dashi-first-link-edge
    janetSequenceCoordinate
    aufbauCoordinate
    Ibrahim.supportedBy
    Ibrahim.canonicalDashiFirstLinkPolicy
    "OEIS describes A167268 as the successive-subshell capacities in Aufbau/Madelung building order; this is source navigation, not mechanism proof"
    true

aufbauToMadelungHistory : Ibrahim.DashiFirstLinkEdge
aufbauToMadelungHistory =
  Ibrahim.dashi-first-link-edge
    aufbauCoordinate
    madelungHistoricalCoordinate
    Ibrahim.supportedBy
    Ibrahim.canonicalDashiFirstLinkPolicy
    "modern Madelung-rule literature traces the n+l,n ordering to Madelung's historical exposition"
    true

madelungToKlechkovskii : Ibrahim.DashiFirstLinkEdge
madelungToKlechkovskii =
  Ibrahim.dashi-first-link-edge
    madelungHistoricalCoordinate
    klechkovskiiCoordinate
    Ibrahim.crossPollinatesWith
    Ibrahim.canonicalDashiFirstLinkPolicy
    "Klechkovskii gives a historical physical justification of successive n+l-group filling; retained as a distinct source object"
    true

madelungToAllenKnight : Ibrahim.DashiFirstLinkEdge
madelungToAllenKnight =
  Ibrahim.dashi-first-link-edge
    madelungHistoricalCoordinate
    allenKnightCoordinate
    Ibrahim.crossPollinatesWith
    Ibrahim.canonicalDashiFirstLinkPolicy
    "Allen-Knight explicitly study the origin and physical complications of the Madelung rule and cite Madelung 1936"
    true

historicalProxyToExactSelector : Ibrahim.DashiFirstLinkEdge
historicalProxyToExactSelector =
  Ibrahim.dashi-first-link-edge
    historicalProxyCoordinate
    exactSelectorCoordinate
    Ibrahim.generalisesTo
    Ibrahim.canonicalDashiFirstLinkPolicy
    "the exact selector is a typed repair/generalisation of the historical finite toy route; append-only provenance preserves the proxy rather than rewriting it"
    true

------------------------------------------------------------------------
-- Route status and non-promotion boundary.
------------------------------------------------------------------------

record IbrahimDeweyOEISSelectorBoundary : Set where
  constructor ibrahim-dewey-oeis-selector-boundary
  field
    exactSelectorExists : Bool
    a167268PrefixGenerationExists : Bool
    historicalProxyEqualsExactSelector : Bool
    oeisIdentifiesPhysicalMechanism : Bool
    madelungHistoricalCitationProvesDashiSelector : Bool
    deweyOrQidPaysPhysicalOrder : Bool

canonicalIbrahimDeweyOEISSelectorBoundary : IbrahimDeweyOEISSelectorBoundary
canonicalIbrahimDeweyOEISSelectorBoundary =
  ibrahim-dewey-oeis-selector-boundary true true false false false false

record IbrahimDeweyOEISSelectorFrontier : Set where
  constructor ibrahim-dewey-oeis-selector-frontier
  field
    paidRoute : String
    correction : String
    nextStructuralWeld : String
    nextPhysicalWeld : String
    nextHistoricalLeaf : String
    paymentRule : String

canonicalIbrahimDeweyOEISSelectorFrontier : IbrahimDeweyOEISSelectorFrontier
canonicalIbrahimDeweyOEISSelectorFrontier =
  ibrahim-dewey-oeis-selector-frontier
    "periodic-table -> exact (n+l,n) selector -> A167268 -> Aufbau Q585745/GoldBook AT06996 -> Madelung/Klechkovskii/Allen-Knight source chain is now explicit"
    "the historical n+alpha*l producer remains provenance-valid but is not globally identical to this selector; alpha=3/5 reverses 6s/4f"
    "partition the exact selected subshell stream into period blocks and connect that same-object partition to A093907/A018227, rather than relying only on their closed-form arithmetic generator"
    "connect the selected block basis to the interacting Hamiltonian/spectrum and calibrated ionization-energy consumer"
    "continue searching for the original standalone historical filling script/hash/parameter schedule and any same-object pre-PR public manuscript"
    "Ibrahim/Dewey/OEIS/QID/GoldBook/DOI/link select evidence targets; only dependency-satisfying same-object receipts pay conclusions"

selectorOwner : Set
selectorOwner = Selector.ExactMadelungSelectorBoundary

historicalBoundaryOwner : Set
historicalBoundaryOwner = Boundary.MadelungSelectorBoundary
