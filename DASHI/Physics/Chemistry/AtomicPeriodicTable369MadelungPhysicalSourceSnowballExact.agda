module DASHI.Physics.Chemistry.AtomicPeriodicTable369MadelungPhysicalSourceSnowballExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369MadelungExactSelector as Selector

------------------------------------------------------------------------
-- Primary/analytic source snowball for the n+l,n structural selector.
--
-- These receipts are deliberately separated from the exact Agda selector:
-- the selector is a mathematical ordering object; the literature addresses
-- historical formulation, model justification, and empirical/physical limits.
------------------------------------------------------------------------

record MadelungPhysicalSource : Set where
  constructor madelungPhysicalSource
  field
    authors : String
    title : String
    year : String
    doi : String
    qid : String
    dewey : String
    oeis : String
    directLink : String
    primaryStatus : String
    relationship : String

madelung1936 : MadelungPhysicalSource
madelung1936 =
  madelungPhysicalSource
    "Erwin Madelung"
    "Die Mathematischen Hilfsmittel des Physikers"
    "1936, second edition"
    "10.1007/978-3-662-02177-4 (modern Springer archive e-book DOI)"
    "Erwin Madelung Q72626"
    "unresolved"
    "A167268 / A093907 historical rule lineage"
    "https://doi.org/10.1007/978-3-662-02177-4"
    "historical source object"
    "historical lineage for the n+l,n rule; archive DOI date is not silently treated as a 1936 DOI assignment"

klechkovskii1962 : MadelungPhysicalSource
klechkovskii1962 =
  madelungPhysicalSource
    "V. M. Klechkovskii"
    "Justification of the Rule for Successive Filling of (n + l) Groups"
    "Soviet Physics JETP 14(2), 334, February 1962; submitted 1961-02-16"
    "unassigned in inspected JETP source"
    "unresolved"
    "unresolved"
    "A167268 / A093907 physical-rule context"
    "https://jetp.ras.ru/cgi-bin/e/index/e/14/2/p334?a=list"
    "primary historical physics paper"
    "derives successive n+l-group filling inside a Thomas-Fermi statistical model and explicitly notes that predicted Z interval limits are close to but not exactly empirical"

demkovOstrovskii1972 : MadelungPhysicalSource
demkovOstrovskii1972 =
  madelungPhysicalSource
    "Yu. N. Demkov and V. N. Ostrovskii"
    "n+l Filling Rule in the Periodic System and Focusing Potentials"
    "Soviet Physics JETP 35(1), 66, July 1972; submitted 1971-07-09"
    "unassigned in inspected JETP source"
    "unresolved"
    "unresolved"
    "A167268 / A093907 physical-rule context"
    "https://jetp.ras.ru/cgi-bin/e/index/e/35/1/p66?a=list"
    "primary historical physics paper"
    "states the lexicographic n+l,n rule, supplies a focusing-potential model, and explicitly marks empirical exceptions; therefore it supports the structural rule while blocking exception-free ground-state promotion"

allenKnight2002 : MadelungPhysicalSource
allenKnight2002 =
  madelungPhysicalSource
    "Leland C. Allen and Eugene T. Knight"
    "The Lowdin challenge: Origin of the n+l,n (Madelung) rule for filling the orbital configurations of the periodic table"
    "2002"
    "10.1002/qua.965"
    "unresolved"
    "unresolved"
    "A167268 / A093907 analytic context"
    "https://doi.org/10.1002/qua.965"
    "peer-reviewed analytic literature"
    "uses relativistic atomic-orbital data through Z=118 to analyze s/d and s/f perturbations and the unexpected occupancy order; analytic context, not DASHI mechanism authority"

------------------------------------------------------------------------
-- Source-level boundary.
------------------------------------------------------------------------

record MadelungPhysicalSourceBoundary : Set where
  constructor madelungPhysicalSourceBoundary
  field
    primaryLiteratureSupportsRuleFamily : Bool
    primaryLiteratureReportsModelDependence : Bool
    primaryLiteratureReportsExceptions : Bool
    structuralSelectorEqualsEmpiricalGroundStateSequence : Bool
    ThomasFermiModelEqualsDashi369Mechanism : Bool
    focusingPotentialEqualsDashiHamiltonian : Bool
    citationImportsPhysicalProofIntoAgda : Bool

canonicalMadelungPhysicalSourceBoundary : MadelungPhysicalSourceBoundary
canonicalMadelungPhysicalSourceBoundary =
  madelungPhysicalSourceBoundary true true true false false false false

------------------------------------------------------------------------
-- Highest-alpha consequence for the physical lane.
------------------------------------------------------------------------

record MadelungPhysicalSourceFrontier : Set where
  constructor madelungPhysicalSourceFrontier
  field
    sourceLeafPaid : String
    exceptionBoundaryPaid : String
    nextPhysicalObject : String
    empiricalComparisonLeaf : String
    attributionRule : String

canonicalMadelungPhysicalSourceFrontier : MadelungPhysicalSourceFrontier
canonicalMadelungPhysicalSourceFrontier =
  madelungPhysicalSourceFrontier
    "Madelung historical lineage plus Klechkovskii Thomas-Fermi justification, Demkov/Ostrovskii focusing-potential analysis, and Allen/Knight modern analytic context are explicitly receipted"
    "the source chain itself establishes that the simple n+l,n rule is a structural/model rule with empirical exceptions, so the exact Agda selector is not silently promoted to literal ground-state occupancy for every atom"
    "same-object DASHI interacting Hamiltonian on the selected one-particle basis, with ground-state selector and spectrum receipts"
    "compare selected structural order against authoritative ground-state configurations/levels only after the empirical dataset/source object is explicitly acquired"
    "DOI/QID/Dewey/OEIS/link/source dates remain attribution coordinates; only the source's stated model/result and same-object formal witness pay each claim"

selectorBoundaryOwner : Set
selectorBoundaryOwner = Selector.ExactMadelungSelectorBoundary
