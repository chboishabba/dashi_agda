module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseTerminalNotationRoleBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseWeightedNDimStateGraphExact as Graph
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePartialStateCoordinateAlignmentExact as Align

------------------------------------------------------------------------
-- ADK TERMINAL NOTATION-ROLE BRIDGE
--
-- Li, Liu & Ji 2015 use two terminal symbols in the same ligand-free route
-- discussion:
--
--   prose / Fig. 5 interpretation:
--     gamma -> delta -> zeta
--     alpha -> beta -> epsilon -> zeta
--
--   Eq. (1) path-flux expression:
--     alpha -> beta -> gamma -> delta -> xi
--     alpha -> beta -> epsilon -> xi
--
-- Figure 5 separately says zeta is the closed crystal structure.  This owner
-- records the source-internal collision at the level actually paid by the text:
-- both symbols occupy the terminal closed-route *role*.  It does NOT assert
-- definitional equality xi = zeta, diagnose a typo, or manufacture a per-state
-- dLN coordinate.
------------------------------------------------------------------------

data TerminalNotationTag : Set where
  proseFigureZeta : TerminalNotationTag
  equationFluxXi : TerminalNotationTag

zetaTagIsNotXiTag : proseFigureZeta ≡ equationFluxXi → ⊥
zetaTagIsNotXiTag ()

data TerminalRouteRole : Set where
  terminalClosedRouteRole : TerminalRouteRole

notationRole : TerminalNotationTag → TerminalRouteRole
notationRole proseFigureZeta = terminalClosedRouteRole
notationRole equationFluxXi = terminalClosedRouteRole

zetaAndXiShareTerminalRole :
  notationRole proseFigureZeta ≡ notationRole equationFluxXi
zetaAndXiShareTerminalRole = refl

------------------------------------------------------------------------
-- Heterogeneous source-object bridge.  Equality is intentionally not the
-- carrier: the graph object remains equation-level xi while the figure object
-- remains figure-level zeta.
------------------------------------------------------------------------

record TerminalRoleBridge : Set where
  constructor terminal-role-bridge
  field
    equationGraphState : Graph.AdKLandscapeState
    figureStateLabel : Align.FigureLandscapeStateLabel
    equationNotation : TerminalNotationTag
    figureNotation : TerminalNotationTag
    sharedRole : TerminalRouteRole
    sourceReceipt : String

open TerminalRoleBridge public

canonicalTerminalRoleBridge : TerminalRoleBridge
canonicalTerminalRoleBridge =
  terminal-role-bridge
    Graph.xiEquationTarget
    Align.zetaFigure
    equationFluxXi
    proseFigureZeta
    terminalClosedRouteRole
    "Li-Liu-Ji ligand-free prose terminates both routes at zeta; Eq. (1) writes the corresponding two route-flux paths with terminal xi; bridge is role-level only"

------------------------------------------------------------------------
-- A tagged terminal carrier preserves which source notation was used.
------------------------------------------------------------------------

record TaggedTerminalClosedRouteState : Set where
  constructor tagged-terminal-closed-route-state
  field
    notation : TerminalNotationTag
    role : TerminalRouteRole
    sourceObject : String

open TaggedTerminalClosedRouteState public

figureTaggedTerminal : TaggedTerminalClosedRouteState
figureTaggedTerminal =
  tagged-terminal-closed-route-state
    proseFigureZeta
    terminalClosedRouteRole
    "Figure/prose zeta: closed crystal terminal role"

equationTaggedTerminal : TaggedTerminalClosedRouteState
equationTaggedTerminal =
  tagged-terminal-closed-route-state
    equationFluxXi
    terminalClosedRouteRole
    "Eq. (1) xi: terminal route-flux role"

figureAndEquationTerminalTagsRemainDistinct :
  notation figureTaggedTerminal ≡ notation equationTaggedTerminal → ⊥
figureAndEquationTerminalTagsRemainDistinct ()

------------------------------------------------------------------------
-- Source / attribution coordinate.
------------------------------------------------------------------------

record TerminalNotationSourceCoordinate : Set where
  constructor terminal-notation-source-coordinate
  field
    label : String
    doi : String
    pmid : String
    pmcid : String
    qid : String
    directLink : String
    sourceRole : String
    dLnRole : String

liLiuJi2015TerminalNotationSource : TerminalNotationSourceCoordinate
liLiuJi2015TerminalNotationSource =
  terminal-notation-source-coordinate
    "Li, Liu and Ji 2015 ligand-free AdK terminal notation seam"
    "10.1016/j.bpj.2015.06.059"
    "26244746"
    "PMC4572606"
    "source-article QID unresolved in inspected sources; adenylate kinase Q356240"
    "https://pmc.ncbi.nlm.nih.gov/articles/PMC4572606/"
    "pays prose pathways gamma->delta->zeta and alpha->beta->epsilon->zeta, Figure-5 zeta closed-crystal role, and Eq. (1) corresponding path-flux expressions terminating at xi; does not pay xi=zeta definitional equality"
    "paper defines dLN as a third CV globally, but this notation-role seam supplies no per-state dLN value"

weightedGraphDonor : Graph.WeightedGraphSourceCoordinate
weightedGraphDonor = Graph.liLiuJi2015WeightedGraphSource

partialAlignmentDonor : Align.PartialAlignmentSourceCoordinate
partialAlignmentDonor = Align.liLiuJi2015PartialAlignmentSource

------------------------------------------------------------------------
-- Fail-closed boundary.
------------------------------------------------------------------------

record AdKTerminalNotationRoleBoundary : Set where
  constructor adk-terminal-notation-role-boundary
  field
    proseZetaAndEquationXiShareTerminalClosedRouteRole : Bool
    proseZetaAndEquationXiDefinitionallyIdentified : Bool
    roleBridgeRetainsSourceNotationTag : Bool
    figureZetaClosedCrystalRoleRetained : Bool
    equationXiFluxTerminalRoleRetained : Bool
    sourceInternalNotationCollisionPaysDashiEqualityRepair : Bool
    roleRepairDiagnosesSourceTypo : Bool
    roleRepairCreatesNamedStateDLnCoordinate : Bool
    roleRepairCreatesPerEdgeRate : Bool
    roleRepairCreatesExperimentalMechanism : Bool

canonicalAdKTerminalNotationRoleBoundary : AdKTerminalNotationRoleBoundary
canonicalAdKTerminalNotationRoleBoundary =
  adk-terminal-notation-role-boundary
    true
    false
    true
    true
    true
    false
    false
    false
    false
    false
