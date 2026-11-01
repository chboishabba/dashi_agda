module DASHI.Physics.Chemistry.AtomicPeriodicTable369MadelungSelectorBoundaryExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369OEISAufbauFormulaWeldExact as Aufbau

------------------------------------------------------------------------
-- Exact boundary for the historical toy ordering C_alpha(n,l)=n+alpha*l.
--
-- The archive reports alpha=0.6 as a representative value and explicitly
-- notes that alpha controls crossings such as 4s/3d.  Scaling by five gives
-- the integer-equivalent score
--
--   score3of5(n,l) = 5*n + 3*l.
--
-- This owner records a concrete later counterexample: alpha=3/5 correctly
-- places 4s before 3d, but it places 4f before 6s.  Madelung/Aufbau order uses
-- n+l first (then lower n on ties), so 6s (n+l=6) must precede 4f (n+l=7).
-- Therefore the fixed-alpha proxy cannot be promoted to the full A167268 /
-- A093907 selector merely from its early Z=2,10,18 successes.
------------------------------------------------------------------------

record OrbitalBlock : Set where
  constructor orbitalBlock
  field
    principal : Nat
    angular : Nat

open OrbitalBlock public

fourS : OrbitalBlock
fourS = orbitalBlock 4 0

threeD : OrbitalBlock
threeD = orbitalBlock 3 2

sixS : OrbitalBlock
sixS = orbitalBlock 6 0

fourF : OrbitalBlock
fourF = orbitalBlock 4 3

madelungDiagonal : OrbitalBlock -> Nat
madelungDiagonal b = principal b + angular b

score3of5 : OrbitalBlock -> Nat
score3of5 b = 5 * principal b + 3 * angular b

------------------------------------------------------------------------
-- Early desired crossing: 4s is cheaper than 3d at alpha=3/5.
------------------------------------------------------------------------

fourSScore : score3of5 fourS ≡ 20
fourSScore = refl

threeDScore : score3of5 threeD ≡ 21
threeDScore = refl

fourSDiagonal : madelungDiagonal fourS ≡ 4
fourSDiagonal = refl

threeDDiagonal : madelungDiagonal threeD ≡ 5
threeDDiagonal = refl

------------------------------------------------------------------------
-- Decisive later reversal: proxy says 4f (29) before 6s (30), while Madelung
-- diagonals say 6s (6) before 4f (7).
------------------------------------------------------------------------

sixSScore : score3of5 sixS ≡ 30
sixSScore = refl

fourFScore : score3of5 fourF ≡ 29
fourFScore = refl

sixSDiagonal : madelungDiagonal sixS ≡ 6
sixSDiagonal = refl

fourFDiagonal : madelungDiagonal fourF ≡ 7
fourFDiagonal = refl

record FixedAlphaThreeFifthsCounterexample : Set where
  constructor fixedAlphaThreeFifthsCounterexample
  field
    early4sScore : score3of5 fourS ≡ 20
    early3dScore : score3of5 threeD ≡ 21
    later6sScore : score3of5 sixS ≡ 30
    later4fScore : score3of5 fourF ≡ 29
    madelung6sDiagonal : madelungDiagonal sixS ≡ 6
    madelung4fDiagonal : madelungDiagonal fourF ≡ 7

canonicalFixedAlphaThreeFifthsCounterexample : FixedAlphaThreeFifthsCounterexample
canonicalFixedAlphaThreeFifthsCounterexample =
  fixedAlphaThreeFifthsCounterexample
    fourSScore threeDScore sixSScore fourFScore sixSDiagonal fourFDiagonal

------------------------------------------------------------------------
-- Provenance and source-role receipt.
------------------------------------------------------------------------

record SelectorSourceReceipt : Set where
  constructor selectorSourceReceipt
  field
    objectName : String
    doi : String
    qid : String
    goldBook : String
    dewey : String
    oeis : String
    directLink : String
    sourceRole : String
    relationship : String

archiveProxyReceipt : SelectorSourceReceipt
archiveProxyReceipt =
  selectorSourceReceipt
    "DASHI Atom archived n+alpha*l toy ordering"
    "unassigned"
    "unassigned"
    "unassigned"
    "539.7 / 546.8 topic coordinates only"
    "A167268 / A093907 comparison targets"
    "canonical DASHI Atom archive thread 25ec0d2e654f33ea6f524f816b4c465e86ef21cf"
    "primary internal programme/run narrative; original standalone script identity still unresolved"
    "historical toy selector whose early closure behaviour is retained, but whose fixed-alpha global Aufbau identity is now explicitly blocked"

aufbauSemanticReceipt : SelectorSourceReceipt
aufbauSemanticReceipt =
  selectorSourceReceipt
    "Aufbau principle"
    "unassigned"
    "Q585745"
    "AT06996"
    "unresolved in inspected semantic source"
    "A167268 / A093907"
    "https://www.wikidata.org/wiki/Q585745"
    "semantic terminology coordinate"
    "identifies the external building-up principle; QID/Gold Book identity imports no DASHI mechanism proof"

allenKnightReceipt : SelectorSourceReceipt
allenKnightReceipt =
  selectorSourceReceipt
    "Allen and Knight, The Lowdin challenge: Origin of the n+l,n (Madelung) rule for filling the orbital configurations of the periodic table"
    "10.1002/qua.965"
    "unresolved"
    "unassigned"
    "unresolved"
    "A167268 / A093907 literature context"
    "https://doi.org/10.1002/qua.965"
    "peer-reviewed analytic literature"
    "external source on the problem of explaining the Madelung filling rule; not evidence that n+alpha*l or DASHI derives that rule"

------------------------------------------------------------------------
-- Corrected selector frontier.
------------------------------------------------------------------------

record MadelungSelectorBoundary : Set where
  constructor madelungSelectorBoundary
  field
    earlyClosuresPromoteFixedAlphaToGlobalAufbau : Bool
    fixedThreeFifthsMatchesA167268Globally : Bool
    arithmeticA093907WeldPaysSelectorMechanism : Bool
    qidGoldBookOrOeisPaysMechanism : Bool
    exactLexicographicMadelungSelectorStillNeeded : Bool

canonicalMadelungSelectorBoundary : MadelungSelectorBoundary
canonicalMadelungSelectorBoundary =
  madelungSelectorBoundary false false false false true

record MadelungSelectorFrontier : Set where
  constructor madelungSelectorFrontier
  field
    paid : String
    disprovedPromotion : String
    nextMathematicalOwner : String
    nextPhysicalOwner : String
    attributionRule : String

canonicalMadelungSelectorFrontier : MadelungSelectorFrontier
canonicalMadelungSelectorFrontier =
  madelungSelectorFrontier
    "capacity formulas and the abstract A093907/A018227 arithmetic construction are exact; alpha=3/5 early 4s/3d scores are also exact"
    "the same fixed alpha=3/5 reverses 6s/4f relative to Madelung order, so early 2,10,18 closure success cannot promote the toy proxy to the full Aufbau selector"
    "implement/prove the exact lexicographic (n+l,n) selector, or a separately justified state-dependent/finite-window selector, and weld it to A167268 before regrouping into A093907"
    "after selector identity, weld the selected basis to the same-object interacting Hamiltonian/spectrum and calibrated ionization energies"
    "archive/DOI/QID/GoldBook/Dewey/OEIS/link remain distinct source coordinates; correction evidence is append-only and does not rewrite the historical run"

-- Link the arithmetic OEIS weld without promoting it into selector identity.
aufbauArithmeticOwner : Set
aufbauArithmeticOwner = Aufbau.OEISAufbauWeldBoundary
