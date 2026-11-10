module DASHI.Physics.Motors.Resonate369SchematicAdmissionExact where

------------------------------------------------------------------------
-- SOURCE-BOUND SCHEMATIC INFERENCE, NOT A CLAIM TO HAVE DOWNLOADED
-- ANY MANUFACTURER SCHEMATIC OR THIRD-PARTY CAD.
--
-- Slobodian / Infinity SAV historical claims and Holmstrom /
-- Resonate369 derivative devices are kept explicitly distinct.
-- The constructor names below describe hypothetical source evidence.
--
-- Neither schematic implication nor a structural model implies
-- physical efficiency, flyback recovery, or anomalous energy.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Motors.Resonate369ConditionalPolarityExact as Polarity

-- A statement is not promoted to an observed/verified source fact by
-- its mere existence as a Boolean, string, or constructor argument.
data EvidenceKind : Set where
  manufacturerDescription : EvidenceKind
  originalSchematic : EvidenceKind
  readOnlyCADMeasurement : EvidenceKind
  videoObservation : EvidenceKind
  physicalInstrumentMeasurement : EvidenceKind

data DesignIdentity : Set where
  slobodianHistoricalMG10 : DesignIdentity
  holmstromC07 : DesignIdentity
  holmstromDodecatron : DesignIdentity
  holmstromV1Impulse : DesignIdentity
  holmstromEZSpin : DesignIdentity
  holmstromAtmoMotor : DesignIdentity

record SourceReceipt : Set where
  constructor sourceReceipt
  field
    design : DesignIdentity
    revision : String
    sourceURL : String
    authorAttribution : String
    sourceKind : EvidenceKind
    extractionMethod : String
    uncertaintyStatement : String

-- All source evidence is attached to a named, revision-specific design.
-- Evidence acceptance must be supplied by an external inspection step,
-- never inferred from a product description or a source URL.
record SelectedEvidence (design : DesignIdentity) : Set where
  constructor selectedEvidence
  field
    receipt : SourceReceipt
    sameDesign : SourceReceipt.design receipt ≡ design
    inspectedSource : Set

data Terminal : Set where
  terminalA terminalB : Terminal

data Component : Set where
  coil : Nat → Component
  magnet : Nat → Component
  capacitor : Nat → Component
  diode : Nat → Component
  switch : Nat → Component
  supply : Component
  earth : Component

record Port : Set where
  constructor port
  field
    component : Component
    terminal : Terminal

-- A netlist is a *model*; absence of listed edges does not imply
-- the absence of physical connections. No edge is asserted here
-- about a particular manufactured circuit.
record Netlist : Set where
  constructor netlist
  field
    Connected : Port → Port → Set

-- An admitted connection needs an original selected source witness.
record AdmittedConnection
  (design : DesignIdentity)
  (n : Netlist)
  (p q : Port) : Set where
  constructor admittedConnection
  field
    source : SelectedEvidence design
    depictedConnection : Netlist.Connected n p q

-- Path composition is purely structural, and works without
-- first estimating resistance, voltage, or energy.
data Reachable (n : Netlist) : Port → Port → Set where
  same : ∀ {p} → Reachable n p p
  then : ∀ {p q r} →
    Netlist.Connected n p q →
    Reachable n q r →
    Reachable n p r

-- A path of two depicted edges is an entailed graph path.
twoEdgePath :
  (n : Netlist) (p q r : Port) →
  Netlist.Connected n p q →
  Netlist.Connected n q r →
  Reachable n p r
twoEdgePath n p q r pq qr = then pq (then qr same)

-- Describing all coils as 'in series' is a textual source assertion
-- unless selected electrical junctions confirm an actual one-path
-- topology and exclude bypass branches.
record SelectedSeriesTrace (design : DesignIdentity) (n : Netlist) : Set where
  constructor selectedSeriesTrace
  field
    source : SelectedEvidence design
    entry exit : Port
    connectedSeriesPath : Reachable n entry exit
    noParallelBypassEstablished : Set

-- Additional physical assumptions are first-class gates.
-- Nothing below constructs these records for real devices.
record SelectedWindingPolarity (design : DesignIdentity) : Set where
  constructor selectedWindingPolarity
  field
    source : SelectedEvidence design
    pole winding terminal : Bool

record OppositePoleAndWinding
  (design : DesignIdentity) : Set where
  constructor oppositePoleAndWinding
  field
    first second : SelectedWindingPolarity design
    oppositePoles :
      SelectedWindingPolarity.pole second
      ≡ Polarity.flip (SelectedWindingPolarity.pole first)
    oppositeWindings :
      SelectedWindingPolarity.winding second
      ≡ Polarity.flip (SelectedWindingPolarity.winding first)
    sameTerminalConvention :
      SelectedWindingPolarity.terminal second
      ≡ SelectedWindingPolarity.terminal first

-- This is a genuine implication from *evidence-bound assumptions*.
-- It establishes predicted sign parity only, not voltage magnitude.
pairedCoilsPredictedSignAgreement :
  ∀ {design} (pair : OppositePoleAndWinding design) →
  Polarity.effectiveSign
    (SelectedWindingPolarity.pole
      (OppositePoleAndWinding.second pair))
    (SelectedWindingPolarity.winding
      (OppositePoleAndWinding.second pair))
    (SelectedWindingPolarity.terminal
      (OppositePoleAndWinding.second pair))
  ≡
  Polarity.effectiveSign
    (SelectedWindingPolarity.pole
      (OppositePoleAndWinding.first pair))
    (SelectedWindingPolarity.winding
      (OppositePoleAndWinding.first pair))
    (SelectedWindingPolarity.terminal
      (OppositePoleAndWinding.first pair))
pairedCoilsPredictedSignAgreement pair
  rewrite OppositePoleAndWinding.oppositePoles pair
        | OppositePoleAndWinding.oppositeWindings pair
        | OppositePoleAndWinding.sameTerminalConvention pair =
    Polarity.pairedReversalPreservesSign
      (SelectedWindingPolarity.pole
        (OppositePoleAndWinding.first pair))
      (SelectedWindingPolarity.winding
        (OppositePoleAndWinding.first pair))
      (SelectedWindingPolarity.terminal
        (OppositePoleAndWinding.first pair))

-- Explicitly distinct outputs: a valid schematic topology proof can
-- predict a path or sign, but not attest actual performance.
record ExperimentClosure (design : DesignIdentity) : Set where
  constructor experimentClosure
  field
    measuredInputPower : Set
    measuredOutputPower : Set
    storageChangeAccounted : Set
    independentCalibration : Set
    uncertaintyBound : Set
