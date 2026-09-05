module DASHI.Physics.Plasma.MHDInvariantFibreBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- MHD INVARIANT FIBRES
--
-- Kinetic helicity, magnetic helicity and cross helicity are distinct
-- observables living over the same fluid/plasma state.  Sharing a theorem
-- shape does not identify their carriers, hypotheses or conservation laws.
------------------------------------------------------------------------

data InvariantKind : Set where
  kineticHelicity
  magneticHelicity
  crossHelicity
  totalEnergy
  : InvariantKind

record MHDStateFibre : Set₁ where
  constructor mhd-state-fibre
  field
    BaseState : Set
    VelocityField : Set
    MagneticField : Set
    VectorPotential : Set
    DensityField : Set
    PressureField : Set
    CurrentField : Set
    base : BaseState
    velocity : VelocityField
    magnetic : MagneticField
    vectorPotential : VectorPotential
    density : DensityField
    pressure : PressureField
    current : CurrentField
    stateReference : String

open MHDStateFibre public

record InvariantObserver (state : MHDStateFibre) : Set₁ where
  constructor invariant-observer
  field
    Value : Set
    kind : InvariantKind
    observe : Value
    definitionReference : String

open InvariantObserver public

record IdealInvariantReceipt
    (state : MHDStateFibre)
    (observer : InvariantObserver state) : Set₁ where
  constructor ideal-invariant-receipt
  field
    DomainBoundaryConditions : Set
    RegularityConditions : Set
    IdealEvolutionConditions : Set
    conservedAlongIdealFlow : Set
    receiptReference : String

open IdealInvariantReceipt public

record DissipativeInvariantBudget
    (state : MHDStateFibre)
    (observer : InvariantObserver state) : Set₁ where
  constructor dissipative-invariant-budget
  field
    DissipativeTerm : Set
    BoundaryFluxTerm : Set
    ProductionOrConversionTerm : Set
    balanceLaw : Set
    budgetReference : String

open DissipativeInvariantBudget public

------------------------------------------------------------------------
-- BIDI boundary.
------------------------------------------------------------------------

record MHDInvariantBoundary : Set where
  constructor mhd-invariant-boundary
  field
    kineticHelicityIsMagneticHelicity : Bool
    kineticHelicityIsMagneticHelicityIsFalse :
      kineticHelicityIsMagneticHelicity ≡ false

    magneticHelicityIsCrossHelicity : Bool
    magneticHelicityIsCrossHelicityIsFalse :
      magneticHelicityIsCrossHelicity ≡ false

    navierStokesHelicityReceiptProvesMagneticHelicityConservation : Bool
    navierStokesHelicityReceiptProvesMagneticHelicityConservationIsFalse :
      navierStokesHelicityReceiptProvesMagneticHelicityConservation ≡ false

    sharedTransportShapeMayBeReused : Bool
    sharedTransportShapeMayBeReusedIsTrue :
      sharedTransportShapeMayBeReused ≡ true

    localInvariantReceiptNeedsLocalHypotheses : Bool
    localInvariantReceiptNeedsLocalHypothesesIsTrue :
      localInvariantReceiptNeedsLocalHypotheses ≡ true

canonicalMHDInvariantBoundary : MHDInvariantBoundary
canonicalMHDInvariantBoundary =
  mhd-invariant-boundary
    false refl
    false refl
    false refl
    true refl
    true refl
