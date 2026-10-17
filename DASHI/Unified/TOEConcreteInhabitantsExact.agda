module DASHI.Unified.TOEConcreteInhabitantsExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Actual native mathematical inhabitant: selected atomic 2p^2 Coulomb model.
--
-- This is a TOE-local recut of the exact finite result carried by Agda PR
-- #1194.  The original reconstruction owns the hydrogenic/Gaunt integration
-- and gives F0=93/512, F2=45/512 and V_ee=(21/128) I_3.  Here we instantiate
-- the finite carrier and its C3/Hamiltonian commutation literally, rather than
-- storing only a Boolean that the payment exists.
------------------------------------------------------------------------

record Rational : Set where
  constructor rational
  field
    numerator : Nat
    denominator : Nat
open Rational public

zeroRational : Rational
zeroRational = rational 0 1

atomicP2CoulombEnergy : Rational
atomicP2CoulombEnergy = rational 21 128

atomicP2SlaterF0 : Rational
atomicP2SlaterF0 = rational 93 512

atomicP2SlaterF2 : Rational
atomicP2SlaterF2 = rational 45 512

data AtomicP2Basis : Set where
  p2NegZero : AtomicP2Basis
  p2NegPos : AtomicP2Basis
  p2ZeroPos : AtomicP2Basis

atomicP2C3 : AtomicP2Basis → AtomicP2Basis
atomicP2C3 p2NegZero = p2ZeroPos
atomicP2C3 p2NegPos = p2NegZero
atomicP2C3 p2ZeroPos = p2NegPos

atomicP2C3OrderThree :
  (x : AtomicP2Basis) →
  atomicP2C3 (atomicP2C3 (atomicP2C3 x)) ≡ x
atomicP2C3OrderThree p2NegZero = refl
atomicP2C3OrderThree p2NegPos = refl
atomicP2C3OrderThree p2ZeroPos = refl

atomicP2CoulombMatrix : AtomicP2Basis → AtomicP2Basis → Rational
atomicP2CoulombMatrix p2NegZero p2NegZero = atomicP2CoulombEnergy
atomicP2CoulombMatrix p2NegZero p2NegPos = zeroRational
atomicP2CoulombMatrix p2NegZero p2ZeroPos = zeroRational
atomicP2CoulombMatrix p2NegPos p2NegZero = zeroRational
atomicP2CoulombMatrix p2NegPos p2NegPos = atomicP2CoulombEnergy
atomicP2CoulombMatrix p2NegPos p2ZeroPos = zeroRational
atomicP2CoulombMatrix p2ZeroPos p2NegZero = zeroRational
atomicP2CoulombMatrix p2ZeroPos p2NegPos = zeroRational
atomicP2CoulombMatrix p2ZeroPos p2ZeroPos = atomicP2CoulombEnergy

atomicP2CoulombC3Invariant :
  (a b : AtomicP2Basis) →
  atomicP2CoulombMatrix (atomicP2C3 a) (atomicP2C3 b)
  ≡ atomicP2CoulombMatrix a b
atomicP2CoulombC3Invariant p2NegZero p2NegZero = refl
atomicP2CoulombC3Invariant p2NegZero p2NegPos = refl
atomicP2CoulombC3Invariant p2NegZero p2ZeroPos = refl
atomicP2CoulombC3Invariant p2NegPos p2NegZero = refl
atomicP2CoulombC3Invariant p2NegPos p2NegPos = refl
atomicP2CoulombC3Invariant p2NegPos p2ZeroPos = refl
atomicP2CoulombC3Invariant p2ZeroPos p2NegZero = refl
atomicP2CoulombC3Invariant p2ZeroPos p2NegPos = refl
atomicP2CoulombC3Invariant p2ZeroPos p2ZeroPos = refl

record AtomicP2HamiltonianInhabitant : Set where
  field
    basis : Set
    c3 : basis → basis
    c3OrderThree : (x : basis) → c3 (c3 (c3 x)) ≡ x
    matrixElement : basis → basis → Rational
    c3HamiltonianInvariant :
      (a b : basis) → matrixElement (c3 a) (c3 b) ≡ matrixElement a b
    sourceOwner : String
    completeAtomPromoted : Bool
    completeAtomPromotedIsFalse : completeAtomPromoted ≡ false
open AtomicP2HamiltonianInhabitant public

canonicalAtomicP2HamiltonianInhabitant : AtomicP2HamiltonianInhabitant
canonicalAtomicP2HamiltonianInhabitant =
  record
    { basis = AtomicP2Basis
    ; c3 = atomicP2C3
    ; c3OrderThree = atomicP2C3OrderThree
    ; matrixElement = atomicP2CoulombMatrix
    ; c3HamiltonianInvariant = atomicP2CoulombC3Invariant
    ; sourceOwner =
        "Agda PR #1194 / AtomicPeriodicTable369P2CoulombExecutionExact: selected common-spin hydrogenic 2p^2 projected Coulomb carrier"
    ; completeAtomPromoted = false
    ; completeAtomPromotedIsFalse = refl
    }

------------------------------------------------------------------------
-- Cross-branch formal inhabitants.
--
-- These records point at actual constructed theorem values on sibling Lean
-- branches.  They are inhabitants of an imported-formal-inhabitant type here;
-- they are deliberately NOT Agda proof terms and do not pay physical identity.
------------------------------------------------------------------------

data InhabitantAuthority : Set where
  nativeAgdaInhabitant : InhabitantAuthority
  importedFormalInhabitant : InhabitantAuthority
  calibratedPhysicalInhabitant : InhabitantAuthority

record FormalInhabitantReceipt : Set where
  field
    prover : String
    repository : String
    pullRequest : Nat
    headCommit : String
    moduleName : String
    declaration : String
    propositionScope : String
    authority : InhabitantAuthority
    importedAsAgdaTheorem : Bool
    importedAsAgdaTheoremIsFalse : importedAsAgdaTheorem ≡ false
open FormalInhabitantReceipt public

lean68RTInhabitant : FormalInhabitantReceipt
lean68RTInhabitant =
  record
    { prover = "Lean4"
    ; repository = "chboishabba/dashi_lean4"
    ; pullRequest = 68
    ; headCommit = "1b3772daa785d29f119e1a8ce92764819e12b941"
    ; moduleName = "Synthesis.TerminalConcreteInstantiation"
    ; declaration = "canonicalTerminalRT"
    ; propositionScope =
        "For every cut depth k, the concrete corrected independent-Bell tree has actualEntropy = actualCutEntropy."
    ; authority = importedFormalInhabitant
    ; importedAsAgdaTheorem = false
    ; importedAsAgdaTheoremIsFalse = refl
    }

lean68JacobsonInhabitant : FormalInhabitantReceipt
lean68JacobsonInhabitant =
  record
    { prover = "Lean4"
    ; repository = "chboishabba/dashi_lean4"
    ; pullRequest = 68
    ; headCommit = "1b3772daa785d29f119e1a8ce92764819e12b941"
    ; moduleName = "Synthesis.TerminalConcreteInstantiation"
    ; declaration = "canonicalTerminalVacuumEinstein"
    ; propositionScope =
        "Concrete flat-vacuum Jacobson benchmark: Einstein+Lambda equality with Lambda=0, together with recovered-Lambda constancy and SI/CODATA calibration metadata."
    ; authority = importedFormalInhabitant
    ; importedAsAgdaTheorem = false
    ; importedAsAgdaTheoremIsFalse = refl
    }

lean73CMInhabitant : FormalInhabitantReceipt
lean73CMInhabitant =
  record
    { prover = "Lean4"
    ; repository = "chboishabba/dashi_lean4"
    ; pullRequest = 73
    ; headCommit = "4dde2b77cbdb76bdb21db852966db2ffa0ca88d3"
    ; moduleName = "Dashi.EisensteinJZeroPointCMExact"
    ; declaration = "omegaPointEndomorphism"
    ; propositionScope =
        "Actual order-three additive endomorphism of the nonsingular j=0 elliptic point group over Q(omega), preserving the same cubic equation and group law."
    ; authority = importedFormalInhabitant
    ; importedAsAgdaTheorem = false
    ; importedAsAgdaTheoremIsFalse = refl
    }

record TOEConcreteInhabitantBundle : Set where
  field
    atomicHamiltonian : AtomicP2HamiltonianInhabitant
    rtFormalInhabitant : FormalInhabitantReceipt
    jacobsonFormalInhabitant : FormalInhabitantReceipt
    cmFormalInhabitant : FormalInhabitantReceipt
    physicalSameObjectClosureProvided : Bool
    physicalSameObjectClosureProvidedIsFalse :
      physicalSameObjectClosureProvided ≡ false
open TOEConcreteInhabitantBundle public

canonicalTOEConcreteInhabitantBundle : TOEConcreteInhabitantBundle
canonicalTOEConcreteInhabitantBundle =
  record
    { atomicHamiltonian = canonicalAtomicP2HamiltonianInhabitant
    ; rtFormalInhabitant = lean68RTInhabitant
    ; jacobsonFormalInhabitant = lean68JacobsonInhabitant
    ; cmFormalInhabitant = lean73CMInhabitant
    ; physicalSameObjectClosureProvided = false
    ; physicalSameObjectClosureProvidedIsFalse = refl
    }
