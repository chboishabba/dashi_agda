module DASHI.Moonshine.PenumbralDiscriminantProperty where

-- Conjecture 4.3-style discriminant property.  The quadratic field controlling
-- an irreducible constituent's trace is related to the discriminant indexing
-- the graded piece.  This is deliberately isolated from the proven existence
-- of the virtual graded modules.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)

record DiscriminantPropertyArithmetic : Set₁ where
  field
    Discriminant : Set
    multiply : Discriminant → Nat → Discriminant
    square : Nat → Nat
    CoprimeTo : Nat → Discriminant → Set
    CongruentSquareModulo : Discriminant → Nat → Nat → Set
    absoluteOrder : Discriminant → Nat

record PenumbralDiscriminantProperty
  (arithmetic : DiscriminantPropertyArithmetic)
  (G Module Constituent TraceValue QuadraticField : Set) : Setω where
  field
    D0 d D1 : DiscriminantPropertyArithmetic.Discriminant arithmetic
    level residue f : Nat

    fCoprimeToD0 :
      DiscriminantPropertyArithmetic.CoprimeTo arithmetic f D0

    D : DiscriminantPropertyArithmetic.Discriminant arithmetic
    discriminantFactorization :
      D ≡ DiscriminantPropertyArithmetic.multiply arithmetic d
        (DiscriminantPropertyArithmetic.square arithmetic f)

    residueCongruence :
      DiscriminantPropertyArithmetic.CongruentSquareModulo arithmetic
        D residue level

    groupElement : G
    orderIsQuadraticDiscriminantMagnitude : Set

    gradedModule : Module
    irreducibleConstituent : Constituent
    constituentOccurs : Set
    constituentIrreducible : Set

    traceValue : TraceValue
    traceIsConstituentTrace : Set

    quadraticField : QuadraticField
    fieldIsD1QuadraticField : Set
    traceLiesInQuadraticField : Set
    traceIsIrrational : Set

record DiscriminantPropertyStatus : Set where
  field
    observedInSpecifiedCases : ⊤
    generalStatementRemainsConjectural : ⊤
    notNeededForModuleExistenceTheorems : ⊤
    noFieldClaimFromCoefficientIntegrality : ⊤

penumbralDiscriminantPropertyStatus : DiscriminantPropertyStatus
penumbralDiscriminantPropertyStatus = record
  { observedInSpecifiedCases = tt
  ; generalStatementRemainsConjectural = tt
  ; notNeededForModuleExistenceTheorems = tt
  ; noFieldClaimFromCoefficientIntegrality = tt
  }
