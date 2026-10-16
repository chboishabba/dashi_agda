module DASHI.Moonshine.Monster3BSchrodingerLiteralCharacterReceiptExact where

------------------------------------------------------------------------
-- LITERAL SCHRODINGER CHARACTER: EXECUTABLE SAME-MODEL RECEIPT
--
-- The repository action convention is
--
--   rho(a,b,c) f(x) = zeta^(c + b.(x-a)) f(x-a).
--
-- Therefore on the literal delta basis
--
--   rho(a,b,c) delta_y = zeta^(c + b.y) delta_(y+a).
--
-- The companion executable audit
--
--   scripts/verify_monster3b_schrodinger_character.py
--
-- derives, rather than assumes, the character:
--
--   a != 0       -> no fixed delta basis point -> trace 0
--   a = 0,b != 0 -> zeta^c sum_y zeta^(b.y) = 0
--   a = b = 0    -> 729 zeta^c.
--
-- It brute-forces all 729 additive-character sums on F3^6 and exhaustively
-- classifies all 3^13 = 1,594,323 Heisenberg coordinates.  The resulting
-- four-value character is exactly the canonical nonlinear zeta signature
-- already used by Monster3BKernelCharacterCriterionExact.
--
-- AUTHORITY BOUNDARY
-- ------------------
-- This is exact executable evidence for the LITERAL MODEL action.  It does not
-- create an Agda-kernel trace theorem, a Mathlib FDRep object, or an actual
-- Monster W_zeta constituent.  Those remain separately proof-relevant.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)

scriptPath : String
scriptPath = "scripts/verify_monster3b_schrodinger_character.py"

receiptPath : String
receiptPath = "outputs/monster3b_schrodinger_literal_character_20261016.json"

basisDegree : Nat
basisDegree = 729

heisenbergOrder : Nat
heisenbergOrder = 1594323

identityCount : Nat
identityCount = 1

centralZetaCount : Nat
centralZetaCount = 1

centralZetaSquaredCount : Nat
centralZetaSquaredCount = 1

noncentralCount : Nat
noncentralCount = 1594320

nonzeroTranslationCount : Nat
nonzeroTranslationCount = 1592136

pureNonzeroModulationCount : Nat
pureNonzeroModulationCount = 2184

noncentralPartitionCloses :
  nonzeroTranslationCount + pureNonzeroModulationCount ≡ noncentralCount
noncentralPartitionCloses = refl

record Boundary : Set where
  constructor boundary
  field
    literalRepositoryActionConventionConsumed : Bool
    all729ModulationCharacterSumsVerified : Bool
    all1594323HeisenbergCoordinatesClassified : Bool
    identityTrace729PaidExecutable : Bool
    centralZetaTrace729PaidExecutable : Bool
    centralZetaSquaredTrace729PaidExecutable : Bool
    noncentralTraceZeroPaidExecutable : Bool
    literalCharacterMatchesCanonicalHeisenbergSignatureExecutable : Bool

    agdaKernelTraceDerivationPaidHere : Bool
    commonFDRepTransportPaidHere : Bool
    actualMonsterConstituentAttachedHere : Bool
    executableReceiptPromotesActualMonsterIdentity : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary
  true true true true true true true true
  false false false false
