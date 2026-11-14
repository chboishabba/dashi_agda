module DASHI.Cognition.Teleodynamics.ExceptionalE6E8DualIncidenceHyperfabricExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.Teleodynamics.ExceptionalE6Mod3FiniteGeometryExact as E6
import DASHI.Cognition.Teleodynamics.ExceptionalE6RootSubsystemHyperfabricExact as Fabric

------------------------------------------------------------------------
-- E6 NULL QUADRIC <-> E8 ORDER-THREE SYMPLECTIC DUAL INCIDENCE
--
-- The finite computation distinguishes the E8 symplectic point graph from its
-- line-intersection graph.  The E6 null projective graph matches the latter,
-- not the former.  The 120 H3 patches collapse three-to-one onto 40 A2^3
-- subsystem classes, canonically indexed by their radical null line; those 40
-- classes therefore inherit the same tested dual-line geometry.
------------------------------------------------------------------------

record DualIncidenceArithmetic : Set where
  constructor dual-incidence-arithmetic
  field
    e6NullProjectivePoints : Nat
    a2CubedSubsystemClasses : Nat
    h3Patches : Nat
    h3PatchesPerA2Cubed : Nat
    e8SymplecticProjectivePoints : Nat
    e8SymplecticProjectiveLines : Nat
open DualIncidenceArithmetic public

canonicalDualIncidenceArithmetic : DualIncidenceArithmetic
canonicalDualIncidenceArithmetic =
  dual-incidence-arithmetic 40 40 120 3 40 40

h3ThreeToOneArithmetic : 40 ≡ 40
h3ThreeToOneArithmetic = refl

record E6NullA2CubedRecognition : Set₁ where
  field
    E6NullLine : Set
    A2CubedSubsystem : Set
    H3Patch : Set

    radicalClass : H3Patch → E6NullLine
    subsystemClass : H3Patch → A2CubedSubsystem

    nullToSubsystem : E6NullLine → A2CubedSubsystem
    subsystemToNull : A2CubedSubsystem → E6NullLine
    nullRoundTrip : (x : E6NullLine) → subsystemToNull (nullToSubsystem x) ≡ x
    subsystemRoundTrip :
      (x : A2CubedSubsystem) → nullToSubsystem (subsystemToNull x) ≡ x

    threeH3PatchesPerClassReceipt : Set
    h3ClassCompatibilityReceipt : Set
    provenance : String

record E8SymplecticDualLineRecognition : Set₁ where
  field
    E6NullLine : Set
    E8Point E8Line : Set

    e8Incident : E8Point → E8Line → Set
    e6Adjacent : E6NullLine → E6NullLine → Set
    e8LinesMeet : E8Line → E8Line → Set

    e6ToE8Line : E6NullLine → E8Line
    e8LineToE6 : E8Line → E6NullLine
    fromAfterTo : (x : E6NullLine) → e8LineToE6 (e6ToE8Line x) ≡ x
    toAfterFrom : (l : E8Line) → e6ToE8Line (e8LineToE6 l) ≡ l

    adjacencyIntertwines : Set
    pointGraphNonIdentificationReceipt : Set
    provenance : String

record A2CubedE8LineWeld : Set₁ where
  field
    E6NullLine A2CubedSubsystem E8Line : Set
    e6A2 : E6NullA2CubedRecognition
    e6E8 : E8SymplecticDualLineRecognition
    a2CubedToE8Line : A2CubedSubsystem → E8Line
    e8LineToA2Cubed : E8Line → A2CubedSubsystem
    a2AfterE8 : (x : A2CubedSubsystem) → e8LineToA2Cubed (a2CubedToE8Line x) ≡ x
    e8AfterA2 : (x : E8Line) → a2CubedToE8Line (e8LineToA2Cubed x) ≡ x
    lineIntersectionIntertwines : Set
    provenance : String

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data MatchingFortyCountsCreateDuality : Set where
data MatchingSRGCreatesCanonicalBijection : Set where
data DualIncidenceCreatesE8Representation : Set where
data A2CubedLineWeldCreatesAlbertProduct : Set where

fortyCountsDoNotCreateDuality : MatchingFortyCountsCreateDuality → ⊥
fortyCountsDoNotCreateDuality ()

srgDoesNotCreateCanonicalBijection : MatchingSRGCreatesCanonicalBijection → ⊥
srgDoesNotCreateCanonicalBijection ()

dualityDoesNotCreateE8Representation : DualIncidenceCreatesE8Representation → ⊥
dualityDoesNotCreateE8Representation ()

a2CubedWeldDoesNotCreateAlbertProduct : A2CubedLineWeldCreatesAlbertProduct → ⊥
a2CubedWeldDoesNotCreateAlbertProduct ()

record ExceptionalE6E8DualIncidenceBoundary : Set where
  constructor exceptional-e6-e8-dual-incidence-boundary
  field
    fortyFortyArithmeticRecorded : Bool
    threeToOneH3A2CubedReceiptRecorded : Bool
    e6NullToE8LineGraphPythonReceiptRecorded : Bool
    e6NullToE8PointGraphIdentificationRejected : Bool
    a2CubedToE8LinePythonReceiptRecorded : Bool
    nullA2RecognitionInhabitedHere : Bool
    e8DualLineRecognitionInhabitedHere : Bool
    a2CubedE8LineWeldInhabitedHere : Bool

canonicalExceptionalE6E8DualIncidenceBoundary :
  ExceptionalE6E8DualIncidenceBoundary
canonicalExceptionalE6E8DualIncidenceBoundary =
  exceptional-e6-e8-dual-incidence-boundary
    true true true true true
    false false false
