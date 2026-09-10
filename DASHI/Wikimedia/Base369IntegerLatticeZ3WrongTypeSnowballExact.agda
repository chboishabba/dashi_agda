module DASHI.Wikimedia.Base369IntegerLatticeZ3WrongTypeSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Integer.Base using (ℤ; +_; -_)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.WikipediaAllPairsPrunedMergeSnowballExact as AllPairs

------------------------------------------------------------------------
-- BASE369 TERNARY-27 <-> INTEGER-LATTICE Z^3 SNOWBALL
--
-- Repo-native "Z3" in the Navier-Stokes lane means the exact integer Fourier
-- lattice Z^3, not the Microsoft Z3 SMT solver and not the Zuse Z3 computer.
--
-- External coordinates inspected 2026-09-10:
--   Integer lattice: enwiki oldid 1330716805; Wikidata Q1252145.
--   Z3 Theorem Prover: Wikidata Q85816952.
--   Zuse Z3 computer: Wikidata Q222419.
--
-- The Base369 ternary cube {-1,0,+1}^3 is embedded below as a finite bounded
-- subset of the repo's ambient integer Fourier lattice Z^3. This is a genuine
-- carrier relationship, unlike the external Z3 name collisions.
------------------------------------------------------------------------

integerLatticeQid : Identity.ExternalIdentityDemand
integerLatticeQid = Identity.mkOptionalIdentityDemand
  "Base369 / integer-Fourier-lattice snowball"
  "integer lattice identity"
  "integer lattice"
  Identity.wikidataQid
  (Identity.verified "Q1252145" "enwiki Integer lattice oldid 1330716805 inspected 2026-09-10")

integerLatticeWikipedia : Identity.ExternalIdentityDemand
integerLatticeWikipedia = Identity.mkOptionalIdentityDemand
  "Base369 / integer-Fourier-lattice snowball"
  "integer lattice Wikipedia revision coordinate"
  "Integer lattice"
  Identity.canonicalURL
  (Identity.verified
    "https://en.wikipedia.org/w/index.php?title=Integer_lattice&oldid=1330716805"
    "current retrieved revision inspected 2026-09-10")

z3TheoremProverQid : Identity.ExternalIdentityDemand
z3TheoremProverQid = Identity.mkOptionalIdentityDemand
  "Z3 namespace WrongType snowball"
  "Microsoft Z3 theorem prover identity"
  "Z3 Theorem Prover"
  Identity.wikidataQid
  (Identity.verified "Q85816952" "Wikidata inspected 2026-09-10")

zuseZ3Qid : Identity.ExternalIdentityDemand
zuseZ3Qid = Identity.mkOptionalIdentityDemand
  "Z3 namespace WrongType snowball"
  "Zuse Z3 computer identity"
  "Z3 computer"
  Identity.wikidataQid
  (Identity.verified "Q222419" "Wikidata inspected 2026-09-10")

------------------------------------------------------------------------
-- Exact finite-cube embedding into the ambient integer Fourier lattice.
------------------------------------------------------------------------

tritToInteger : SSP.SSPTrit → ℤ
tritToInteger SSP.sspNegOne = - (+ 1)
tritToInteger SSP.sspZero = + 0
tritToInteger SSP.sspPosOne = + 1

ternaryPointToZ3 : Geometry.Ternary27Point → Z3.FourierMode
ternaryPointToZ3 (Geometry.ternary27Point x y z) =
  Z3.mode (tritToInteger x) (tritToInteger y) (tritToInteger z)

originMapsToZeroMode : ternaryPointToZ3 Geometry.origin ≡ Z3.zeroMode
originMapsToZeroMode = refl

negativeCornerMapsExactly :
  ternaryPointToZ3 Geometry.negativeCorner ≡
  Z3.mode (- (+ 1)) (- (+ 1)) (- (+ 1))
negativeCornerMapsExactly = refl

positiveCornerMapsExactly :
  ternaryPointToZ3 Geometry.positiveCorner ≡
  Z3.mode (+ 1) (+ 1) (+ 1)
positiveCornerMapsExactly = refl

record TernaryCubeIntegerLatticeEmbedding : Set where
  constructor ternary-cube-integer-lattice-embedding
  field
    finiteCarrierReference : String
    ambientCarrierReference : String
    finiteStateCount : String
    embeddingReference : String
    originPreserved : Bool
    allFiniteCoordinatesAreIntegers : Bool
    finiteCubeEqualsWholeIntegerLattice : Bool
    embeddingCreatesFourierPhysics : Bool
open TernaryCubeIntegerLatticeEmbedding public

canonicalTernaryCubeIntegerLatticeEmbedding : TernaryCubeIntegerLatticeEmbedding
canonicalTernaryCubeIntegerLatticeEmbedding = ternary-cube-integer-lattice-embedding
  "DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact.Ternary27Point"
  "DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode = Z^3"
  "3^3 = 27"
  "ternaryPointToZ3"
  true true false false

------------------------------------------------------------------------
-- Namespace / WrongType classification.
------------------------------------------------------------------------

data Z3ExternalMeaning : Set where
  integerLatticeZCubed : Z3ExternalMeaning
  microsoftSMTSolver : Z3ExternalMeaning
  zuseElectromechanicalComputer : Z3ExternalMeaning
  unresolvedZ3Meaning : Z3ExternalMeaning

record Z3NameResolutionReceipt : Set where
  constructor z3-name-resolution-receipt
  field
    surfaceToken : String
    requestedConsumer : String
    resolvedMeaning : Z3ExternalMeaning
    identityReference : String
    wrongTypeChecked : Bool
    sameObjectAsRepoIntegerLattice : Bool
    mayEnterMathematicalCarrierAlgebra : Bool
open Z3NameResolutionReceipt public

repoZ3Resolution : Z3NameResolutionReceipt
repoZ3Resolution = z3-name-resolution-receipt
  "Z3"
  "DASHI Navier-Stokes Fourier-mode carrier"
  integerLatticeZCubed
  "NSIntegerFourierLattice / Q1252145"
  true true true

solverZ3Resolution : Z3NameResolutionReceipt
solverZ3Resolution = z3-name-resolution-receipt
  "Z3"
  "external software identity"
  microsoftSMTSolver
  "Q85816952"
  true false false

computerZ3Resolution : Z3NameResolutionReceipt
computerZ3Resolution = z3-name-resolution-receipt
  "Z3"
  "historical computer identity"
  zuseElectromechanicalComputer
  "Q222419"
  true false false

------------------------------------------------------------------------
-- All-pairs implications.
------------------------------------------------------------------------

record Base369Z3AllPairsProjection : Set where
  constructor base369-z3-all-pairs-projection
  field
    ternaryCubeVsIntegerLatticePairEligible : Bool
    ternaryCubeEmbeddingMayFastPathCarrierGate : Bool
    z3SolverNameCollisionHitsWrongTypeGate : Bool
    zuseComputerNameCollisionHitsWrongTypeGate : Bool
    externalNameCollisionDeletesCandidateHistory : Bool
    finiteCubeMaySnowballIntoAmbientLatticeAxis : Bool
    ambientLatticeMayBeUsedToCompareTriadClosure : Bool
    embeddingAloneCreatesNavierStokesClaim : Bool
open Base369Z3AllPairsProjection public

canonicalBase369Z3AllPairsProjection : Base369Z3AllPairsProjection
canonicalBase369Z3AllPairsProjection = base369-z3-all-pairs-projection
  true true true true false true true false

allPairsBoundary : AllPairs.WikipediaAllPairsBoundary
allPairsBoundary = AllPairs.canonicalWikipediaAllPairsBoundary

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data FiniteTernaryCubeEqualsZ3 : Set where
data IntegerEmbeddingCreatesPhysics : Set where
data Z3TokenCreatesSMTSolverIdentity : Set where
data Z3TokenCreatesComputerIdentity : Set where
data SolverQidCreatesIntegerLattice : Set where
data IntegerLatticeQidCreatesRepoTheorem : Set where

finiteCubeDoesNotEqualWholeLattice : FiniteTernaryCubeEqualsZ3 → ⊥
finiteCubeDoesNotEqualWholeLattice ()

embeddingDoesNotCreatePhysics : IntegerEmbeddingCreatesPhysics → ⊥
embeddingDoesNotCreatePhysics ()

z3TokenDoesNotCreateSolverIdentity : Z3TokenCreatesSMTSolverIdentity → ⊥
z3TokenDoesNotCreateSolverIdentity ()

z3TokenDoesNotCreateComputerIdentity : Z3TokenCreatesComputerIdentity → ⊥
z3TokenDoesNotCreateComputerIdentity ()

solverQidDoesNotCreateIntegerLattice : SolverQidCreatesIntegerLattice → ⊥
solverQidDoesNotCreateIntegerLattice ()

integerLatticeIdentityDoesNotCreateRepoTheorem : IntegerLatticeQidCreatesRepoTheorem → ⊥
integerLatticeIdentityDoesNotCreateRepoTheorem ()

record Base369IntegerLatticeZ3Boundary : Set where
  constructor base369-integer-lattice-z3-boundary
  field
    integerLatticeQidRecorded : Bool
    integerLatticeRevisionRecorded : Bool
    z3SolverQidRecorded : Bool
    zuseZ3QidRecorded : Bool
    finiteCubeEmbeddingRecorded : Bool
    z3NamespaceWrongTypeExplicit : Bool
    finiteVsInfiniteCarrierSeparated : Bool
    externalIdentityCreatesTheorem : Bool
open Base369IntegerLatticeZ3Boundary public

canonicalBase369IntegerLatticeZ3Boundary : Base369IntegerLatticeZ3Boundary
canonicalBase369IntegerLatticeZ3Boundary = base369-integer-lattice-z3-boundary
  true true true true true true true false
