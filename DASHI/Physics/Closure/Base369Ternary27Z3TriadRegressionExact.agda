module DASHI.Physics.Closure.Base369Ternary27Z3TriadRegressionExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Wikimedia.Base369IntegerLatticeZ3WrongTypeSnowballExact as Embed

------------------------------------------------------------------------
-- FINITE TERNARY-27 / Z^3 TRIAD REGRESSION
--
-- On one coordinate a,b in {-1,0,+1}, the condition a+b in {-1,0,+1}
-- excludes only (-1,-1) and (+1,+1). Hence there are seven ordered
-- coordinate-level resonant choices. Three coordinates separate, so the raw
-- bounded ordered p+q=k incidence count is 7^3 = 343.
--
-- This is the primitive resonance/cutoff layer only. Nonzero-mode conditions,
-- reality/conjugacy quotienting, phase, polarisation/helicity, Schur weights
-- and physical amplitudes remain downstream filters exactly as in the existing
-- PhysicalTriadEnumeration owner.
------------------------------------------------------------------------

data SignedOne : Set where
  negOne zeroOne posOne : SignedOne

data ResonantCoordinateChoice : Set where
  negPosToZero : ResonantCoordinateChoice
  negZeroToNeg : ResonantCoordinateChoice
  zeroNegToNeg : ResonantCoordinateChoice
  zeroZeroToZero : ResonantCoordinateChoice
  zeroPosToPos : ResonantCoordinateChoice
  posZeroToPos : ResonantCoordinateChoice
  posNegToZero : ResonantCoordinateChoice

coordinateChoiceCount : Nat
coordinateChoiceCount = 7

record TernaryBoundedTriadCode : Set where
  constructor ternary-bounded-triad-code
  field
    xChoice : ResonantCoordinateChoice
    yChoice : ResonantCoordinateChoice
    zChoice : ResonantCoordinateChoice
open TernaryBoundedTriadCode public

rawOrderedBoundedTriadCount : Nat
rawOrderedBoundedTriadCount = coordinateChoiceCount * coordinateChoiceCount * coordinateChoiceCount

rawOrderedBoundedTriadCountIs343 : rawOrderedBoundedTriadCount ≡ 343
rawOrderedBoundedTriadCountIs343 = refl

------------------------------------------------------------------------
-- Exact interpretation into coordinate triples.
------------------------------------------------------------------------

record CoordinateIncidence : Set where
  constructor coordinate-incidence
  field
    left : SignedOne
    right : SignedOne
    output : SignedOne
open CoordinateIncidence public

choiceIncidence : ResonantCoordinateChoice → CoordinateIncidence
choiceIncidence negPosToZero = coordinate-incidence negOne posOne zeroOne
choiceIncidence negZeroToNeg = coordinate-incidence negOne zeroOne negOne
choiceIncidence zeroNegToNeg = coordinate-incidence zeroOne negOne negOne
choiceIncidence zeroZeroToZero = coordinate-incidence zeroOne zeroOne zeroOne
choiceIncidence zeroPosToPos = coordinate-incidence zeroOne posOne posOne
choiceIncidence posZeroToPos = coordinate-incidence posOne zeroOne posOne
choiceIncidence posNegToZero = coordinate-incidence posOne negOne zeroOne

record TriadCoordinateProduct : Set where
  constructor triad-coordinate-product
  field
    x : CoordinateIncidence
    y : CoordinateIncidence
    z : CoordinateIncidence
open TriadCoordinateProduct public

codeToCoordinateProduct : TernaryBoundedTriadCode → TriadCoordinateProduct
codeToCoordinateProduct code =
  triad-coordinate-product
    (choiceIncidence (xChoice code))
    (choiceIncidence (yChoice code))
    (choiceIncidence (zChoice code))

------------------------------------------------------------------------
-- Same carrier seam with existing Base369/Z^3 and NS enumeration owners.
------------------------------------------------------------------------

ternaryCubeStateCountIs27 : Geometry.hypervoxelStateCount ≡ 27
ternaryCubeStateCountIs27 = Geometry.hypervoxelStateCountIs27

originEmbeddingStillExact :
  Embed.ternaryPointToZ3 Geometry.origin ≡ Z3.zeroMode
originEmbeddingStillExact = Embed.originMapsToZeroMode

record Ternary27TriadRegressionReceipt : Set where
  constructor ternary27-triad-regression-receipt
  field
    finiteModeCarrierReference : String
    ambientLatticeReference : String
    existingEnumerationReference : String
    coordinateResonanceChoiceCount : Nat
    productDimension : Nat
    rawOrderedIncidenceCount : Nat
    rawCountProof : rawOrderedIncidenceCount ≡ 343
    rawResonanceAndCutoffSeparatedFromNonzero : Bool
    nonzeroTriadCountPaid : Bool
    executableEnumerationLengthEquals343Paid : Bool
    phasePolarisationQuotientApplied : Bool
    oeisIdentityCreatesNSMeaning : Bool
open Ternary27TriadRegressionReceipt public

canonicalTernary27TriadRegressionReceipt : Ternary27TriadRegressionReceipt
canonicalTernary27TriadRegressionReceipt =
  ternary27-triad-regression-receipt
    "Base369 Ternary27Point / cutoff N=1 coordinate cube"
    "NSIntegerFourierLattice.FourierMode = Z^3"
    "NSTriadKNPhysicalTriadEnumeration.physicalTriadEnumeration 1"
    7 3 rawOrderedBoundedTriadCount rawOrderedBoundedTriadCountIs343
    true false false false false

------------------------------------------------------------------------
-- Regression target: next payment is to identify the 343 combinatorial codes
-- bijectively with the literal executable physicalTriadEnumeration 1 list.
------------------------------------------------------------------------

record TriadRegressionFrontier : Set where
  constructor triad-regression-frontier
  field
    finiteCubeEmbeddingPaid : Bool
    coordinateCombinatoricsPaid : Bool
    rawCount343Paid : Bool
    literalEnumerationBijectionPaid : Bool
    literalEnumerationLengthPaid : Bool
    nonzeroSubcountPaid : Bool
    conjugacyOrbitCountPaid : Bool
    schurWeightedRegressionPaid : Bool
open TriadRegressionFrontier public

currentTriadRegressionFrontier : TriadRegressionFrontier
currentTriadRegressionFrontier =
  triad-regression-frontier true true true false false false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data Raw343EqualsNonzeroPhysicalTriads : Set where
data Raw343EqualsHelicityResolvedStates : Set where
data FiniteRegressionProvesUniformSchurBound : Set where
data OEIS343CreatesTriadTheorem : Set where

rawCountIsNotNonzeroCount : Raw343EqualsNonzeroPhysicalTriads → ⊥
rawCountIsNotNonzeroCount ()

rawCountIsNotHelicityStateCount : Raw343EqualsHelicityResolvedStates → ⊥
rawCountIsNotHelicityStateCount ()

finiteRegressionDoesNotProveUniformSchur : FiniteRegressionProvesUniformSchurBound → ⊥
finiteRegressionDoesNotProveUniformSchur ()

oeisDoesNotCreateTriadTheorem : OEIS343CreatesTriadTheorem → ⊥
oeisDoesNotCreateTriadTheorem ()

physicalEnumerationSoundnessRetained :
  ∀ {τ} →
  τ Physical.∈ Physical.physicalTriadEnumeration 1 →
  Z3.addMode (Physical.p τ) (Physical.q τ) ≡ Physical.k τ
physicalEnumerationSoundnessRetained = Physical.physicalTriadEnumerationResonanceSound
