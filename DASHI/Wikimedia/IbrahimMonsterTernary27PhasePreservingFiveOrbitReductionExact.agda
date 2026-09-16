module DASHI.Wikimedia.IbrahimMonsterTernary27PhasePreservingFiveOrbitReductionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Modes
import DASHI.Biology.SSP15ComplementPhaseProjectorExact as SSP15

------------------------------------------------------------------------
-- TERNARY-27 -> THREE PRESERVED PHASES x FIVE INNER ORBITS
--
-- The intended reduction is not a direct 27 -> 5 selector.
--
--   T^3 = T x T^2
--        -> T x (T^2 / global inner inversion)
--        = 3 x 5
--        = 15.
--
-- The outer ternary coordinate is retained as a phase label.  Only the inner
-- nine-state sheet is quotiented by simultaneous sign inversion.  This is
-- therefore deliberately distinct from quotienting all 27 states by global
-- inversion, whose finite runtime/orbit count is 14.
--
-- A separate finite indexing identifies the five inner orbit constructors with
-- the repository's five ComplementMode5 names.  That indexing is useful for
-- transporting the carrier into SSP15; it is NOT a semantic theorem that the
-- inversion orbits are D4 irreducible types or Monster modes.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Adapter between the two repository ternary carriers.
------------------------------------------------------------------------

sspToKernelTrit : SSP.SSPTrit → Triadic.KernelTrit
sspToKernelTrit SSP.sspNegOne = Triadic.negativeTrit
sspToKernelTrit SSP.sspZero = Triadic.zeroTrit
sspToKernelTrit SSP.sspPosOne = Triadic.positiveTrit

kernelToSSPTrit : Triadic.KernelTrit → SSP.SSPTrit
kernelToSSPTrit Triadic.negativeTrit = SSP.sspNegOne
kernelToSSPTrit Triadic.zeroTrit = SSP.sspZero
kernelToSSPTrit Triadic.positiveTrit = SSP.sspPosOne

sspKernelRoundTrip :
  (t : SSP.SSPTrit) → kernelToSSPTrit (sspToKernelTrit t) ≡ t
sspKernelRoundTrip SSP.sspNegOne = refl
sspKernelRoundTrip SSP.sspZero = refl
sspKernelRoundTrip SSP.sspPosOne = refl

kernelSSPRoundTrip :
  (t : Triadic.KernelTrit) → sspToKernelTrit (kernelToSSPTrit t) ≡ t
kernelSSPRoundTrip Triadic.negativeTrit = refl
kernelSSPRoundTrip Triadic.zeroTrit = refl
kernelSSPRoundTrip Triadic.positiveTrit = refl

negateSSP : SSP.SSPTrit → SSP.SSPTrit
negateSSP SSP.sspNegOne = SSP.sspPosOne
negateSSP SSP.sspZero = SSP.sspZero
negateSSP SSP.sspPosOne = SSP.sspNegOne

------------------------------------------------------------------------
-- 2. Exact phase-preserving quotient T^3 -> T x NineOrbit.
------------------------------------------------------------------------

PhaseOrbit15 : Set
PhaseOrbit15 = SSP.SSPTrit × Triadic.NineOrbit

innerSheet : Geometry.Ternary27Point → Triadic.NineSheet
innerSheet (Geometry.ternary27Point x y z) =
  sspToKernelTrit y , sspToKernelTrit z

reduce27ToPhaseOrbit15 : Geometry.Ternary27Point → PhaseOrbit15
reduce27ToPhaseOrbit15 (Geometry.ternary27Point x y z) =
  x , Triadic.quotientNine (sspToKernelTrit y , sspToKernelTrit z)

innerInvert27 : Geometry.Ternary27Point → Geometry.Ternary27Point
innerInvert27 (Geometry.ternary27Point x y z) =
  Geometry.ternary27Point x (negateSSP y) (negateSSP z)

reduce27InnerInversionInvariant :
  (p : Geometry.Ternary27Point) →
  reduce27ToPhaseOrbit15 (innerInvert27 p) ≡ reduce27ToPhaseOrbit15 p
reduce27InnerInversionInvariant
  (Geometry.ternary27Point x SSP.sspNegOne SSP.sspNegOne) = refl
reduce27InnerInversionInvariant
  (Geometry.ternary27Point x SSP.sspNegOne SSP.sspZero) = refl
reduce27InnerInversionInvariant
  (Geometry.ternary27Point x SSP.sspNegOne SSP.sspPosOne) = refl
reduce27InnerInversionInvariant
  (Geometry.ternary27Point x SSP.sspZero SSP.sspNegOne) = refl
reduce27InnerInversionInvariant
  (Geometry.ternary27Point x SSP.sspZero SSP.sspZero) = refl
reduce27InnerInversionInvariant
  (Geometry.ternary27Point x SSP.sspZero SSP.sspPosOne) = refl
reduce27InnerInversionInvariant
  (Geometry.ternary27Point x SSP.sspPosOne SSP.sspNegOne) = refl
reduce27InnerInversionInvariant
  (Geometry.ternary27Point x SSP.sspPosOne SSP.sspZero) = refl
reduce27InnerInversionInvariant
  (Geometry.ternary27Point x SSP.sspPosOne SSP.sspPosOne) = refl

canonicalLiftPhaseOrbit15 : PhaseOrbit15 → Geometry.Ternary27Point
canonicalLiftPhaseOrbit15 (phase , orbit) =
  Geometry.ternary27Point
    phase
    (kernelToSSPTrit (proj₁ (Triadic.canonicalNineRepresentative orbit)))
    (kernelToSSPTrit (proj₂ (Triadic.canonicalNineRepresentative orbit)))

reduceCanonicalLift :
  (lane : PhaseOrbit15) →
  reduce27ToPhaseOrbit15 (canonicalLiftPhaseOrbit15 lane) ≡ lane
reduceCanonicalLift (phase , Triadic.zeroOrbit) = refl
reduceCanonicalLift (phase , Triadic.firstAxisOrbit) = refl
reduceCanonicalLift (phase , Triadic.secondAxisOrbit) = refl
reduceCanonicalLift (phase , Triadic.equalSignOrbit) = refl
reduceCanonicalLift (phase , Triadic.oppositeSignOrbit) = refl

outerPhaseCount : Nat
outerPhaseCount = 3

innerNineStateCount : Nat
innerNineStateCount = 3 * 3

innerOrbitCount : Nat
innerOrbitCount = 5

phaseOrbitStateCount : Nat
phaseOrbitStateCount = outerPhaseCount * innerOrbitCount

innerNineStateCountIsNine : innerNineStateCount ≡ 9
innerNineStateCountIsNine = refl

phaseOrbitStateCountIsFifteen : phaseOrbitStateCount ≡ 15
phaseOrbitStateCountIsFifteen = refl

------------------------------------------------------------------------
-- 3. Finite indexing into the existing SSP15 carrier.
------------------------------------------------------------------------

orbitToComplementMode : Triadic.NineOrbit → Modes.ComplementMode5
orbitToComplementMode Triadic.zeroOrbit = Modes.mode09
orbitToComplementMode Triadic.firstAxisOrbit = Modes.mode18
orbitToComplementMode Triadic.secondAxisOrbit = Modes.mode27
orbitToComplementMode Triadic.equalSignOrbit = Modes.mode36
orbitToComplementMode Triadic.oppositeSignOrbit = Modes.mode45

complementModeToOrbit : Modes.ComplementMode5 → Triadic.NineOrbit
complementModeToOrbit Modes.mode09 = Triadic.zeroOrbit
complementModeToOrbit Modes.mode18 = Triadic.firstAxisOrbit
complementModeToOrbit Modes.mode27 = Triadic.secondAxisOrbit
complementModeToOrbit Modes.mode36 = Triadic.equalSignOrbit
complementModeToOrbit Modes.mode45 = Triadic.oppositeSignOrbit

orbitModeRoundTrip :
  (orbit : Triadic.NineOrbit) →
  complementModeToOrbit (orbitToComplementMode orbit) ≡ orbit
orbitModeRoundTrip Triadic.zeroOrbit = refl
orbitModeRoundTrip Triadic.firstAxisOrbit = refl
orbitModeRoundTrip Triadic.secondAxisOrbit = refl
orbitModeRoundTrip Triadic.equalSignOrbit = refl
orbitModeRoundTrip Triadic.oppositeSignOrbit = refl

modeOrbitRoundTrip :
  (mode : Modes.ComplementMode5) →
  orbitToComplementMode (complementModeToOrbit mode) ≡ mode
modeOrbitRoundTrip Modes.mode09 = refl
modeOrbitRoundTrip Modes.mode18 = refl
modeOrbitRoundTrip Modes.mode27 = refl
modeOrbitRoundTrip Modes.mode36 = refl
modeOrbitRoundTrip Modes.mode45 = refl

sspToBalancedPhase : SSP.SSPTrit → Harmonic.BalancedTrit
sspToBalancedPhase SSP.sspNegOne = Harmonic.negativeTrit
sspToBalancedPhase SSP.sspZero = Harmonic.zeroTrit
sspToBalancedPhase SSP.sspPosOne = Harmonic.positiveTrit

balancedPhaseToSSP : Harmonic.BalancedTrit → SSP.SSPTrit
balancedPhaseToSSP Harmonic.negativeTrit = SSP.sspNegOne
balancedPhaseToSSP Harmonic.zeroTrit = SSP.sspZero
balancedPhaseToSSP Harmonic.positiveTrit = SSP.sspPosOne

sspBalancedRoundTrip :
  (phase : SSP.SSPTrit) → balancedPhaseToSSP (sspToBalancedPhase phase) ≡ phase
sspBalancedRoundTrip SSP.sspNegOne = refl
sspBalancedRoundTrip SSP.sspZero = refl
sspBalancedRoundTrip SSP.sspPosOne = refl

balancedSSPRoundTrip :
  (phase : Harmonic.BalancedTrit) → sspToBalancedPhase (balancedPhaseToSSP phase) ≡ phase
balancedSSPRoundTrip Harmonic.negativeTrit = refl
balancedSSPRoundTrip Harmonic.zeroTrit = refl
balancedSSPRoundTrip Harmonic.positiveTrit = refl

phaseOrbitToSSP15 : PhaseOrbit15 → SSP15.SSP15InternalLane
phaseOrbitToSSP15 (phase , orbit) =
  orbitToComplementMode orbit , sspToBalancedPhase phase

ssp15ToPhaseOrbit : SSP15.SSP15InternalLane → PhaseOrbit15
ssp15ToPhaseOrbit (mode , phase) =
  balancedPhaseToSSP phase , complementModeToOrbit mode

phaseOrbitSSP15RoundTrip :
  (lane : PhaseOrbit15) →
  ssp15ToPhaseOrbit (phaseOrbitToSSP15 lane) ≡ lane
phaseOrbitSSP15RoundTrip (phase , orbit)
  rewrite sspBalancedRoundTrip phase | orbitModeRoundTrip orbit = refl

ssp15PhaseOrbitRoundTrip :
  (lane : SSP15.SSP15InternalLane) →
  phaseOrbitToSSP15 (ssp15ToPhaseOrbit lane) ≡ lane
ssp15PhaseOrbitRoundTrip (mode , phase)
  rewrite balancedSSPRoundTrip phase | modeOrbitRoundTrip mode = refl

------------------------------------------------------------------------
-- 4. WrongType boundaries.
------------------------------------------------------------------------

data PhasePreservingReductionEqualsFullGlobalInversion : Set where
data OrbitIndexingCreatesSemanticD4Identity : Set where
data ReducedFifteenCreatesMonster42dSameObject : Set where

phasePreservingReductionDoesNotBecomeFullGlobalInversion :
  PhasePreservingReductionEqualsFullGlobalInversion → ⊥
phasePreservingReductionDoesNotBecomeFullGlobalInversion ()

orbitIndexingDoesNotCreateSemanticD4Identity :
  OrbitIndexingCreatesSemanticD4Identity → ⊥
orbitIndexingDoesNotCreateSemanticD4Identity ()

reducedFifteenDoesNotCreateMonster42dSameObject :
  ReducedFifteenCreatesMonster42dSameObject → ⊥
reducedFifteenDoesNotCreateMonster42dSameObject ()

------------------------------------------------------------------------
-- 5. Reduction boundary.
------------------------------------------------------------------------

record Ternary27ReductionBoundary : Set where
  constructor ternary27-reduction-boundary
  field
    ternary27AsOuterPhaseTimesInnerNinePaid : Bool
    innerNineToFiveOrbitQuotientPaid : Bool
    phasePreservingThreeTimesFiveReductionPaid : Bool
    reducedFifteenToSSP15CarrierBijectionPaid : Bool
    fullGlobalInversionOrbitCount : Nat
    fullGlobalInversionOrbitCountKernelProved : Bool
    phasePreservingReductionEqualsFullGlobalInversion : Bool
    orbitToComplementModeIndexingIsSemanticIdentity : Bool
    reducedFifteenIsMonster42dSameObject : Bool
    nextResidual : String
open Ternary27ReductionBoundary public

currentTernary27ReductionBoundary : Ternary27ReductionBoundary
currentTernary27ReductionBoundary = ternary27-reduction-boundary
  true true true true
  14 false false false false
  "The exact paid map is T^3 -> T x (T^2/global inner inversion) = 3 x 5 = 15, preserving the outer ternary phase. This is not the full T^3/global inversion quotient. The five NineOrbit constructors are put in a finite indexing bijection with ComplementMode5 solely to reuse the existing SSP15 carrier; no D4 or Monster semantic identity follows from that indexing. The next proof-bearing bridge is from this phase-preserving reduced carrier, followed by the existing 15 -> 14 -> 42 construction, to a selected Monster class-42 action."

phasePreservingThreeTimesFiveReductionPaidIsTrue :
  phasePreservingThreeTimesFiveReductionPaid currentTernary27ReductionBoundary ≡ true
phasePreservingThreeTimesFiveReductionPaidIsTrue = refl

fullGlobalInversionOrbitCountIsFourteen :
  fullGlobalInversionOrbitCount currentTernary27ReductionBoundary ≡ 14
fullGlobalInversionOrbitCountIsFourteen = refl

phasePreservingReductionEqualsFullGlobalInversionIsFalse :
  phasePreservingReductionEqualsFullGlobalInversion currentTernary27ReductionBoundary ≡ false
phasePreservingReductionEqualsFullGlobalInversionIsFalse = refl

orbitToComplementModeIndexingIsSemanticIdentityIsFalse :
  orbitToComplementModeIndexingIsSemanticIdentity currentTernary27ReductionBoundary ≡ false
orbitToComplementModeIndexingIsSemanticIdentityIsFalse = refl

reducedFifteenIsMonster42dSameObjectIsFalse :
  reducedFifteenIsMonster42dSameObject currentTernary27ReductionBoundary ≡ false
reducedFifteenIsMonster42dSameObjectIsFalse = refl
