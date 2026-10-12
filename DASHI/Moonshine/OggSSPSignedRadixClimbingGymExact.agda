module DASHI.Moonshine.OggSSPSignedRadixClimbingGymExact where

------------------------------------------------------------------------
-- OGG / SSP15 SIGNED RADIX CLIMBING-GYM COMPOSITION
--
-- DASHI CONTRIBUTION
--
-- This module does NOT introduce another SSP15 carrier, another signed
-- FRACTRAN semantics, or another radix tree.  It composes three already-owned
-- objects:
--
--   * canonical Ogg / Monster prime lane;
--   * pointed signed SSP/FRACTRAN multiplicity;
--   * positive-radix outward refinement tree.
--
-- For a selected Ogg prime p, depth-d wall addresses therefore live in the
-- existing dependent carrier
--
--     RadialTreeAddress (base-p chart) d.
--
-- Signed negation changes the FRACTRAN/phase orientation but not the radial
-- address.  Radial coarsening removes one address digit but does not change the
-- signed multiplicity.  The two operations therefore commute definitionally.
--
-- The JMD height formula
--
--   frac(t log p / 2pi),
--
-- and the hole ladder
--
--   2pi m / (p^a log p)
--
-- are downstream analytic/empirical observation surfaces.  They are not
-- silently manufactured by this finite carrier.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Biology.FRACTRANWreathControlledSymmetryExact as Wreath
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Foundations.RadixValuationStageBridge as Radix
import DASHI.Foundations.RepresentationChartInvariant as Representation
import DASHI.Moonshine.Base369Ternary27SpectralSymmetryIrrepBridgeExact as Spectral
import DASHI.Moonshine.JInvariant369SignedSSPFRACTRANPhaseFibreExact as SignedPhase
import DASHI.Moonshine.JInvariant369SSP15SignedFRACTRANBranchExact as SignedBranch
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

------------------------------------------------------------------------
-- 1. Canonical Ogg lane -> its own positive-radix chart.
------------------------------------------------------------------------

oggPrimeRadixChart : Lane.MonsterPrimeLane → Radix.RadixChart
oggPrimeRadixChart Lane.p2 =
  Radix.radix-chart 2 Representation.positive 0 "Ogg p2 radial wall"
oggPrimeRadixChart Lane.p3 =
  Radix.radix-chart 3 Representation.positive 0 "Ogg p3 radial wall"
oggPrimeRadixChart Lane.p5 =
  Radix.radix-chart 5 Representation.positive 0 "Ogg p5 radial wall"
oggPrimeRadixChart Lane.p7 =
  Radix.radix-chart 7 Representation.positive 0 "Ogg p7 radial wall"
oggPrimeRadixChart Lane.p11 =
  Radix.radix-chart 11 Representation.positive 0 "Ogg p11 radial wall"
oggPrimeRadixChart Lane.p13 =
  Radix.radix-chart 13 Representation.positive 0 "Ogg p13 radial wall"
oggPrimeRadixChart Lane.p17 =
  Radix.radix-chart 17 Representation.positive 0 "Ogg p17 radial wall"
oggPrimeRadixChart Lane.p19 =
  Radix.radix-chart 19 Representation.positive 0 "Ogg p19 radial wall"
oggPrimeRadixChart Lane.p23 =
  Radix.radix-chart 23 Representation.positive 0 "Ogg p23 radial wall"
oggPrimeRadixChart Lane.p29 =
  Radix.radix-chart 29 Representation.positive 0 "Ogg p29 radial wall"
oggPrimeRadixChart Lane.p31 =
  Radix.radix-chart 31 Representation.positive 0 "Ogg p31 radial wall"
oggPrimeRadixChart Lane.p41 =
  Radix.radix-chart 41 Representation.positive 0 "Ogg p41 radial wall"
oggPrimeRadixChart Lane.p47 =
  Radix.radix-chart 47 Representation.positive 0 "Ogg p47 radial wall"
oggPrimeRadixChart Lane.p59 =
  Radix.radix-chart 59 Representation.positive 0 "Ogg p59 radial wall"
oggPrimeRadixChart Lane.p71 =
  Radix.radix-chart 71 Representation.positive 0 "Ogg p71 radial wall"

oggPrimeRadixValueExact :
  (prime : Lane.MonsterPrimeLane) →
  Radix.radix (oggPrimeRadixChart prime)
  ≡ Lane.monsterPrimeLaneToNat prime
oggPrimeRadixValueExact Lane.p2 = refl
oggPrimeRadixValueExact Lane.p3 = refl
oggPrimeRadixValueExact Lane.p5 = refl
oggPrimeRadixValueExact Lane.p7 = refl
oggPrimeRadixValueExact Lane.p11 = refl
oggPrimeRadixValueExact Lane.p13 = refl
oggPrimeRadixValueExact Lane.p17 = refl
oggPrimeRadixValueExact Lane.p19 = refl
oggPrimeRadixValueExact Lane.p23 = refl
oggPrimeRadixValueExact Lane.p29 = refl
oggPrimeRadixValueExact Lane.p31 = refl
oggPrimeRadixValueExact Lane.p41 = refl
oggPrimeRadixValueExact Lane.p47 = refl
oggPrimeRadixValueExact Lane.p59 = refl
oggPrimeRadixValueExact Lane.p71 = refl

------------------------------------------------------------------------
-- 2. The signed wall state retains lane identity explicitly.
--
-- PointedSignedSSPLane is reused because a neutral signed multiplicity alone
-- does not remember which Ogg lane produced it.
------------------------------------------------------------------------

record SignedRadixWallState (depth : Nat) : Set where
  constructor signed-radix-wall-state
  field
    pointedSignedLane : SignedBranch.PointedSignedSSPLane
    radialAddress :
      Radix.RadialTreeAddress
        (oggPrimeRadixChart
          (SignedBranch.selectedPrime pointedSignedLane))
        depth

open SignedRadixWallState public

wallPrime :
  ∀ {depth} →
  SignedRadixWallState depth →
  Lane.MonsterPrimeLane
wallPrime state =
  SignedBranch.selectedPrime (pointedSignedLane state)

wallMultiplicity :
  ∀ {depth} →
  SignedRadixWallState depth →
  Signed.SignedMultiplicity
wallMultiplicity state =
  SignedBranch.signedMultiplicity (pointedSignedLane state)

wallOrientation :
  ∀ {depth} →
  SignedRadixWallState depth →
  Signed.FibreOrientation
wallOrientation state =
  Signed.orientationOfMultiplicity (wallMultiplicity state)

wallSpectralPhase :
  ∀ {depth} →
  SignedRadixWallState depth →
  Spectral.AxisFrequency
wallSpectralPhase state =
  SignedPhase.signedSSPPhaseObserver (wallMultiplicity state)

------------------------------------------------------------------------
-- 3. Radial coarsening acts on address only.
------------------------------------------------------------------------

coarsenSignedRadixWall :
  ∀ {depth} →
  SignedRadixWallState (suc depth) →
  SignedRadixWallState depth
coarsenSignedRadixWall
  (signed-radix-wall-state pointed address) =
  signed-radix-wall-state
    pointed
    (Radix.radialCoarsen address)

coarsenPreservesPrime :
  ∀ {depth}
    (state : SignedRadixWallState (suc depth)) →
  wallPrime (coarsenSignedRadixWall state) ≡ wallPrime state
coarsenPreservesPrime state = refl

coarsenPreservesMultiplicity :
  ∀ {depth}
    (state : SignedRadixWallState (suc depth)) →
  wallMultiplicity (coarsenSignedRadixWall state)
  ≡ wallMultiplicity state
coarsenPreservesMultiplicity state = refl

coarsenPreservesOrientation :
  ∀ {depth}
    (state : SignedRadixWallState (suc depth)) →
  wallOrientation (coarsenSignedRadixWall state)
  ≡ wallOrientation state
coarsenPreservesOrientation state = refl

coarsenPreservesSpectralPhase :
  ∀ {depth}
    (state : SignedRadixWallState (suc depth)) →
  wallSpectralPhase (coarsenSignedRadixWall state)
  ≡ wallSpectralPhase state
coarsenPreservesSpectralPhase state = refl

------------------------------------------------------------------------
-- 4. Signed/FRACTRAN negation acts on multiplicity only.
------------------------------------------------------------------------

negatePointedSignedLane :
  SignedBranch.PointedSignedSSPLane →
  SignedBranch.PointedSignedSSPLane
negatePointedSignedLane state =
  SignedBranch.pointed-signed-ssp-lane
    (SignedBranch.selectedPrime state)
    (Signed.negateMultiplicity
      (SignedBranch.signedMultiplicity state))

negateSignedRadixWall :
  ∀ {depth} →
  SignedRadixWallState depth →
  SignedRadixWallState depth
negateSignedRadixWall
  (signed-radix-wall-state pointed address) =
  signed-radix-wall-state
    (negatePointedSignedLane pointed)
    address

negatePreservesPrime :
  ∀ {depth}
    (state : SignedRadixWallState depth) →
  wallPrime (negateSignedRadixWall state) ≡ wallPrime state
negatePreservesPrime state = refl

negateTwice :
  ∀ {depth}
    (state : SignedRadixWallState depth) →
  negateSignedRadixWall (negateSignedRadixWall state) ≡ state
negateTwice
  (signed-radix-wall-state
    (SignedBranch.pointed-signed-ssp-lane prime
      (Signed.negativeMultiplicity n))
    address) = refl
negateTwice
  (signed-radix-wall-state
    (SignedBranch.pointed-signed-ssp-lane prime Signed.zeroMultiplicity)
    address) = refl
negateTwice
  (signed-radix-wall-state
    (SignedBranch.pointed-signed-ssp-lane prime
      (Signed.positiveMultiplicity n))
    address) = refl

coarsenNegationCommutes :
  ∀ {depth}
    (state : SignedRadixWallState (suc depth)) →
  coarsenSignedRadixWall (negateSignedRadixWall state)
  ≡
  negateSignedRadixWall (coarsenSignedRadixWall state)
coarsenNegationCommutes
  (signed-radix-wall-state pointed (Radix.radial-extend parent digit)) = refl

------------------------------------------------------------------------
-- 5. Explicit wall form N = p^a.
--
-- Keep the exponent explicit rather than overloading a visual "level" label;
-- the supplied figures use forms p, p^2, p^3 while another caption numbers
-- the root/refinement levels differently.
------------------------------------------------------------------------

record WallForm : Set where
  constructor wall-form
  field
    formLane : Lane.MonsterPrimeLane
    formExponent : Nat

open WallForm public

wallFormN : WallForm → Nat
wallFormN form =
  Radix.radixPower
    (Lane.monsterPrimeLaneToNat (formLane form))
    (formExponent form)

p2Exponent1 : WallForm
p2Exponent1 = wall-form Lane.p2 1

p3Exponent1 : WallForm
p3Exponent1 = wall-form Lane.p3 1

p5Exponent1 : WallForm
p5Exponent1 = wall-form Lane.p5 1

p7Exponent1 : WallForm
p7Exponent1 = wall-form Lane.p7 1

p11Exponent1 : WallForm
p11Exponent1 = wall-form Lane.p11 1

p2Exponent2 : WallForm
p2Exponent2 = wall-form Lane.p2 2

p3Exponent2 : WallForm
p3Exponent2 = wall-form Lane.p3 2

p2Exponent3 : WallForm
p2Exponent3 = wall-form Lane.p2 3

p13Exponent1 : WallForm
p13Exponent1 = wall-form Lane.p13 1

p71Exponent1 : WallForm
p71Exponent1 = wall-form Lane.p71 1

------------------------------------------------------------------------
-- 6. Existing FRACTRAN-controlled wreath action is retained as a distinct
--    dynamic layer.  A symmetry step firing is not a radix refinement step.
------------------------------------------------------------------------

existingControlledWreathState : Set
existingControlledWreathState = Wreath.ControlledState

------------------------------------------------------------------------
-- 7. Authority boundary.
------------------------------------------------------------------------

record OggSSPSignedRadixClimbingGymBoundary : Set where
  constructor ogg-ssp-signed-radix-climbing-gym-boundary
  field
    canonicalOggCarrierReused : Bool
    existingOggToSignedPrimeBridgeReused : Bool
    existingPointedSignedLaneReused : Bool
    existingGenericPositiveRadixTreeReused : Bool
    nativePrimeValueSelectsRadix : Bool
    radialCoarseningPreservesSignedMultiplicity : Bool
    radialCoarseningCommutesWithSignedNegation : Bool
    signedPhaseObserverPreservedByRadialCoarsening : Bool
    existingFRACTRANControlledWreathLayerRetained : Bool

    signedValuationIsRadixAddress : Bool
    wreathSymmetryStepIsRadixRefinement : Bool
    pAryRadixDepthIs369Depth : Bool
    finiteRadixTreeConstructsAnalyticLogPhase : Bool
    finiteRadixTreeConstructsZetaZeroParametrisation : Bool

open OggSSPSignedRadixClimbingGymBoundary public

canonicalOggSSPSignedRadixClimbingGymBoundary :
  OggSSPSignedRadixClimbingGymBoundary
canonicalOggSSPSignedRadixClimbingGymBoundary =
  ogg-ssp-signed-radix-climbing-gym-boundary
    true true true true true true true true true
    false false false false false
