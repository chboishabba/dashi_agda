module DASHI.Moonshine.Monster3BRegularC3BulkResidualFiftyThreeBidiExact where

------------------------------------------------------------------------
-- CHARACTER-LEVEL 3B REGULAR BULK -> SAME-ACTION 53 RESIDUAL FRONTIER
--
-- The certified 3B restriction already has the exact character identity
--
--   W|C3 = 53 * 1 + 65610 * Reg(C3)
--
-- equivalently, for the three phase multiplicities,
--
--   (65663,65610,65610)
--     = (65610,65610,65610) + (53,0,0).
--
-- Hence the 196830 bulk is not merely numerically 3*65610: at character level
-- it is exactly the balanced regular C3 character.  The only non-character
-- theorem left is to lift that certified character splitting to one literal
-- state/module decomposition carrying the SAME action.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Product using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

import DASHI.Moonshine.Monster3BCyclicFourierDyadicBridgeExact as Fourier
import DASHI.Foundations.ExceptionalAlbertFreudenthalResidualExact as Exceptional

------------------------------------------------------------------------
-- 1. Exact certified character decomposition.
------------------------------------------------------------------------

regularC3Multiplicity : Nat
regularC3Multiplicity = 65610

regularC3BulkDimension : Nat
regularC3BulkDimension = 3 * regularC3Multiplicity

regularC3BulkDimensionIs196830 : regularC3BulkDimension ≡ 196830
regularC3BulkDimensionIs196830 = Fourier.balancedRegularBulkDimensionIs196830

fixedPhaseMultiplicity : Nat
fixedPhaseMultiplicity = Fourier.invariant Fourier.monsterW3B

zetaPhaseMultiplicity : Nat
zetaPhaseMultiplicity = Fourier.zeta Fourier.monsterW3B

zetaSquaredPhaseMultiplicity : Nat
zetaSquaredPhaseMultiplicity = Fourier.zetaSquared Fourier.monsterW3B

fixedPhaseIsRegularPlusResidual :
  regularC3Multiplicity + 53 ≡ fixedPhaseMultiplicity
fixedPhaseIsRegularPlusResidual = Fourier.monsterWCharacterResidual

zetaPhaseIsRegular : zetaPhaseMultiplicity ≡ regularC3Multiplicity
zetaPhaseIsRegular = refl

zetaSquaredPhaseIsRegular :
  zetaSquaredPhaseMultiplicity ≡ regularC3Multiplicity
zetaSquaredPhaseIsRegular = refl

regularBulkPlusResidualIsMonster :
  regularC3BulkDimension + 53 ≡ 196883
regularBulkPlusResidualIsMonster = Fourier.balancedBulkPlusResidualIsMonsterW

------------------------------------------------------------------------
-- 2. Literal lifting target.
--
-- Character equality does not manufacture subspaces.  A valid lift provides
-- one ambient state carrier, three literal phase carriers, a selected regular
-- fixed-phase block of the SAME size as either nontrivial phase, and a residual
-- carrier.  The fixed phase must be reconstructed as regular + residual, and
-- every inclusion must intertwine the same actor.
------------------------------------------------------------------------

record ActualRegularC3BulkResidualLift : Setω where
  field
    Actor Ambient FixedPhase ZetaPhase ZetaSquaredPhase : Set
    RegularFixedPhase Residual53 : Set

    ambientAct : Actor → Ambient → Ambient
    fixedAct : Actor → FixedPhase → FixedPhase
    zetaAct : Actor → ZetaPhase → ZetaPhase
    zetaSquaredAct : Actor → ZetaSquaredPhase → ZetaSquaredPhase
    regularFixedAct : Actor → RegularFixedPhase → RegularFixedPhase
    residualAct : Actor → Residual53 → Residual53

    includeFixed : FixedPhase → Ambient
    includeZeta : ZetaPhase → Ambient
    includeZetaSquared : ZetaSquaredPhase → Ambient

    fixedIntertwinesAmbient :
      (actor : Actor) → (state : FixedPhase) →
      includeFixed (fixedAct actor state) ≡ ambientAct actor (includeFixed state)
    zetaIntertwinesAmbient :
      (actor : Actor) → (state : ZetaPhase) →
      includeZeta (zetaAct actor state) ≡ ambientAct actor (includeZeta state)
    zetaSquaredIntertwinesAmbient :
      (actor : Actor) → (state : ZetaSquaredPhase) →
      includeZetaSquared (zetaSquaredAct actor state)
      ≡ ambientAct actor (includeZetaSquared state)

    fixedToRegularResidual : FixedPhase → RegularFixedPhase ⊎ Residual53
    regularResidualToFixed : RegularFixedPhase ⊎ Residual53 → FixedPhase
    regularResidualAfterFixed :
      (state : FixedPhase) →
      regularResidualToFixed (fixedToRegularResidual state) ≡ state
    fixedAfterRegularResidual :
      (state : RegularFixedPhase ⊎ Residual53) →
      fixedToRegularResidual (regularResidualToFixed state) ≡ state

    regularFixedStable :
      (actor : Actor) → (state : RegularFixedPhase) →
      fixedToRegularResidual
        (fixedAct actor (regularResidualToFixed (inj₁ state)))
      ≡ inj₁ (regularFixedAct actor state)

    residualStable :
      (actor : Actor) → (state : Residual53) →
      fixedToRegularResidual
        (fixedAct actor (regularResidualToFixed (inj₂ state)))
      ≡ inj₂ (residualAct actor state)

    -- Dimension/cardinality authorities are explicit inputs at the lift
    -- boundary rather than inferred from character equality.
    regularFixedDimension : Nat
    residualDimension : Nat
    regularFixedDimensionIs65610 : regularFixedDimension ≡ 65610
    residualDimensionIs53 : residualDimension ≡ 53

open ActualRegularC3BulkResidualLift public

------------------------------------------------------------------------
-- 3. Downstream exceptional recognition target.
--
-- Only AFTER the literal 53 residual has been constructed do we compare it to
-- the Albert/F4 candidate 1 + 26 + 26.
------------------------------------------------------------------------

record ResidualFiftyThreeAlbertRecognition
    (lift : ActualRegularC3BulkResidualLift) : Set₁ where
  field
    AlbertPair : Exceptional.AlbertPairCarrier
    toAlbertResidual : Residual53 lift → Exceptional.ReducedAlbertPair53 AlbertPair
    fromAlbertResidual : Exceptional.ReducedAlbertPair53 AlbertPair → Residual53 lift
    fromAfterTo :
      (state : Residual53 lift) →
      fromAlbertResidual (toAlbertResidual state) ≡ state
    toAfterFrom :
      (state : Exceptional.ReducedAlbertPair53 AlbertPair) →
      toAlbertResidual (fromAlbertResidual state) ≡ state

    exceptionalAct : Actor lift → Exceptional.ReducedAlbertPair53 AlbertPair
      → Exceptional.ReducedAlbertPair53 AlbertPair
    residualIntertwinesExceptional :
      (actor : Actor lift) → (state : Residual53 lift) →
      toAlbertResidual (residualAct lift actor state)
      ≡ exceptionalAct actor (toAlbertResidual state)

------------------------------------------------------------------------
-- 4. Frontier boundary.
------------------------------------------------------------------------

record RegularC3ResidualBoundary : Set where
  constructor regularC3ResidualBoundary
  field
    characterRegularBulkIsExact : Bool
    regularBulkDimension196830Exact : Bool
    characterResidual53Exact : Bool
    literalFixedPhaseRegularBlockConstructedHere : Bool
    literalResidual53ConstructedHere : Bool
    characterEqualityAloneCreatesSubmodule : Bool
    albertRecognitionOnlyDownstreamOfLiteralResidual : Bool
    albertRecognitionInhabitedHere : Bool

canonicalRegularC3ResidualBoundary : RegularC3ResidualBoundary
canonicalRegularC3ResidualBoundary =
  regularC3ResidualBoundary
    true true true
    false false false
    true false
