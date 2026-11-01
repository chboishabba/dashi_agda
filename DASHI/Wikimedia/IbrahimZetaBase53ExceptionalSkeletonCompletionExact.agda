module DASHI.Wikimedia.IbrahimZetaBase53ExceptionalSkeletonCompletionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369FiveModePhaseQuotientExact as Five
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.ExceptionalAlbertFreudenthalResidualExact as Exceptional
import DASHI.Moonshine.Base369MonsterFiftyFourFiveModeResidualActionBidiExact as Base
import DASHI.Moonshine.Base369ExceptionalAlbertFiftyThreeResidualBidiExact as ExistingBridge
import DASHI.Moonshine.Base369ZetaHeisenbergFiftyFourCarrierExact as Zeta
import DASHI.Wikimedia.IbrahimTernary27OriginTraceless26AlbertShapeBidiExact as Shape
import DASHI.Wikimedia.IbrahimZeta54AlbertPair53SnowballAttributionBidiExact as Albert
import DASHI.Wikimedia.IbrahimZetaSixByNineFiveMode54CarrierSnowballExact as Chart

------------------------------------------------------------------------
-- COMPLETE THE CARRIER/DELETION LAYER BEFORE TOUCHING THE ACTION LAYER
--
-- Previous owners paid:
--
--   Zeta54Site <-> AlbertPair54
--   ZetaResidual53 <-> ReducedAlbertPair53
--   Zeta54Site <-> Base.SecondaryCell54
--   zeta-sheet origin <-> Base.distinguishedInvariant54.
--
-- This owner pays the missing residual chart
--
--   Base.ResidualCell53 <-> ZetaResidual53
--
-- so the Base 54->53 deletion and the Albert 54->53 deletion are now the same
-- finite carrier square.  Actual Monster action recognition remains separate.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. The left 26 states = A1*9 + distinguished*8 + A2*9.
------------------------------------------------------------------------

negativeNonOrigin : Five.ModePhaseQuotient9 → Shape.NonOrigin26
negativeNonOrigin Five.A2negative = Shape.nnn
negativeNonOrigin Five.A2positive = Shape.nnz
negativeNonOrigin Five.B1negative = Shape.nnp
negativeNonOrigin Five.B1positive = Shape.nzn
negativeNonOrigin Five.identityMode = Shape.nzz
negativeNonOrigin Five.B2negative = Shape.nzp
negativeNonOrigin Five.B2positive = Shape.npn
negativeNonOrigin Five.Enegative = Shape.npz
negativeNonOrigin Five.Epositive = Shape.npp

positiveNonOrigin : Five.ModePhaseQuotient9 → Shape.NonOrigin26
positiveNonOrigin Five.A2negative = Shape.pnn
positiveNonOrigin Five.A2positive = Shape.pnz
positiveNonOrigin Five.B1negative = Shape.pnp
positiveNonOrigin Five.B1positive = Shape.pzn
positiveNonOrigin Five.identityMode = Shape.pzz
positiveNonOrigin Five.B2negative = Shape.pzp
positiveNonOrigin Five.B2positive = Shape.ppn
positiveNonOrigin Five.Enegative = Shape.ppz
positiveNonOrigin Five.Epositive = Shape.ppp

distinguishedNonOrigin : Base.DistinguishedResidual8 → Shape.NonOrigin26
distinguishedNonOrigin Base.residualA2negative = Shape.znn
distinguishedNonOrigin Base.residualA2positive = Shape.znz
distinguishedNonOrigin Base.residualB1negative = Shape.znp
distinguishedNonOrigin Base.residualB1positive = Shape.zzn
distinguishedNonOrigin Base.residualB2negative = Shape.zzp
distinguishedNonOrigin Base.residualB2positive = Shape.zpn
distinguishedNonOrigin Base.residualEnegative = Shape.zpz
distinguishedNonOrigin Base.residualEpositive = Shape.zpp

nonOriginToBaseLeft : Shape.NonOrigin26 → Base.ResidualCell53
nonOriginToBaseLeft Shape.nnn = inj₁ (Five.A1 , Five.A2negative)
nonOriginToBaseLeft Shape.nnz = inj₁ (Five.A1 , Five.A2positive)
nonOriginToBaseLeft Shape.nnp = inj₁ (Five.A1 , Five.B1negative)
nonOriginToBaseLeft Shape.nzn = inj₁ (Five.A1 , Five.B1positive)
nonOriginToBaseLeft Shape.nzz = inj₁ (Five.A1 , Five.identityMode)
nonOriginToBaseLeft Shape.nzp = inj₁ (Five.A1 , Five.B2negative)
nonOriginToBaseLeft Shape.npn = inj₁ (Five.A1 , Five.B2positive)
nonOriginToBaseLeft Shape.npz = inj₁ (Five.A1 , Five.Enegative)
nonOriginToBaseLeft Shape.npp = inj₁ (Five.A1 , Five.Epositive)
nonOriginToBaseLeft Shape.znn = inj₂ Base.residualA2negative
nonOriginToBaseLeft Shape.znz = inj₂ Base.residualA2positive
nonOriginToBaseLeft Shape.znp = inj₂ Base.residualB1negative
nonOriginToBaseLeft Shape.zzn = inj₂ Base.residualB1positive
nonOriginToBaseLeft Shape.zzp = inj₂ Base.residualB2negative
nonOriginToBaseLeft Shape.zpn = inj₂ Base.residualB2positive
nonOriginToBaseLeft Shape.zpz = inj₂ Base.residualEnegative
nonOriginToBaseLeft Shape.zpp = inj₂ Base.residualEpositive
nonOriginToBaseLeft Shape.pnn = inj₁ (Five.A2 , Five.A2negative)
nonOriginToBaseLeft Shape.pnz = inj₁ (Five.A2 , Five.A2positive)
nonOriginToBaseLeft Shape.pnp = inj₁ (Five.A2 , Five.B1negative)
nonOriginToBaseLeft Shape.pzn = inj₁ (Five.A2 , Five.B1positive)
nonOriginToBaseLeft Shape.pzz = inj₁ (Five.A2 , Five.identityMode)
nonOriginToBaseLeft Shape.pzp = inj₁ (Five.A2 , Five.B2negative)
nonOriginToBaseLeft Shape.ppn = inj₁ (Five.A2 , Five.B2positive)
nonOriginToBaseLeft Shape.ppz = inj₁ (Five.A2 , Five.Enegative)
nonOriginToBaseLeft Shape.ppp = inj₁ (Five.A2 , Five.Epositive)

------------------------------------------------------------------------
-- 2. The right 27 states = B1*9 + B2*9 + E*9.
------------------------------------------------------------------------

pointAtX : SSP.SSPTrit → Five.ModePhaseQuotient9 → Geometry.Ternary27Point
pointAtX x state with Chart.modePhaseToNonary state
... | Zeta.nonary9Point y z = Geometry.ternary27Point x y z

rightPointToBase : Geometry.Ternary27Point → Base.ResidualCell53
rightPointToBase (Geometry.ternary27Point SSP.sspNegOne y z) =
  inj₁ (Five.B1 , Chart.nonaryToModePhase (Zeta.nonary9Point y z))
rightPointToBase (Geometry.ternary27Point SSP.sspZero y z) =
  inj₁ (Five.B2 , Chart.nonaryToModePhase (Zeta.nonary9Point y z))
rightPointToBase (Geometry.ternary27Point SSP.sspPosOne y z) =
  inj₁ (Five.E , Chart.nonaryToModePhase (Zeta.nonary9Point y z))

------------------------------------------------------------------------
-- 3. Base residual <-> zeta residual.
------------------------------------------------------------------------

base53ToZeta53 : Base.ResidualCell53 → Albert.ZetaResidual53
base53ToZeta53 (inj₁ (Five.A1 , state)) = inj₁ (negativeNonOrigin state)
base53ToZeta53 (inj₁ (Five.A2 , state)) = inj₁ (positiveNonOrigin state)
base53ToZeta53 (inj₁ (Five.B1 , state)) = inj₂ (pointAtX SSP.sspNegOne state)
base53ToZeta53 (inj₁ (Five.B2 , state)) = inj₂ (pointAtX SSP.sspZero state)
base53ToZeta53 (inj₁ (Five.E , state)) = inj₂ (pointAtX SSP.sspPosOne state)
base53ToZeta53 (inj₂ residual) = inj₁ (distinguishedNonOrigin residual)

zeta53ToBase53 : Albert.ZetaResidual53 → Base.ResidualCell53
zeta53ToBase53 (inj₁ q) = nonOriginToBaseLeft q
zeta53ToBase53 (inj₂ p) = rightPointToBase p

negativeRoundTrip :
  (s : Five.ModePhaseQuotient9) →
  nonOriginToBaseLeft (negativeNonOrigin s) ≡ inj₁ (Five.A1 , s)
negativeRoundTrip Five.identityMode = refl
negativeRoundTrip Five.A2negative = refl
negativeRoundTrip Five.A2positive = refl
negativeRoundTrip Five.B1negative = refl
negativeRoundTrip Five.B1positive = refl
negativeRoundTrip Five.B2negative = refl
negativeRoundTrip Five.B2positive = refl
negativeRoundTrip Five.Enegative = refl
negativeRoundTrip Five.Epositive = refl

positiveRoundTrip :
  (s : Five.ModePhaseQuotient9) →
  nonOriginToBaseLeft (positiveNonOrigin s) ≡ inj₁ (Five.A2 , s)
positiveRoundTrip Five.identityMode = refl
positiveRoundTrip Five.A2negative = refl
positiveRoundTrip Five.A2positive = refl
positiveRoundTrip Five.B1negative = refl
positiveRoundTrip Five.B1positive = refl
positiveRoundTrip Five.B2negative = refl
positiveRoundTrip Five.B2positive = refl
positiveRoundTrip Five.Enegative = refl
positiveRoundTrip Five.Epositive = refl

distinguishedRoundTrip :
  (r : Base.DistinguishedResidual8) →
  nonOriginToBaseLeft (distinguishedNonOrigin r) ≡ inj₂ r
distinguishedRoundTrip Base.residualA2negative = refl
distinguishedRoundTrip Base.residualA2positive = refl
distinguishedRoundTrip Base.residualB1negative = refl
distinguishedRoundTrip Base.residualB1positive = refl
distinguishedRoundTrip Base.residualB2negative = refl
distinguishedRoundTrip Base.residualB2positive = refl
distinguishedRoundTrip Base.residualEnegative = refl
distinguishedRoundTrip Base.residualEpositive = refl

rightB1RoundTrip :
  (s : Five.ModePhaseQuotient9) →
  rightPointToBase (pointAtX SSP.sspNegOne s) ≡ inj₁ (Five.B1 , s)
rightB1RoundTrip s with Chart.modePhaseToNonary s
... | n rewrite Chart.modePhaseNonaryRoundTrip s = refl

rightB2RoundTrip :
  (s : Five.ModePhaseQuotient9) →
  rightPointToBase (pointAtX SSP.sspZero s) ≡ inj₁ (Five.B2 , s)
rightB2RoundTrip s with Chart.modePhaseToNonary s
... | n rewrite Chart.modePhaseNonaryRoundTrip s = refl

rightERoundTrip :
  (s : Five.ModePhaseQuotient9) →
  rightPointToBase (pointAtX SSP.sspPosOne s) ≡ inj₁ (Five.E , s)
rightERoundTrip s with Chart.modePhaseToNonary s
... | n rewrite Chart.modePhaseNonaryRoundTrip s = refl

base53Zeta53RoundTrip :
  (s : Base.ResidualCell53) → zeta53ToBase53 (base53ToZeta53 s) ≡ s
base53Zeta53RoundTrip (inj₁ (Five.A1 , s)) = negativeRoundTrip s
base53Zeta53RoundTrip (inj₁ (Five.A2 , s)) = positiveRoundTrip s
base53Zeta53RoundTrip (inj₁ (Five.B1 , s)) = rightB1RoundTrip s
base53Zeta53RoundTrip (inj₁ (Five.B2 , s)) = rightB2RoundTrip s
base53Zeta53RoundTrip (inj₁ (Five.E , s)) = rightERoundTrip s
base53Zeta53RoundTrip (inj₂ r) = distinguishedRoundTrip r

zetaLeftRoundTrip :
  (q : Shape.NonOrigin26) → base53ToZeta53 (nonOriginToBaseLeft q) ≡ inj₁ q
zetaLeftRoundTrip Shape.nnn = refl
zetaLeftRoundTrip Shape.nnz = refl
zetaLeftRoundTrip Shape.nnp = refl
zetaLeftRoundTrip Shape.nzn = refl
zetaLeftRoundTrip Shape.nzz = refl
zetaLeftRoundTrip Shape.nzp = refl
zetaLeftRoundTrip Shape.npn = refl
zetaLeftRoundTrip Shape.npz = refl
zetaLeftRoundTrip Shape.npp = refl
zetaLeftRoundTrip Shape.znn = refl
zetaLeftRoundTrip Shape.znz = refl
zetaLeftRoundTrip Shape.znp = refl
zetaLeftRoundTrip Shape.zzn = refl
zetaLeftRoundTrip Shape.zzp = refl
zetaLeftRoundTrip Shape.zpn = refl
zetaLeftRoundTrip Shape.zpz = refl
zetaLeftRoundTrip Shape.zpp = refl
zetaLeftRoundTrip Shape.pnn = refl
zetaLeftRoundTrip Shape.pnz = refl
zetaLeftRoundTrip Shape.pnp = refl
zetaLeftRoundTrip Shape.pzn = refl
zetaLeftRoundTrip Shape.pzz = refl
zetaLeftRoundTrip Shape.pzp = refl
zetaLeftRoundTrip Shape.ppn = refl
zetaLeftRoundTrip Shape.ppz = refl
zetaLeftRoundTrip Shape.ppp = refl

zetaRightRoundTrip :
  (p : Geometry.Ternary27Point) → base53ToZeta53 (rightPointToBase p) ≡ inj₂ p
zetaRightRoundTrip (Geometry.ternary27Point SSP.sspNegOne y z)
  rewrite Chart.nonaryModePhaseRoundTrip (Zeta.nonary9Point y z) = refl
zetaRightRoundTrip (Geometry.ternary27Point SSP.sspZero y z)
  rewrite Chart.nonaryModePhaseRoundTrip (Zeta.nonary9Point y z) = refl
zetaRightRoundTrip (Geometry.ternary27Point SSP.sspPosOne y z)
  rewrite Chart.nonaryModePhaseRoundTrip (Zeta.nonary9Point y z) = refl

zeta53Base53RoundTrip :
  (s : Albert.ZetaResidual53) → base53ToZeta53 (zeta53ToBase53 s) ≡ s
zeta53Base53RoundTrip (inj₁ q) = zetaLeftRoundTrip q
zeta53Base53RoundTrip (inj₂ p) = zetaRightRoundTrip p

------------------------------------------------------------------------
-- 4. The 53 inclusion is the restriction of the already-paid 54 chart.
------------------------------------------------------------------------

negativePointMatches :
  (s : Five.ModePhaseQuotient9) →
  Shape.nonOriginToPoint (negativeNonOrigin s) ≡ pointAtX SSP.sspNegOne s
negativePointMatches Five.identityMode = refl
negativePointMatches Five.A2negative = refl
negativePointMatches Five.A2positive = refl
negativePointMatches Five.B1negative = refl
negativePointMatches Five.B1positive = refl
negativePointMatches Five.B2negative = refl
negativePointMatches Five.B2positive = refl
negativePointMatches Five.Enegative = refl
negativePointMatches Five.Epositive = refl

positivePointMatches :
  (s : Five.ModePhaseQuotient9) →
  Shape.nonOriginToPoint (positiveNonOrigin s) ≡ pointAtX SSP.sspPosOne s
positivePointMatches Five.identityMode = refl
positivePointMatches Five.A2negative = refl
positivePointMatches Five.A2positive = refl
positivePointMatches Five.B1negative = refl
positivePointMatches Five.B1positive = refl
positivePointMatches Five.B2negative = refl
positivePointMatches Five.B2positive = refl
positivePointMatches Five.Enegative = refl
positivePointMatches Five.Epositive = refl

baseResidualInclusionCommutes :
  (s : Base.ResidualCell53) →
  Chart.zeta54ToBase54 (Albert.includeZetaResidual53 (base53ToZeta53 s))
  ≡ Base.includeResidual53 s
baseResidualInclusionCommutes (inj₁ (Five.A1 , state))
  rewrite negativePointMatches state
        | Chart.modePhaseNonaryRoundTrip state = refl
baseResidualInclusionCommutes (inj₁ (Five.A2 , state))
  rewrite positivePointMatches state
        | Chart.modePhaseNonaryRoundTrip state = refl
baseResidualInclusionCommutes (inj₁ (Five.B1 , state))
  with Chart.modePhaseToNonary state
... | n rewrite Chart.modePhaseNonaryRoundTrip state = refl
baseResidualInclusionCommutes (inj₁ (Five.B2 , state))
  with Chart.modePhaseToNonary state
... | n rewrite Chart.modePhaseNonaryRoundTrip state = refl
baseResidualInclusionCommutes (inj₁ (Five.E , state))
  with Chart.modePhaseToNonary state
... | n rewrite Chart.modePhaseNonaryRoundTrip state = refl
baseResidualInclusionCommutes (inj₂ Base.residualA2negative) = refl
baseResidualInclusionCommutes (inj₂ Base.residualA2positive) = refl
baseResidualInclusionCommutes (inj₂ Base.residualB1negative) = refl
baseResidualInclusionCommutes (inj₂ Base.residualB1positive) = refl
baseResidualInclusionCommutes (inj₂ Base.residualB2negative) = refl
baseResidualInclusionCommutes (inj₂ Base.residualB2positive) = refl
baseResidualInclusionCommutes (inj₂ Base.residualEnegative) = refl
baseResidualInclusionCommutes (inj₂ Base.residualEpositive) = refl

------------------------------------------------------------------------
-- 5. Compose all the way to the exceptional carrier shapes.
------------------------------------------------------------------------

base54ToAlbert54 : Base.SecondaryCell54 → Albert.CubeAlbertPair54
base54ToAlbert54 s = Albert.zeta54ToAlbertPair54 (Chart.base54ToZeta54 s)

albert54ToBase54 : Albert.CubeAlbertPair54 → Base.SecondaryCell54
albert54ToBase54 a = Chart.zeta54ToBase54 (Albert.albertPair54ToZeta54 a)

base54Albert54RoundTrip :
  (s : Base.SecondaryCell54) → albert54ToBase54 (base54ToAlbert54 s) ≡ s
base54Albert54RoundTrip s
  rewrite Albert.zeta54Albert54RoundTrip (Chart.base54ToZeta54 s)
        | Chart.base54Zeta54RoundTrip s = refl

albert54Base54RoundTrip :
  (a : Albert.CubeAlbertPair54) → base54ToAlbert54 (albert54ToBase54 a) ≡ a
albert54Base54RoundTrip a
  rewrite Chart.zeta54Base54RoundTrip (Albert.albertPair54ToZeta54 a)
        | Albert.albert54Zeta54RoundTrip a = refl

base53ToAlbert53 : Base.ResidualCell53 → Albert.CubeReducedAlbert53
base53ToAlbert53 s = Albert.zetaResidual53ToAlbert53 (base53ToZeta53 s)

albert53ToBase53 : Albert.CubeReducedAlbert53 → Base.ResidualCell53
albert53ToBase53 a = zeta53ToBase53 (Albert.albert53ToZetaResidual53 a)

base53Albert53RoundTrip :
  (s : Base.ResidualCell53) → albert53ToBase53 (base53ToAlbert53 s) ≡ s
base53Albert53RoundTrip s
  rewrite Albert.zeta53Albert53RoundTrip (base53ToZeta53 s)
        | base53Zeta53RoundTrip s = refl

albert53Base53RoundTrip :
  (a : Albert.CubeReducedAlbert53) → base53ToAlbert53 (albert53ToBase53 a) ≡ a
albert53Base53RoundTrip a
  rewrite zeta53Base53RoundTrip (Albert.albert53ToZetaResidual53 a)
        | Albert.albert53Zeta53RoundTrip a = refl

baseRemovedInvariantMapsToAlbertRemovedScalar :
  base54ToAlbert54 Base.distinguishedInvariant54
  ≡ inj₁ (inj₁ Exceptional.scalarLine)
baseRemovedInvariantMapsToAlbertRemovedScalar = refl

------------------------------------------------------------------------
-- 6. Strong proof-bearing completion receipt; action remains explicitly open.
------------------------------------------------------------------------

record CarrierDeletionCompletion : Set where
  constructor carrier-deletion-completion
  field
    full54Bijection : Bool
    residual53Bijection : Bool
    baseResidualInclusionCommutes : Bool
    removedInvariantMatchesAlbertLeftScalar : Bool
    existingSkeletonInterfaceReached : Bool
    actual54ActionRecognitionPaid : Bool
    actual53SameActionRestrictionPaid : Bool
    monsterRepresentationIdentificationPaid : Bool
open CarrierDeletionCompletion public

currentCarrierDeletionCompletion : CarrierDeletionCompletion
currentCarrierDeletionCompletion = carrier-deletion-completion
  true true true true true false false false

------------------------------------------------------------------------
-- 7. WrongType boundary.
------------------------------------------------------------------------

data CarrierCompletionCreatesActionRecognition : Set where
data FiveModeLabelsBecomeExceptionalRepresentations : Set where
data RemovedPointBecomesJordanUnit : Set where

carrierCompletionDoesNotCreateAction : CarrierCompletionCreatesActionRecognition → ⊥
carrierCompletionDoesNotCreateAction ()

fiveModeLabelsDoNotBecomeExceptional : FiveModeLabelsBecomeExceptionalRepresentations → ⊥
fiveModeLabelsDoNotBecomeExceptional ()

removedPointDoesNotBecomeJordanUnit : RemovedPointBecomesJordanUnit → ⊥
removedPointDoesNotBecomeJordanUnit ()

nextResidual : String
nextResidual =
  "the Base/Zeta/Albert 54->53 finite carrier square is now explicit with two-sided maps and commuting residual inclusion. The highest-alpha remaining theorem is no longer carrier identity: acquire or construct an ActualFiftyFourFiveModeResidualActionRecognition on the actual Monster restriction and prove that the same 54 action fixes the distinguished state and restricts to the 53 residual. Only then instantiate Base369ExceptionalResidualRecognition. In parallel snowball action-level primary sources and exact restriction-character data; do not let QID/DOI/OEIS/Dewey metadata pay the action."
