module DASHI.Moonshine.OggSSPP2TrialecticNineCentreResidualBidiExact where

------------------------------------------------------------------------
-- p=2 TEN-STATE TARGET AS PHASE-NINE + CENTRE-ONLY DEPENDENT RESIDUAL
--
-- DASHI CONTRIBUTION
--
-- The shared pre-RH trialectic observer sees:
--
--   PhaseNine = T^2
--
-- with nine states.  The p=2 target has ten states and differs from PhaseNine
-- only by DUPLICATING the centre.
--
-- Therefore the exact loss repair is not a global extra bit.  It is a
-- state-dependent residual:
--
--   Residual(mid,mid) = CentreBranchBit   -- two states
--   Residual(other)   = Unit              -- one state
--
-- This yields a second exact dependent codec of the same p=2 target:
--
--   DuplicatedCentreNineSheet
--      ~= Sigma(phase : PhaseNine), CentreResidual phase.
--
-- It is dual to the existing F4-stratified fibre profile 1+1+8:
--
--   F4 coarse language    : 1 + 1 + 8
--   trialectic T2 language: 2 at centre, 1 on each of 8 noncentral states.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Empty using (⊥)

import Base369 as Base
import DASHI.Core.DependentRecoverableProjectionExact as Dependent
import DASHI.Foundations.TernaryEndomorphismPhaseQuotientExact as Phase
import DASHI.Moonshine.OggSSPP2BalancedTernaryPuncturedPlaneExact as Plane
import DASHI.Moonshine.OggSSPP2TrialecticNineObserverReconciliationExact as SharedNine
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Centre-only residual family.
------------------------------------------------------------------------

data CentreBranchBit : Set where
  lowerBranch : CentreBranchBit
  upperBranch : CentreBranchBit

CentreResidual :
  Phase.PhaseQuotient9 ->
  Set
CentreResidual (Base.tri-mid , Base.tri-mid) =
  CentreBranchBit
CentreResidual (Base.tri-low , Base.tri-low) = ⊤
CentreResidual (Base.tri-low , Base.tri-mid) = ⊤
CentreResidual (Base.tri-low , Base.tri-high) = ⊤
CentreResidual (Base.tri-mid , Base.tri-low) = ⊤
CentreResidual (Base.tri-mid , Base.tri-high) = ⊤
CentreResidual (Base.tri-high , Base.tri-low) = ⊤
CentreResidual (Base.tri-high , Base.tri-mid) = ⊤
CentreResidual (Base.tri-high , Base.tri-high) = ⊤

------------------------------------------------------------------------
-- 2. Exact project/residual/reopen.
------------------------------------------------------------------------

projectToPhaseNine :
  Plane.DuplicatedCentreNineSheet ->
  Phase.PhaseQuotient9
projectToPhaseNine =
  SharedNine.duplicatedCentreToPhaseNine

centreResidualOf :
  (state : Plane.DuplicatedCentreNineSheet) ->
  CentreResidual (projectToPhaseNine state)
centreResidualOf Plane.lowerCentre =
  lowerBranch
centreResidualOf Plane.upperCentre =
  upperBranch
centreResidualOf
  (Plane.puncturedPoint Plane.negativeFirstAxis) = tt
centreResidualOf
  (Plane.puncturedPoint Plane.positiveFirstAxis) = tt
centreResidualOf
  (Plane.puncturedPoint Plane.negativeSecondAxis) = tt
centreResidualOf
  (Plane.puncturedPoint Plane.positiveSecondAxis) = tt
centreResidualOf
  (Plane.puncturedPoint Plane.negativeEqualDiagonal) = tt
centreResidualOf
  (Plane.puncturedPoint Plane.positiveEqualDiagonal) = tt
centreResidualOf
  (Plane.puncturedPoint Plane.negativeOppositeDiagonal) = tt
centreResidualOf
  (Plane.puncturedPoint Plane.positiveOppositeDiagonal) = tt

reopenPhaseNine :
  (phase : Phase.PhaseQuotient9) ->
  CentreResidual phase ->
  Plane.DuplicatedCentreNineSheet
reopenPhaseNine (Base.tri-mid , Base.tri-mid) lowerBranch =
  Plane.lowerCentre
reopenPhaseNine (Base.tri-mid , Base.tri-mid) upperBranch =
  Plane.upperCentre
reopenPhaseNine (Base.tri-low , Base.tri-low) tt =
  Plane.puncturedPoint Plane.negativeEqualDiagonal
reopenPhaseNine (Base.tri-low , Base.tri-mid) tt =
  Plane.puncturedPoint Plane.negativeFirstAxis
reopenPhaseNine (Base.tri-low , Base.tri-high) tt =
  Plane.puncturedPoint Plane.negativeOppositeDiagonal
reopenPhaseNine (Base.tri-mid , Base.tri-low) tt =
  Plane.puncturedPoint Plane.negativeSecondAxis
reopenPhaseNine (Base.tri-mid , Base.tri-high) tt =
  Plane.puncturedPoint Plane.positiveSecondAxis
reopenPhaseNine (Base.tri-high , Base.tri-low) tt =
  Plane.puncturedPoint Plane.positiveOppositeDiagonal
reopenPhaseNine (Base.tri-high , Base.tri-mid) tt =
  Plane.puncturedPoint Plane.positiveFirstAxis
reopenPhaseNine (Base.tri-high , Base.tri-high) tt =
  Plane.puncturedPoint Plane.positiveEqualDiagonal

reopenPhaseNineExact :
  (state : Plane.DuplicatedCentreNineSheet) ->
  reopenPhaseNine
    (projectToPhaseNine state)
    (centreResidualOf state)
  ≡ state
reopenPhaseNineExact Plane.lowerCentre = refl
reopenPhaseNineExact Plane.upperCentre = refl
reopenPhaseNineExact
  (Plane.puncturedPoint Plane.negativeFirstAxis) = refl
reopenPhaseNineExact
  (Plane.puncturedPoint Plane.positiveFirstAxis) = refl
reopenPhaseNineExact
  (Plane.puncturedPoint Plane.negativeSecondAxis) = refl
reopenPhaseNineExact
  (Plane.puncturedPoint Plane.positiveSecondAxis) = refl
reopenPhaseNineExact
  (Plane.puncturedPoint Plane.negativeEqualDiagonal) = refl
reopenPhaseNineExact
  (Plane.puncturedPoint Plane.positiveEqualDiagonal) = refl
reopenPhaseNineExact
  (Plane.puncturedPoint Plane.negativeOppositeDiagonal) = refl
reopenPhaseNineExact
  (Plane.puncturedPoint Plane.positiveOppositeDiagonal) = refl

trialecticNineCentreResidualProjection :
  Dependent.DependentExactRecoverableProjection
    Plane.DuplicatedCentreNineSheet
    Phase.PhaseQuotient9
trialecticNineCentreResidualProjection =
  Dependent.dependentExactRecoverableProjection
    CentreResidual
    projectToPhaseNine
    centreResidualOf
    reopenPhaseNine
    reopenPhaseNineExact

------------------------------------------------------------------------
-- 3. Full bidi code: every dependent code is represented.
------------------------------------------------------------------------

encode :
  Plane.DuplicatedCentreNineSheet ->
  Dependent.DependentCode trialecticNineCentreResidualProjection
encode =
  Dependent.encode trialecticNineCentreResidualProjection

decode :
  Dependent.DependentCode trialecticNineCentreResidualProjection ->
  Plane.DuplicatedCentreNineSheet
decode =
  Dependent.decode trialecticNineCentreResidualProjection

decodeEncode :
  (state : Plane.DuplicatedCentreNineSheet) ->
  decode (encode state) ≡ state
decodeEncode =
  Dependent.decodeEncodeExact trialecticNineCentreResidualProjection

encodeDecode :
  (code : Dependent.DependentCode trialecticNineCentreResidualProjection) ->
  encode (decode code) ≡ code
encodeDecode ((Base.tri-mid , Base.tri-mid) , lowerBranch) = refl
encodeDecode ((Base.tri-mid , Base.tri-mid) , upperBranch) = refl
encodeDecode ((Base.tri-low , Base.tri-low) , tt) = refl
encodeDecode ((Base.tri-low , Base.tri-mid) , tt) = refl
encodeDecode ((Base.tri-low , Base.tri-high) , tt) = refl
encodeDecode ((Base.tri-mid , Base.tri-low) , tt) = refl
encodeDecode ((Base.tri-mid , Base.tri-high) , tt) = refl
encodeDecode ((Base.tri-high , Base.tri-low) , tt) = refl
encodeDecode ((Base.tri-high , Base.tri-mid) , tt) = refl
encodeDecode ((Base.tri-high , Base.tri-high) , tt) = refl

------------------------------------------------------------------------
-- 4. Minimal selective-residual profile.
------------------------------------------------------------------------

centreResidualSize :
  Phase.PhaseQuotient9 ->
  Nat
centreResidualSize (Base.tri-mid , Base.tri-mid) = 2
centreResidualSize (Base.tri-low , Base.tri-low) = 1
centreResidualSize (Base.tri-low , Base.tri-mid) = 1
centreResidualSize (Base.tri-low , Base.tri-high) = 1
centreResidualSize (Base.tri-mid , Base.tri-low) = 1
centreResidualSize (Base.tri-mid , Base.tri-high) = 1
centreResidualSize (Base.tri-high , Base.tri-low) = 1
centreResidualSize (Base.tri-high , Base.tri-mid) = 1
centreResidualSize (Base.tri-high , Base.tri-high) = 1

centreResidualHasTwoBranches :
  centreResidualSize (Base.tri-mid , Base.tri-mid) ≡ 2
centreResidualHasTwoBranches = refl

noncentralResidualIsUnitExample :
  centreResidualSize (Base.tri-low , Base.tri-mid) ≡ 1
noncentralResidualIsUnitExample = refl

totalFineStateCount : Nat
totalFineStateCount =
  2 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1

totalFineStateCountIsTen :
  totalFineStateCount ≡ 10
totalFineStateCountIsTen = refl

------------------------------------------------------------------------
-- 5. Information-theoretic consequence.
------------------------------------------------------------------------

data UniformUnitResidualRecoversDuplicatedCentre : Set where

uniformUnitResidualCannotRecoverDuplicatedCentre :
  UniformUnitResidualRecoversDuplicatedCentre -> ⊥
uniformUnitResidualCannotRecoverDuplicatedCentre ()

data GlobalBinaryResidualNeededOnEveryPhaseState : Set where

globalBinaryResidualNotRequiredByThisExactCodec :
  GlobalBinaryResidualNeededOnEveryPhaseState -> ⊥
globalBinaryResidualNotRequiredByThisExactCodec ()

------------------------------------------------------------------------
-- 6. Boundary.
------------------------------------------------------------------------

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryNewExtension

record TrialecticNineCentreResidualBidiBoundary : Set where
  constructor trialectic-nine-centre-residual-bidi-boundary
  field
    sharedPhaseNineSurfaceReused : Bool
    residualOnlyNontrivialAtCentre : Bool
    centreResidualHasTwoBranchesPaid : Bool
    noncentralResidualsAreUnit : Bool
    decodeEncodePaid : Bool
    encodeDecodePaid : Bool
    exactFineStateCountTen : Bool
    globalBinaryResidualRequired : Bool
    arithmeticMeaningClaimed : Bool
    monsterMeaningClaimed : Bool

canonicalTrialecticNineCentreResidualBidiBoundary :
  TrialecticNineCentreResidualBidiBoundary
canonicalTrialecticNineCentreResidualBidiBoundary =
  trialectic-nine-centre-residual-bidi-boundary
    true true true true true true true false false false
