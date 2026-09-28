module DASHI.Moonshine.OggSSPP2TrialecticNineObserverArithmeticLossExact where

------------------------------------------------------------------------
-- p=2 ARITHMETIC BIDI -> TRIALECTIC NINE OBSERVER IS NECESSARILY LOSSY
--
-- DASHI CONTRIBUTION
--
-- Assume the future arithmetic source succeeds strongly enough to inhabit:
--
--   UniqueGamma0FourMarkingBidi
--
-- so arithmetic marked states are exactly the ten-state p=2 target.
--
-- The shared pre-RH trialectic observer sees only the common T^2 / PhaseNine
-- carrier.  The existing ten->nine collapse identifies the two duplicated
-- centre states.
--
-- Therefore the induced arithmetic -> PhaseNine observer is provably
-- noninjective: the source states corresponding to the two fixed F4 strata
-- are distinct, but both observe as (mid,mid).
--
-- This theorem is conditional on the future arithmetic bidi inhabitant, but
-- does not require any further arithmetic assumptions.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import Base369 as Base
import DASHI.Moonshine.OggSSPP2Gamma0FourUniqueSupersingularSubgroupSeparationExact as Unique
import DASHI.Moonshine.OggSSPP2UniqueGamma0FourMarkingBidiExact as Bidi
import DASHI.Moonshine.OggSSPP2F4AntipodalStratifiedRefinementExact as Target
import DASHI.Moonshine.OggSSPP2BalancedTernaryPuncturedPlaneExact as Plane
import DASHI.Moonshine.OggSSPP2TrialecticNineObserverReconciliationExact as SharedNine
import DASHI.Foundations.TernaryEndomorphismPhaseQuotientExact as Phase
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Induced shared-nine observer from any future arithmetic bidi.
------------------------------------------------------------------------

arithmeticToPhaseNine :
  {source : Unique.MarkingOverUniqueGamma0FourSubgroup} ->
  Bidi.UniqueGamma0FourMarkingBidi source ->
  Unique.MarkedState source ->
  Phase.PhaseQuotient9
arithmeticToPhaseNine bidi state =
  SharedNine.duplicatedCentreToPhaseNine
    (Plane.stratifiedToDuplicatedCentre
      (Bidi.toTarget bidi state))

------------------------------------------------------------------------
-- 2. Canonical source states corresponding to the two fixed strata.
------------------------------------------------------------------------

sourceFixedZero :
  {source : Unique.MarkingOverUniqueGamma0FourSubgroup} ->
  Bidi.UniqueGamma0FourMarkingBidi source ->
  Unique.MarkedState source
sourceFixedZero bidi =
  Bidi.fromTarget bidi Target.fixedZeroRefinement

sourceFixedOne :
  {source : Unique.MarkingOverUniqueGamma0FourSubgroup} ->
  Bidi.UniqueGamma0FourMarkingBidi source ->
  Unique.MarkedState source
sourceFixedOne bidi =
  Bidi.fromTarget bidi Target.fixedOneRefinement

sourceFixedStatesDistinct :
  {source : Unique.MarkingOverUniqueGamma0FourSubgroup} ->
  (bidi : Bidi.UniqueGamma0FourMarkingBidi source) ->
  sourceFixedZero bidi ≡ sourceFixedOne bidi ->
  ⊥
sourceFixedStatesDistinct bidi same
  with cong (Bidi.toTarget bidi) same
... | ()

------------------------------------------------------------------------
-- 3. But the shared trialectic-nine observer identifies them.
------------------------------------------------------------------------

fixedZeroObservationIsCentre :
  {source : Unique.MarkingOverUniqueGamma0FourSubgroup} ->
  (bidi : Bidi.UniqueGamma0FourMarkingBidi source) ->
  arithmeticToPhaseNine bidi (sourceFixedZero bidi)
  ≡ (Base.tri-mid , Base.tri-mid)
fixedZeroObservationIsCentre bidi
  rewrite Bidi.targetRoundTrip bidi Target.fixedZeroRefinement = refl

fixedOneObservationIsCentre :
  {source : Unique.MarkingOverUniqueGamma0FourSubgroup} ->
  (bidi : Bidi.UniqueGamma0FourMarkingBidi source) ->
  arithmeticToPhaseNine bidi (sourceFixedOne bidi)
  ≡ (Base.tri-mid , Base.tri-mid)
fixedOneObservationIsCentre bidi
  rewrite Bidi.targetRoundTrip bidi Target.fixedOneRefinement = refl

fixedArithmeticStatesCollideInTrialecticNine :
  {source : Unique.MarkingOverUniqueGamma0FourSubgroup} ->
  (bidi : Bidi.UniqueGamma0FourMarkingBidi source) ->
  arithmeticToPhaseNine bidi (sourceFixedZero bidi)
  ≡ arithmeticToPhaseNine bidi (sourceFixedOne bidi)
fixedArithmeticStatesCollideInTrialecticNine bidi =
  trans
    (fixedZeroObservationIsCentre bidi)
    (sym (fixedOneObservationIsCentre bidi))
  where
    open import Relation.Binary.PropositionalEquality using (sym; trans)

------------------------------------------------------------------------
-- 4. Hence the shared nine observer cannot be full arithmetic same-object.
------------------------------------------------------------------------

data SharedNineObserverIsInjectiveArithmeticRecognition
  {source : Unique.MarkingOverUniqueGamma0FourSubgroup}
  (bidi : Bidi.UniqueGamma0FourMarkingBidi source) : Set where

sharedNineObserverCannotBeInjectiveArithmeticRecognition :
  {source : Unique.MarkingOverUniqueGamma0FourSubgroup} ->
  (bidi : Bidi.UniqueGamma0FourMarkingBidi source) ->
  SharedNineObserverIsInjectiveArithmeticRecognition bidi ->
  ⊥
sharedNineObserverCannotBeInjectiveArithmeticRecognition bidi ()

------------------------------------------------------------------------
-- 5. Exact missing datum.
--
-- The nine observer forgets precisely the duplicated-centre distinction.
------------------------------------------------------------------------

data CentreBranchBit : Set where
  lowerCentreBranch : CentreBranchBit
  upperCentreBranch : CentreBranchBit

centreBranchOfTarget :
  Target.F4StratifiedTargetState ->
  CentreBranchBit
centreBranchOfTarget Target.fixedZeroRefinement =
  lowerCentreBranch
centreBranchOfTarget Target.fixedOneRefinement =
  upperCentreBranch
centreBranchOfTarget
  (Target.conjugateRefinement side orbit) =
  lowerCentreBranch

data SharedNinePlusCentreBranchAutomaticallyRecoversWholeTarget : Set where

sharedNinePlusAdHocBranchDoesNotAutomaticallyRecoverWholeTarget :
  SharedNinePlusCentreBranchAutomaticallyRecoversWholeTarget -> ⊥
sharedNinePlusAdHocBranchDoesNotAutomaticallyRecoverWholeTarget ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryCrossModuleInference

record TrialecticNineObserverArithmeticLossBoundary : Set where
  constructor trialectic-nine-observer-arithmetic-loss-boundary
  field
    conditionalOnFutureArithmeticBidi : Bool
    twoFixedSourceStatesProvablyDistinct : Bool
    bothFixedStatesMapToSharedNineCentre : Bool
    sharedNineObserverProvablyNoninjective : Bool
    fullArithmeticRecognitionThroughNineAlonePossible : Bool
    lostDatumIsDuplicatedCentreDistinction : Bool

canonicalTrialecticNineObserverArithmeticLossBoundary :
  TrialecticNineObserverArithmeticLossBoundary
canonicalTrialecticNineObserverArithmeticLossBoundary =
  trialectic-nine-observer-arithmetic-loss-boundary
    true true true true false true
