module DASHI.Foundations.Base369LayeredAttractorAndCoarseFineExact where

------------------------------------------------------------------------
-- The 3/6/9 pattern is cumulative depth:
--   3 = one local ternary horizon,
--   6 = immediate plus medium transport,
--   9 = immediate, medium, and long integration.
--
-- Separately, 11 = 1 + 10 is a coarse/fine carrier.  The coarse coordinate
-- may itself carry nominal/actual fibres, but that semantic two-one split does
-- not replace the structural 1+10 decomposition.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Fin.Base using (Fin)

open import Base369 using
  ( TriTruth
  ; tri-low
  ; tri-mid
  ; tri-high
  )
open import DASHI.Foundations.Base369SignedMembershipExact using
  ( NominalActual
  ; nominalActual
  ; nominal
  ; actual
  )

record Horizon3 : Set where
  constructor horizon3
  field
    state : TriTruth
    transport : TriTruth
    result : TriTruth

open Horizon3 public

record Depth6 : Set where
  constructor depth6
  field
    immediate : Horizon3
    medium : Horizon3

open Depth6 public

record Depth9 : Set where
  constructor depth9
  field
    firstSix : Depth6
    long : Horizon3

open Depth9 public

project9To6 : Depth9 → Depth6
project9To6 = firstSix

project6To3 : Depth6 → Horizon3
project6To3 = immediate

project9To3 : Depth9 → Horizon3
project9To3 x = immediate (firstSix x)

-- Refinement is not a destructive replacement.  A caller supplies the new
-- horizon and the projection recovers the previously established layer.
extend3To6 : Horizon3 → Horizon3 → Depth6
extend3To6 first next = depth6 first next

extend6To9 : Depth6 → Horizon3 → Depth9
extend6To9 first next = depth9 first next

projectAfterExtend3To6 :
  (first next : Horizon3) → project6To3 (extend3To6 first next) ≡ first
projectAfterExtend3To6 first next = refl

projectAfterExtend6To9 :
  (first : Depth6) → (next : Horizon3) → project9To6 (extend6To9 first next) ≡ first
projectAfterExtend6To9 first next = refl

horizon3CoordinateCount : Nat
horizon3CoordinateCount = 3

depth6CoordinateCount : Nat
depth6CoordinateCount = 6

depth9CoordinateCount : Nat
depth9CoordinateCount = 9

record LayeredAttractor (A : Set) : Set where
  constructor layeredAttractor
  field
    immediateAttractor : A
    mediumAttractor : A
    longAttractor : A

open LayeredAttractor public

record HorizonCompatible {A : Set} (target : LayeredAttractor A) : Set where
  constructor horizonCompatible
  field
    immediatePreserved : A
    mediumPreserved : A
    longPreserved : A

------------------------------------------------------------------------
-- A branch may be locally successful and globally adverse.
------------------------------------------------------------------------

record HorizonDrift : Set where
  constructor horizonDrift
  field
    immediateDrift : TriTruth
    mediumDrift : TriTruth
    longDrift : TriTruth

open HorizonDrift public

attractiveDeadEndDrift : HorizonDrift
attractiveDeadEndDrift = horizonDrift tri-high tri-low tri-low

longHorizonRecoveryDrift : HorizonDrift
longHorizonRecoveryDrift = horizonDrift tri-low tri-mid tri-high

-- A complete local horizon can coexist with open deeper horizons.
data HorizonCompletion : Set where
  horizonOpen
  horizonComplete : HorizonCompletion

record LayeredCompletion : Set where
  constructor layeredCompletion
  field
    complete3 : HorizonCompletion
    complete6 : HorizonCompletion
    complete9 : HorizonCompletion

open LayeredCompletion public

localOnlyCompletion : LayeredCompletion
localOnlyCompletion =
  layeredCompletion horizonComplete horizonOpen horizonOpen

localOnlyIsCompleteAt3 : complete3 localOnlyCompletion ≡ horizonComplete
localOnlyIsCompleteAt3 = refl

localOnlyRemainsOpenAt6 : complete6 localOnlyCompletion ≡ horizonOpen
localOnlyRemainsOpenAt6 = refl

localOnlyRemainsOpenAt9 : complete9 localOnlyCompletion ≡ horizonOpen
localOnlyRemainsOpenAt9 = refl

------------------------------------------------------------------------
-- A literal three-horizon witness where immediate success becomes a medium
-- and long-horizon adverse trajectory.  This is the typed version of the
-- attractive-dead-end example.
------------------------------------------------------------------------

positiveHorizon : Horizon3
positiveHorizon = horizon3 tri-high tri-high tri-high

adverseHorizon : Horizon3
adverseHorizon = horizon3 tri-low tri-low tri-low

attractiveDeadEnd369 : Depth9
attractiveDeadEnd369 =
  depth9
    (depth6 positiveHorizon adverseHorizon)
    adverseHorizon

attractiveDeadEndImmediate :
  project9To3 attractiveDeadEnd369 ≡ positiveHorizon
attractiveDeadEndImmediate = refl

attractiveDeadEndMedium :
  medium (project9To6 attractiveDeadEnd369) ≡ adverseHorizon
attractiveDeadEndMedium = refl

attractiveDeadEndLong :
  long attractiveDeadEnd369 ≡ adverseHorizon
attractiveDeadEndLong = refl

------------------------------------------------------------------------
-- Structural coarse/fine 11.
------------------------------------------------------------------------

record CoarseFine11 (Coarse Fine : Set) : Set where
  constructor coarseFine11
  field
    coarse1 : Coarse
    fine10 : Fin 10 → Fine

open CoarseFine11 public

coarseFineCoordinateCount : Nat
coarseFineCoordinateCount = 1 + 10

coarseFineCoordinateCountIs11 : coarseFineCoordinateCount ≡ 11
coarseFineCoordinateCountIs11 = refl

record CoarseFineReconstruction
  (Whole Coarse Fine : Set) : Set₁ where
  constructor coarseFineReconstruction
  field
    observe : Whole → CoarseFine11 Coarse Fine
    reconstruct : CoarseFine11 Coarse Fine → Whole
    reconstructAfterObserve :
      (x : Whole) → reconstruct (observe x) ≡ x

open CoarseFineReconstruction public

-- A nominal/actual pair may live inside the single coarse channel.
record CoarseWithNominalActual (A Fine : Set) : Set where
  constructor coarseWithNominalActual
  field
    coarseSemanticPair : NominalActual A
    fineRealisation : Fin 10 → Fine

open CoarseWithNominalActual public

-- Structural 1+10 and semantic nominal/actual are independent axes.  This
-- witness has a positively declared coarse state, an adverse realised coarse
-- state, and adverse fine channels.  The coarse declaration therefore cannot
-- be used as a proof that the fine realisation is aligned.
declaredPositiveRealisedAdverse11 :
  CoarseWithNominalActual TriTruth TriTruth
declaredPositiveRealisedAdverse11 =
  coarseWithNominalActual
    (nominalActual tri-high tri-low)
    (λ _ → tri-low)

nominalSideIsPositive :
  nominal (coarseSemanticPair declaredPositiveRealisedAdverse11)
  ≡ tri-high
nominalSideIsPositive = refl

actualSideIsAdverse :
  actual (coarseSemanticPair declaredPositiveRealisedAdverse11)
  ≡ tri-low
actualSideIsAdverse = refl

------------------------------------------------------------------------
-- The address alphabet never restricts the fibre ontology.
------------------------------------------------------------------------

record AddressedFibre
  (Address : Set)
  (Fibre : Address → Set) : Set₁ where
  constructor addressedFibre
  field
    address : Address
    payload : Fibre address

open AddressedFibre public

record ContinuousOrWaveCarrier
  (Address : Set)
  (Field : Set)
  (at : Address → Field) : Set₁ where
  constructor continuousOrWaveCarrier
  field
    exactField : Field
    localAddress : Address
    addressAgrees : at localAddress ≡ exactField

-- Generic n-ary/mixed carriers are admitted simply by choosing another Address.
-- Balanced ternary is the minimal signed local alphabet, not an ontological
-- claim that the payload is finite or discrete.
