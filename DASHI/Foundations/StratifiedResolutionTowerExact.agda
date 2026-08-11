module DASHI.Foundations.StratifiedResolutionTowerExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Saunders Mac Lane,
-- "Categories for the Working Mathematician", second edition,
-- Springer, 1998.
-- DOI: 10.1007/978-1-4757-4721-8.
--
-- Mark Goresky and Robert MacPherson,
-- "Stratified Morse Theory",
-- Springer, 1988.
-- DOI: 10.1007/978-3-642-71714-7.
--
-- DASHI CONTRIBUTION
--
-- Separate three notions that had previously been compressed into one
-- coarse/fine slogan:
--   1. a bare inverse system of resolution quotients;
--   2. stratum-indexed fibre models whose fibre type may jump;
--   3. the compatible-history object representing an inverse-limit point.
--
-- A bare tower does NOT assume a chosen lift.  A MultiscaleCarrier from the
-- existing MDL layer is stronger: every projection carries a chosen section.
-- This module records that distinction explicitly instead of silently turning
-- every quotient into a global product.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.MultiscaleMDL as MDL
import DASHI.Foundations.CoarseMetricPushforward as Coarse

------------------------------------------------------------------------
-- Minimal resolution tower.
------------------------------------------------------------------------

record ResolutionTower : Set₁ where
  field
    Carrier : Nat → Set
    project : ∀ {r} → Carrier (suc r) → Carrier r

open ResolutionTower public

oneStepProjection :
  (tower : ResolutionTower) →
  Nat →
  Coarse.Projection
oneStepProjection tower r = record
  { FineCarrier = Carrier tower (suc r)
  ; CoarseCarrier = Carrier tower r
  ; project = project tower
  }

oneStepFibre :
  (tower : ResolutionTower) →
  (r : Nat) →
  Carrier tower r →
  Set
oneStepFibre tower r coarse =
  Coarse.Fibre (oneStepProjection tower r) coarse

------------------------------------------------------------------------
-- A movable coarse/fine cut.  The same level is fine relative to its
-- predecessor and coarse relative to its successor.
------------------------------------------------------------------------

record CoarseFineCut
    (tower : ResolutionTower)
    (r : Nat) : Set where
  constructor coarseFineCut
  field
    fineState : Carrier tower (suc r)
    coarseState : Carrier tower r
    projectsTo : project tower fineState ≡ coarseState

open CoarseFineCut public

cutFromFine :
  ∀ {tower : ResolutionTower} {r} →
  Carrier tower (suc r) →
  CoarseFineCut tower r
cutFromFine {tower} fine =
  coarseFineCut fine (project tower fine) refl

record MiddleLevelRole
    (tower : ResolutionTower)
    (r : Nat) : Set where
  constructor middleLevelRole
  field
    middle : Carrier tower (suc r)
    coarseShadow : Carrier tower r
    finerWitness : Carrier tower (suc (suc r))
    middleIsFineOverCoarse : project tower middle ≡ coarseShadow
    middleIsCoarseUnderFiner : project tower finerWitness ≡ middle

open MiddleLevelRole public

------------------------------------------------------------------------
-- Split towers are a STRICTLY STRONGER structure.  They have a chosen lift
-- at every level with project(lift x) = x.
------------------------------------------------------------------------

record SplitResolutionStructure
    (tower : ResolutionTower) : Set₁ where
  field
    lift : ∀ {r} → Carrier tower r → Carrier tower (suc r)
    project-lift :
      ∀ {r} (x : Carrier tower r) →
      project tower (lift x) ≡ x

open SplitResolutionStructure public

resolutionTowerFromMultiscale :
  MDL.MultiscaleCarrier →
  ResolutionTower
resolutionTowerFromMultiscale tower = record
  { Carrier = MDL.Carrier tower
  ; project = MDL.project tower
  }

multiscaleCarriesChosenSplit :
  (tower : MDL.MultiscaleCarrier) →
  SplitResolutionStructure (resolutionTowerFromMultiscale tower)
multiscaleCarriesChosenSplit tower = record
  { lift = MDL.lift tower
  ; project-lift = MDL.project-lift tower
  }

------------------------------------------------------------------------
-- Stratum-indexed fibre type.
--
-- The equivalence is explicit and local to the coarse point's stratum.  This
-- allows a regular point, symmetry-fixed point, and singular point to carry
-- genuinely different fibre models.
------------------------------------------------------------------------

record FibreEquivalence (A B : Set) : Set where
  constructor fibreEquivalence
  field
    to : A → B
    from : B → A
    from-to : (a : A) → from (to a) ≡ a
    to-from : (b : B) → to (from b) ≡ b

open FibreEquivalence public

record StratifiedProjection
    (P : Coarse.Projection) : Set₁ where
  field
    Stratum : Set
    stratumOf : Coarse.CoarseCarrier P → Stratum
    FibreModel : Stratum → Set
    fibreEquivalenceAt :
      (coarse : Coarse.CoarseCarrier P) →
      FibreEquivalence
        (Coarse.Fibre P coarse)
        (FibreModel (stratumOf coarse))

open StratifiedProjection public

record StratifiedResolutionTower
    (tower : ResolutionTower) : Set₁ where
  field
    stratifiedStep :
      (r : Nat) →
      StratifiedProjection (oneStepProjection tower r)

open StratifiedResolutionTower public

------------------------------------------------------------------------
-- Concrete singular-fibre witness.
--
-- The regular stratum has two fine realisations while the fixed stratum has
-- one.  This is a finite executable witness that "stratified" is doing real
-- work: the fibre family is not globally constant.
------------------------------------------------------------------------

data ToyCoarse : Set where
  toyRegular toyFixed : ToyCoarse

data ToyFine : Set where
  regularFineLeft regularFineRight fixedFine : ToyFine

toyProject : ToyFine → ToyCoarse
toyProject regularFineLeft = toyRegular
toyProject regularFineRight = toyRegular
toyProject fixedFine = toyFixed

toyProjection : Coarse.Projection
toyProjection = record
  { FineCarrier = ToyFine
  ; CoarseCarrier = ToyCoarse
  ; project = toyProject
  }

data ToyStratum : Set where
  regularStratum fixedStratum : ToyStratum

data RegularFibreModel : Set where
  regularLeft regularRight : RegularFibreModel

data FixedFibreModel : Set where
  fixedOnly : FixedFibreModel

toyStratumOf : ToyCoarse → ToyStratum
toyStratumOf toyRegular = regularStratum
toyStratumOf toyFixed = fixedStratum

toyFibreModel : ToyStratum → Set
toyFibreModel regularStratum = RegularFibreModel
toyFibreModel fixedStratum = FixedFibreModel

regularTo : Coarse.Fibre toyProjection toyRegular → RegularFibreModel
regularTo (regularFineLeft , refl) = regularLeft
regularTo (regularFineRight , refl) = regularRight
regularTo (fixedFine , ())

regularFrom : RegularFibreModel → Coarse.Fibre toyProjection toyRegular
regularFrom regularLeft = regularFineLeft , refl
regularFrom regularRight = regularFineRight , refl

regularFromTo :
  (fibre : Coarse.Fibre toyProjection toyRegular) →
  regularFrom (regularTo fibre) ≡ fibre
regularFromTo (regularFineLeft , refl) = refl
regularFromTo (regularFineRight , refl) = refl
regularFromTo (fixedFine , ())

regularToFrom :
  (model : RegularFibreModel) →
  regularTo (regularFrom model) ≡ model
regularToFrom regularLeft = refl
regularToFrom regularRight = refl

fixedTo : Coarse.Fibre toyProjection toyFixed → FixedFibreModel
fixedTo (regularFineLeft , ())
fixedTo (regularFineRight , ())
fixedTo (fixedFine , refl) = fixedOnly

fixedFrom : FixedFibreModel → Coarse.Fibre toyProjection toyFixed
fixedFrom fixedOnly = fixedFine , refl

fixedFromTo :
  (fibre : Coarse.Fibre toyProjection toyFixed) →
  fixedFrom (fixedTo fibre) ≡ fibre
fixedFromTo (regularFineLeft , ())
fixedFromTo (regularFineRight , ())
fixedFromTo (fixedFine , refl) = refl

fixedToFrom :
  (model : FixedFibreModel) →
  fixedTo (fixedFrom model) ≡ model
fixedToFrom fixedOnly = refl

toyFibreEquivalenceAt :
  (coarse : ToyCoarse) →
  FibreEquivalence
    (Coarse.Fibre toyProjection coarse)
    (toyFibreModel (toyStratumOf coarse))
toyFibreEquivalenceAt toyRegular =
  fibreEquivalence regularTo regularFrom regularFromTo regularToFrom
toyFibreEquivalenceAt toyFixed =
  fibreEquivalence fixedTo fixedFrom fixedFromTo fixedToFrom

toyStratifiedProjection : StratifiedProjection toyProjection
toyStratifiedProjection = record
  { Stratum = ToyStratum
  ; stratumOf = toyStratumOf
  ; FibreModel = toyFibreModel
  ; fibreEquivalenceAt = toyFibreEquivalenceAt
  }

------------------------------------------------------------------------
-- Exact inverse-limit point interface.
--
-- This is the compatible-history definition: an element gives one state at
-- every finite resolution together with the one-step coherence law.
------------------------------------------------------------------------

record InverseLimitPoint
    (tower : ResolutionTower) : Set₁ where
  constructor inverseLimitPoint
  field
    atResolution : (r : Nat) → Carrier tower r
    coherent :
      (r : Nat) →
      project tower (atResolution (suc r)) ≡ atResolution r

open InverseLimitPoint public

coarseShadow :
  ∀ {tower : ResolutionTower} →
  InverseLimitPoint tower →
  (r : Nat) →
  Carrier tower r
coarseShadow point r = atResolution point r

coarseShadowCoherence :
  ∀ {tower : ResolutionTower}
    (point : InverseLimitPoint tower)
    (r : Nat) →
  project tower (coarseShadow point (suc r))
  ≡ coarseShadow point r
coarseShadowCoherence point r = coherent point r

------------------------------------------------------------------------
-- Observable transport.
--
-- Pulling a coarse observable upward along project is the exact version of
-- "stretch the coarse sheet across the fine sheet".  It is constant on each
-- projection fibre by construction.
------------------------------------------------------------------------

ObservableAt :
  (tower : ResolutionTower) →
  Nat →
  Set →
  Set
ObservableAt tower r Value = Carrier tower r → Value

pullbackObservable :
  ∀ {tower : ResolutionTower} {r Value} →
  ObservableAt tower r Value →
  ObservableAt tower (suc r) Value
pullbackObservable {tower} observable fine =
  observable (project tower fine)

pullbackConstantOnFibre :
  ∀ {tower : ResolutionTower} {r Value}
    (observable : ObservableAt tower r Value)
    {left right : Carrier tower (suc r)} →
  project tower left ≡ project tower right →
  pullbackObservable observable left
  ≡ pullbackObservable observable right
pullbackConstantOnFibre observable refl = refl

------------------------------------------------------------------------
-- Coarse aggregation is additional structure, not supplied by a quotient
-- alone.  Once supplied, coarse-then-stretch is a genuine endomorphism on
-- fine observables.
------------------------------------------------------------------------

record FibreAggregator
    (tower : ResolutionTower)
    (r : Nat)
    (Value : Set) : Set₁ where
  field
    aggregate :
      ObservableAt tower (suc r) Value →
      ObservableAt tower r Value

open FibreAggregator public

coarseThenStretch :
  ∀ {tower : ResolutionTower} {r Value} →
  FibreAggregator tower r Value →
  ObservableAt tower (suc r) Value →
  ObservableAt tower (suc r) Value
coarseThenStretch aggregator fineObservable =
  pullbackObservable (aggregate aggregator fineObservable)

------------------------------------------------------------------------
-- Claim boundary.
------------------------------------------------------------------------

record StratifiedResolutionBoundary : Set where
  constructor stratifiedResolutionBoundary
  field
    everyResolutionProjectionHasChosenGlobalLift : Bool
    everyResolutionProjectionHasChosenGlobalLiftIsFalse :
      everyResolutionProjectionHasChosenGlobalLift ≡ false

    sameCoarsePointDeterminesUniqueFineRealisation : Bool
    sameCoarsePointDeterminesUniqueFineRealisationIsFalse :
      sameCoarsePointDeterminesUniqueFineRealisation ≡ false

    fibreTypeMustBeConstantAcrossAllStrata : Bool
    fibreTypeMustBeConstantAcrossAllStrataIsFalse :
      fibreTypeMustBeConstantAcrossAllStrata ≡ false

    inverseLimitPointIsArbitraryUnrelatedSequence : Bool
    inverseLimitPointIsArbitraryUnrelatedSequenceIsFalse :
      inverseLimitPointIsArbitraryUnrelatedSequence ≡ false

    coarseFineIsAnIntrinsicAbsoluteLevelLabel : Bool
    coarseFineIsAnIntrinsicAbsoluteLevelLabelIsFalse :
      coarseFineIsAnIntrinsicAbsoluteLevelLabel ≡ false

canonicalStratifiedResolutionBoundary : StratifiedResolutionBoundary
canonicalStratifiedResolutionBoundary =
  stratifiedResolutionBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
