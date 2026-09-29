{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CoarseObservableFactorisationBidiExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Core.CoarseFineFabricCalculusExact as Fabric

------------------------------------------------------------------------
-- Consumer-relative coarse recovery: a theorem about the *actual*
-- projection and the *actual* observable, not a new dynamics compiler.
--
-- Without an exhibited section, constancy on projection fibres alone
-- does not construct a total function on an arbitrary abstract Coarse.
-- The section below supplies exactly that missing constructive data.
------------------------------------------------------------------------

record SplitProjection (Fine Coarse : Set) : Set where
  field
    project : Fine → Coarse
    section : Coarse → Fine
    sectionRightInverse : (c : Coarse) → project (section c) ≡ c

open SplitProjection public

record FibreInvariant
    {Fine Coarse Observation : Set}
    (projection : SplitProjection Fine Coarse)
    (observe : Fine → Observation) : Set where
  field
    sameCoarseSameObservable :
      (x y : Fine) →
      project projection x ≡ project projection y →
      observe x ≡ observe y

open FibreInvariant public

coarseObservable :
  ∀ {Fine Coarse Observation : Set}
    (projection : SplitProjection Fine Coarse)
    (observe : Fine → Observation) →
  Coarse → Observation
coarseObservable projection observe c =
  observe (section projection c)

factorisationFromFibreInvariance :
  ∀ {Fine Coarse Observation : Set}
    (projection : SplitProjection Fine Coarse)
    (observe : Fine → Observation) →
  FibreInvariant projection observe →
  (x : Fine) →
  observe x ≡ coarseObservable projection observe (project projection x)
factorisationFromFibreInvariance projection observe invariant x =
  sameCoarseSameObservable invariant x
    (section projection (project projection x))
    (sym (sectionRightInverse projection (project projection x)))

fibreInvarianceFromFactorisation :
  ∀ {Fine Coarse Observation : Set}
    (projection : SplitProjection Fine Coarse)
    (observe : Fine → Observation)
    (coarseObserve : Coarse → Observation) →
  ((x : Fine) → observe x ≡ coarseObserve (project projection x)) →
  FibreInvariant projection observe
fibreInvarianceFromFactorisation projection observe coarseObserve factors =
  record
    { sameCoarseSameObservable = λ x y same →
        trans (factors x)
          (trans (cong coarseObserve same) (sym (factors y)))
    }

-- The reverse branch directly reuses the repository's earlier exact
-- projection-collision no-go.  No separate proof notion is invented.
collisionRefutesEveryCoarsePrediction :
  ∀ {Fine Coarse Observation : Set}
    (project : Fine → Coarse)
    (observe : Fine → Observation) →
  Fabric.ProjectionCollision project observe →
  (candidate : Coarse → Observation) →
  ((x : Fine) → observe x ≡ candidate (project x)) →
  ⊥
collisionRefutesEveryCoarsePrediction project observe collision candidate factors =
  Fabric.consumerCannotFactorThroughProjection collision candidate factors

-- A concrete two-state regression: one coarse address erases a signed
-- distinction. This is an information-loss fixture, NOT a physical
-- Einstein/QFT or CMS prediction.
data FineSign : Set where
  positive : FineSign
  negative : FineSign

data OneCoarse : Set where
  one : OneCoarse

projectSign : FineSign → OneCoarse
projectSign _ = one

observeSign : FineSign → FineSign
observeSign x = x

positiveNotNegative : positive ≡ negative → ⊥
positiveNotNegative ()

signCollision : Fabric.ProjectionCollision projectSign observeSign
signCollision = record
  { Fabric.ProjectionCollision.left = positive
  ; Fabric.ProjectionCollision.right = negative
  ; Fabric.ProjectionCollision.sameProjection = refl
  ; Fabric.ProjectionCollision.consumerSeparates = positiveNotNegative
  }

noSignPredictionFromCoarse :
  (candidate : OneCoarse → FineSign) →
  ((x : FineSign) → observeSign x ≡ candidate (projectSign x)) →
  ⊥
noSignPredictionFromCoarse =
  collisionRefutesEveryCoarsePrediction projectSign observeSign signCollision

-- A different consumer can be represented on exactly the same coarse
-- projection: only the *declared observable* changes.
observeAddress : FineSign → OneCoarse
observeAddress = projectSign

addressFactors :
  (x : FineSign) → observeAddress x ≡ (λ c → c) (projectSign x)
addressFactors _ = refl
