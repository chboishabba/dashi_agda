module DASHI.Physics.Closure.ScaleLocalObservableCriterion where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Tiny finite artifact carrier.

data Artifact : Set where
  atomA atomB atomC atomD : Artifact

data Depth : Set where
  depth0 depth1 depth2 : Depth

data ProjectedArtifact : Set where
  allAtoms leftPair rightPair pointA pointB pointC pointD : ProjectedArtifact

project : Depth → Artifact → ProjectedArtifact
project depth0 _ = allAtoms
project depth1 atomA = leftPair
project depth1 atomB = leftPair
project depth1 atomC = rightPair
project depth1 atomD = rightPair
project depth2 atomA = pointA
project depth2 atomB = pointB
project depth2 atomC = pointC
project depth2 atomD = pointD

representative : Depth → ProjectedArtifact → Artifact
representative depth0 _ = atomA
representative depth1 allAtoms = atomA
representative depth1 leftPair = atomA
representative depth1 rightPair = atomC
representative depth1 pointA = atomA
representative depth1 pointB = atomA
representative depth1 pointC = atomC
representative depth1 pointD = atomC
representative depth2 allAtoms = atomA
representative depth2 leftPair = atomA
representative depth2 rightPair = atomC
representative depth2 pointA = atomA
representative depth2 pointB = atomB
representative depth2 pointC = atomC
representative depth2 pointD = atomD

representative-fiber :
  (d : Depth) →
  (x : Artifact) →
  project d x ≡ project d (representative d (project d x))
representative-fiber depth0 atomA = refl
representative-fiber depth0 atomB = refl
representative-fiber depth0 atomC = refl
representative-fiber depth0 atomD = refl
representative-fiber depth1 atomA = refl
representative-fiber depth1 atomB = refl
representative-fiber depth1 atomC = refl
representative-fiber depth1 atomD = refl
representative-fiber depth2 atomA = refl
representative-fiber depth2 atomB = refl
representative-fiber depth2 atomC = refl
representative-fiber depth2 atomD = refl

------------------------------------------------------------------------
-- Clopen/fiber equivalence: two artifacts are equivalent exactly when
-- finite-depth projection cannot distinguish them.

FiberEquivalent : Depth → Artifact → Artifact → Set
FiberEquivalent d x y = project d x ≡ project d y

Observable : Set
Observable = Artifact → Bool

Subset : Set
Subset = Artifact → Bool

record ClopenFiber (d : Depth) (subset : Subset) : Set where
  field
    constant-on-fibers :
      (x y : Artifact) →
      FiberEquivalent d x y →
      subset x ≡ subset y

------------------------------------------------------------------------
-- Concrete factorization criterion.

ConstantOnFibers : Depth → Observable → Set
ConstantOnFibers d observable =
  (x y : Artifact) →
  FiberEquivalent d x y →
  observable x ≡ observable y

record FactorsThroughProjection (d : Depth) (observable : Observable) : Set where
  field
    coarseObservable : ProjectedArtifact → Bool
    factor-law :
      (x : Artifact) →
      observable x ≡ coarseObservable (project d x)

open FactorsThroughProjection public

private
  sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
  sym refl = refl

  trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans refl q = q

  cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
  cong f refl = refl

factor-through⇒constant-on-fibers :
  {d : Depth} →
  {observable : Observable} →
  FactorsThroughProjection d observable →
  ConstantOnFibers d observable
factor-through⇒constant-on-fibers pack x y same-fiber =
  trans
    (factor-law pack x)
    (trans
      (cong (coarseObservable pack) same-fiber)
      (sym (factor-law pack y)))

constant-on-fibers⇒factor-through :
  {d : Depth} →
  {observable : Observable} →
  ConstantOnFibers d observable →
  FactorsThroughProjection d observable
constant-on-fibers⇒factor-through {d} {observable} constant =
  record
    { coarseObservable = λ p → observable (representative d p)
    ; factor-law = λ x → constant x (representative d (project d x)) (representative-fiber d x)
    }

record ObservableFactorsIffConstantOnFibers
  (d : Depth)
  (observable : Observable)
  : Set where
  field
    forward :
      FactorsThroughProjection d observable →
      ConstantOnFibers d observable
    backward :
      ConstantOnFibers d observable →
      FactorsThroughProjection d observable

finiteToyObservableCriterion :
  (d : Depth) →
  (observable : Observable) →
  ObservableFactorsIffConstantOnFibers d observable
finiteToyObservableCriterion d observable =
  record
    { forward = factor-through⇒constant-on-fibers
    ; backward = constant-on-fibers⇒factor-through
    }

------------------------------------------------------------------------
-- Canonical observable: one-step left/right projected parity.

canonicalCoarseObservable : ProjectedArtifact → Bool
canonicalCoarseObservable allAtoms = false
canonicalCoarseObservable leftPair = true
canonicalCoarseObservable rightPair = false
canonicalCoarseObservable pointA = true
canonicalCoarseObservable pointB = true
canonicalCoarseObservable pointC = false
canonicalCoarseObservable pointD = false

canonicalObservable : Observable
canonicalObservable x = canonicalCoarseObservable (project depth1 x)

canonicalFactorsThroughProjection :
  FactorsThroughProjection depth1 canonicalObservable
canonicalFactorsThroughProjection =
  record
    { coarseObservable = canonicalCoarseObservable
    ; factor-law = λ
        { atomA → refl
        ; atomB → refl
        ; atomC → refl
        ; atomD → refl
        }
    }

canonicalConstantOnFibers :
  ConstantOnFibers depth1 canonicalObservable
canonicalConstantOnFibers =
  factor-through⇒constant-on-fibers canonicalFactorsThroughProjection

canonicalCriterion :
  ObservableFactorsIffConstantOnFibers depth1 canonicalObservable
canonicalCriterion = finiteToyObservableCriterion depth1 canonicalObservable

canonicalForwardDirectionInhabited :
  ConstantOnFibers depth1 canonicalObservable
canonicalForwardDirectionInhabited =
  ObservableFactorsIffConstantOnFibers.forward canonicalCriterion
    canonicalFactorsThroughProjection

canonicalBackwardDirectionInhabited :
  FactorsThroughProjection depth1 canonicalObservable
canonicalBackwardDirectionInhabited =
  ObservableFactorsIffConstantOnFibers.backward canonicalCriterion
    canonicalConstantOnFibers

canonicalClopenFiber :
  ClopenFiber depth1 canonicalObservable
canonicalClopenFiber =
  record
    { constant-on-fibers = canonicalConstantOnFibers
    }

------------------------------------------------------------------------
-- Promotion governance flags.

scaleLocalCriterionClosedForFiniteToy : Bool
scaleLocalCriterionClosedForFiniteToy = true

continuumObservablePromoted : Bool
continuumObservablePromoted = false

physicsLawPromoted : Bool
physicsLawPromoted = false

clayPromotion : Bool
clayPromotion = false
