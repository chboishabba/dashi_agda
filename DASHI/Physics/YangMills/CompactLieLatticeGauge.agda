module DASHI.Physics.YangMills.CompactLieLatticeGauge where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieGroupCore
open import DASHI.Physics.YangMills.CompactLieGroupDerived

------------------------------------------------------------------------
-- Paths over an arbitrary directed edge family.
------------------------------------------------------------------------

data Path {Vertex : Set}
    (Edge : Vertex → Vertex → Set) : Vertex → Vertex → Set where
  empty : ∀ {x} → Path Edge x x
  _▷_ : ∀ {x y z} → Edge x y → Path Edge y z → Path Edge x z

infixr 25 _▷_

GaugeField :
  ∀ {Vertex G : Set} →
  (Edge : Vertex → Vertex → Set) → Set
GaugeField {G = G} Edge =
  ∀ {x y} → Edge x y → G

GaugeTransformation : Set → Set → Set
GaugeTransformation Vertex G = Vertex → G

gaugeAction :
  ∀ {Vertex G : Set}
    {Edge : Vertex → Vertex → Set} →
  (H : Group G) →
  GaugeTransformation Vertex G →
  GaugeField Edge →
  GaugeField Edge
gaugeAction H gamma U {x} {y} edge =
  multiply H
    (multiply H (gamma x) (U edge))
    (inverse H (gamma y))

holonomy :
  ∀ {Vertex G : Set}
    {Edge : Vertex → Vertex → Set}
    {x y : Vertex} →
  (H : Group G) →
  GaugeField Edge →
  Path Edge x y →
  G
holonomy H U empty = identity H
holonomy H U (edge ▷ rest) =
  multiply H (U edge) (holonomy H U rest)

------------------------------------------------------------------------
-- Gauge covariance is proved by exact cancellation at each internal vertex.
------------------------------------------------------------------------

holonomyGaugeCovariant :
  ∀ {Vertex G : Set}
    {Edge : Vertex → Vertex → Set}
    {x y : Vertex} →
  (H : Group G) →
  (gamma : GaugeTransformation Vertex G) →
  (U : GaugeField Edge) →
  (path : Path Edge x y) →
  holonomy H (gaugeAction H gamma U) path
  ≡
  multiply H
    (multiply H (gamma x) (holonomy H U path))
    (inverse H (gamma y))
holonomyGaugeCovariant {x = x} H gamma U empty =
  sym
    (trans
      (cong (λ value → multiply H value (inverse H (gamma x)))
        (identityRight H (gamma x)))
      (inverseRight H (gamma x)))
holonomyGaugeCovariant {x = x} {y = z} H gamma U
  (_▷_ {y = y} edge rest) =
  trans
    (cong
      (multiply H (gaugeAction H gamma U edge))
      (holonomyGaugeCovariant H gamma U rest))
    (gaugeTelescope H
      (gamma x) (gamma y) (gamma z)
      (U edge) (holonomy H U rest))

------------------------------------------------------------------------
-- Class functions therefore give gauge-invariant closed-loop observables.
------------------------------------------------------------------------

record ClassFunction
    {G Scalar : Set}
    (H : Group G)
    (value : G → Scalar) : Set₁ where
  field
    conjugationInvariant :
      ∀ h x → value (conjugate H h x) ≡ value x

open ClassFunction public

loopObservable :
  ∀ {Vertex G Scalar : Set}
    {Edge : Vertex → Vertex → Set}
    {x : Vertex} →
  (H : Group G) →
  (value : G → Scalar) →
  GaugeField Edge →
  Path Edge x x →
  Scalar
loopObservable H value U path = value (holonomy H U path)

loopObservableGaugeInvariant :
  ∀ {Vertex G Scalar : Set}
    {Edge : Vertex → Vertex → Set}
    {x : Vertex} →
  (H : Group G) →
  (value : G → Scalar) →
  (classValue : ClassFunction H value) →
  (gamma : GaugeTransformation Vertex G) →
  (U : GaugeField Edge) →
  (path : Path Edge x x) →
  loopObservable H value (gaugeAction H gamma U) path
  ≡
  loopObservable H value U path
loopObservableGaugeInvariant H value classValue gamma U path =
  trans
    (cong value (holonomyGaugeCovariant H gamma U path))
    (conjugationInvariant classValue _ _)

------------------------------------------------------------------------
-- A Wilson plaquette term is precisely a class-function loop observable.
------------------------------------------------------------------------

record WilsonLocalTerm
    {Vertex G Scalar : Set}
    {Edge : Vertex → Vertex → Set}
    (H : Group G) : Set₁ where
  field
    base : Vertex
    boundary : Path Edge base base
    plaquetteValue : G → Scalar
    plaquetteClassFunction : ClassFunction H plaquetteValue

open WilsonLocalTerm public
