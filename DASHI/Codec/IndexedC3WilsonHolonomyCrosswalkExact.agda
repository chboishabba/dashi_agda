module DASHI.Codec.IndexedC3WilsonHolonomyCrosswalkExact where

-- H08/H10/H15 selected C3 source-owner crosswalk, not an assertion
-- that three site labels automatically form a closed Wilson loop.
-- Original group and class-function owners are reused directly.
-- Source-written; Agda kernel receipt remains OPEN.

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.YangMills.CompactLieGroupCore as Core
import DASHI.Physics.YangMills.CompactLieGroupDerived as Derived
import DASHI.Physics.YangMills.CompactLieLatticeGauge as Gauge

-- Cyclic rotation of three ORDERED group elements changes the based
-- holonomy by conjugation, not by literal element equality.
cyclicThreeIsConjugate :
  ∀ {g : Level} {G : Set g}
  (H : Core.Group G) (u v w : G) →
  Derived.conjugate H u
    (Core.multiply H v (Core.multiply H w u))
    ≡ Core.multiply H u (Core.multiply H v w)
cyclicThreeIsConjugate H u v w =
  trans
    (cong
      (λ t → Core.multiply H
        (Core.multiply H u t) (Core.inverse H u))
      (sym (Core.multiplyAssociative H v w u)))
    (trans
      (cong (λ t → Core.multiply H t (Core.inverse H u))
        (sym (Core.multiplyAssociative H u (Core.multiply H v w) u)))
      (Derived.rightInverseAction H u
        (Core.multiply H u (Core.multiply H v w))))

-- For a class-function consumer the conjugacy is invisible.
-- This specializes the already-owned original Wilson loop algebra.
cyclicThreeClassConsumer :
  ∀ {G Scalar : Set}
  (H : Core.Group G)
  (value : G → Scalar)
  (classValue : Gauge.ClassFunction H value)
  (u v w : G) →
  value (Core.multiply H v (Core.multiply H w u))
    ≡ value (Core.multiply H u (Core.multiply H v w))
cyclicThreeClassConsumer H value classValue u v w =
  trans
    (sym (Gauge.conjugationInvariant classValue u
      (Core.multiply H v (Core.multiply H w u))))
    (cong value (cyclicThreeIsConjugate H u v w))

-- Distinguish site-index cycle, group element cyclic product and
-- an actual gauge-loop realization. The former does not imply the latter.
record SelectedThreePortLoop
    {Vertex G : Set}
    (Edge : Vertex → Vertex → Set)
    (H : Core.Group G) : Set₁ where
  field
    start second third : Vertex
    firstEdge : Edge start second
    secondEdge : Edge second third
    thirdEdge : Edge third start

    linkField : Gauge.GaugeField {Vertex = Vertex} {G = G} Edge

  firstProduct : G
  firstProduct = Core.multiply H
    (linkField start second firstEdge)
    (Core.multiply H
      (linkField second third secondEdge)
      (linkField third start thirdEdge))

  secondProduct : G
  secondProduct = Core.multiply H
    (linkField second third secondEdge)
    (Core.multiply H
      (linkField third start thirdEdge)
      (linkField start second firstEdge))

  cyclicProductsConjugate :
    Derived.conjugate H (linkField start second firstEdge)
      secondProduct ≡ firstProduct
  cyclicProductsConjugate =
    cyclicThreeIsConjugate H
      (linkField start second firstEdge)
      (linkField second third secondEdge)
      (linkField third start thirdEdge)
