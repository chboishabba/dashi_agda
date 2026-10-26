module DASHI.Moonshine.Griess1990RationalAlbertTrialityTransportExact where

-- Same-object algebra transport on the EXISTING Griess1990/Albert owners.
--
-- Original SOURCE: Robert L. Griess Jr., "A Moufang loop, the exceptional
-- Jordan algebra, and a cubic form in 27 variables", J. Algebra 131 (1990),
-- 281-293, DOI 10.1016/0021-8693(90)90176-O.
-- SOURCE for octonion isotopy/related triples: Hurwitz; Alsaody--Gille
-- (Adv. Math. 343, 2019, 864-909). The structure below does not claim a
-- new octonion classification theorem.
--
-- Actual 27x27 rational map and finite 512/729 exact arithmetic:
-- dashi_lean4 PR #52 scripts/
-- check_griess1990_triality_rational_related_triple_recovery.py
-- and its --certificate JSON witness.
--
-- PRECISE VERIFICATION BOUNDARY:
-- The transport consequences below follow constructively from an
-- inhabitant of SameObjectRationalAlbertTransport. This module does NOT
-- yet construct such an Agda inhabitant from the three matrix certificates.
-- Exact rational SymPy PASS != Agda kernel certified witness. Moreover
-- this Albert object is NOT the Monster weight-two Griess algebra, a
-- path-cube Hamiltonian, a physical 26-dimensional string or KK geometry.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Setω)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Moonshine.Base369AlbertF3CubeHamiltonianSymmetryMaxCutExact
  as Existing

-- Rather than redeclare a Jordan algebra (already owned by Existing),
-- this record carries only the missing SAME-OBJECT transport.
record SameObjectRationalAlbertTransport (Actor : Set) : Setω where
  field
    source : Existing.SourceJordanHamiltonian Actor
    native : Existing.SourceJordanHamiltonian Actor

    toNative : Existing.J source → Existing.J native
    toSource : Existing.J native → Existing.J source

    sourceRoundTrip : (x : Existing.J source) →
      toSource (toNative x) ≡ x
    nativeRoundTrip : (y : Existing.J native) →
      toNative (toSource y) ≡ y

    -- The positive rational trace form from the ACTUAL 27D model
    -- is separately transported, rather than inferred from a set-bijection.
    TraceScalar : Set
    sourceTrace : Existing.J source → TraceScalar
    nativeTrace : Existing.J native → TraceScalar
    tracePreserved : (x : Existing.J source) →
      nativeTrace (toNative x) ≡ sourceTrace x

    unitPreserved :
      toNative (Existing.unit source) ≡ Existing.unit native

    productPreserved :
      (x y : Existing.J source) →
      toNative (Existing._∘_ source x y) ≡
      Existing._∘_ native (toNative x) (toNative y)

    -- This field is a separate, stronger SAME-ACTION obligation than
    -- the rational Jordan product map. It must NOT be inferred from
    -- 512 cubic agreements, cardinality 27 or field notation.
    actorIntertwined :
      (a : Actor) (x : Existing.J source) →
      toNative (Existing.act source a x) ≡
      Existing.act native a (toNative x)

open SameObjectRationalAlbertTransport public

-- This part requires only algebra preservation (not Actor equivariance).
leftJordanOperatorTransport :
  ∀ {Actor : Set} (R : SameObjectRationalAlbertTransport Actor)
    (h x : Existing.J (source R)) →
  toNative R (Existing.leftMultiplication (source R) h x) ≡
  Existing.leftMultiplication (native R) (toNative R h) (toNative R x)
leftJordanOperatorTransport R h x = productPreserved R h x

-- Under the independently provided same-object trace, the bilinear
-- product trace is exactly transported (no extra F4/source theorem needed).
tracePairTransport :
  ∀ {Actor : Set} (R : SameObjectRationalAlbertTransport Actor)
    (x y : Existing.J (source R)) →
  nativeTrace R
    (Existing._∘_ (native R) (toNative R x) (toNative R y))
  ≡
  sourceTrace R (Existing._∘_ (source R) x y)
tracePairTransport R x y =
  trans
    (cong (nativeTrace R) (sym (productPreserved R x y)))
    (tracePreserved R (Existing._∘_ (source R) x y))

-- Equality of source idempotents is preserved by the same source map.
idempotentTransport :
  ∀ {Actor : Set} (R : SameObjectRationalAlbertTransport Actor)
    (p : Existing.J (source R)) →
  Existing._∘_ (source R) p p ≡ p →
  Existing._∘_ (native R) (toNative R p) (toNative R p) ≡
  toNative R p
idempotentTransport R p h =
  trans (sym (productPreserved R p p)) (cong (toNative R) h)

-- Source fixed vectors remain fixed under the chosen Actor action
-- ONLY when the separately provided actorIntertwined field is paid.
fixedGeneratorTransport :
  ∀ {Actor : Set} (R : SameObjectRationalAlbertTransport Actor)
    (h : Existing.J (source R)) (a : Actor) →
  Existing.act (source R) a h ≡ h →
  Existing.act (native R) a (toNative R h) ≡ toNative R h
fixedGeneratorTransport R h a hFixed =
  trans (sym (actorIntertwined R a h)) (cong (toNative R) hFixed)

-- The operator commutation statement is transported on ACTUAL source
-- points, not on an unrelated symbolic 27-site or quantum representation.
commutationOnActualSourceImage :
  ∀ {Actor : Set} (R : SameObjectRationalAlbertTransport Actor)
    (h : Existing.J (source R))
    (C : Existing.HamiltonianCommutesWithAction (source R) h)
    (a : Actor) (x : Existing.J (source R)) →
  Existing.act (native R) a
    (Existing.leftMultiplication (native R) (toNative R h) (toNative R x))
  ≡
  Existing.leftMultiplication (native R) (toNative R h)
    (Existing.act (native R) a (toNative R x))
commutationOnActualSourceImage R h C a x =
  trans
    (cong (Existing.act (native R) a)
      (sym (productPreserved R h x)))
    (trans
      (sym (actorIntertwined R a
        (Existing.leftMultiplication (source R) h x)))
      (trans
        (cong (toNative R) (Existing.commuting C a x))
        (trans
          (productPreserved R h (Existing.act (source R) a x))
          (cong
            (Existing.leftMultiplication (native R) (toNative R h))
            (actorIntertwined R a x)))))

-- Invertibility now removes the 'only on the chosen source image' qualifier.
commutationOnEveryNativeElement :
  ∀ {Actor : Set} (R : SameObjectRationalAlbertTransport Actor)
    (h : Existing.J (source R))
    (C : Existing.HamiltonianCommutesWithAction (source R) h)
    (a : Actor) (y : Existing.J (native R)) →
  Existing.act (native R) a
    (Existing.leftMultiplication (native R) (toNative R h) y)
  ≡
  Existing.leftMultiplication (native R) (toNative R h)
    (Existing.act (native R) a y)
commutationOnEveryNativeElement R h C a y
  rewrite sym (nativeRoundTrip R y) =
  commutationOnActualSourceImage R h C a (toSource R y)

-- Consequently the existing generic stabilizer theorem transfers to the
-- native algebra WITHOUT reconstructing that theorem or claiming more:
sourceCommutationForcesNativeFixed :
  ∀ {Actor : Set} (R : SameObjectRationalAlbertTransport Actor)
    (h : Existing.J (source R))
    (C : Existing.HamiltonianCommutesWithAction (source R) h)
    (a : Actor) →
  Existing.act (native R) a (toNative R h) ≡ toNative R h
sourceCommutationForcesNativeFixed R h C a =
  fixedGeneratorTransport R h a
    (Existing.commutingJordanHamiltonianForcesFixedGenerator
      (source R) h C a)

-- Still unpaid, deliberately:
--  (1) literal Q-rational matrix inhabitants of this record;
--  (2) a genuine choice of Actor on both SAME Albert objects;
--  (3) the different Monster VOA Griess product/action;
--  (4) spatial 27-site path / zero-mean 26D / KK/AdS3 dynamics;
--  (5) original-Q F4/E6 classification and a Lean/Agda kernel receipt.
