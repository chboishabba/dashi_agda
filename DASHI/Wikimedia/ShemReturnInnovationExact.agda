module DASHI.Wikimedia.ShemReturnInnovationExact where

-- H27: signed time-update arithmetic on the original Point carrier.
-- The earlier visit is not overwritten or equated with the current visit.
-- A free innovation is a lossless residual, not a prediction constraint.
open import DASHI.Core.Prelude
open import DASHI.Wikimedia.KeyShoeNativeFieldIncidenceExact
  using (Point; add; sub)
open import DASHI.Wikimedia.KeyShoeFieldLawMovingFrameExact
  using (subAdd; addSub)

innovation : Point → Point → Point
innovation previous current = sub current previous

update : Point → Point → Point
update previous delta = add previous delta

updateFromInnovation : (previous current : Point) →
  update previous (innovation previous current) ≡ current
updateFromInnovation = addSub

innovationFromUpdate : (previous delta : Point) →
  innovation previous (update previous delta) ≡ delta
innovationFromUpdate = subAdd

-- Every candidate current state is admitted when innovation is unrestricted.
freeInnovationAdmits : (previous current : Point) →
  Σ Point (λ delta → update previous delta ≡ current)
freeInnovationAdmits previous current =
  innovation previous current , updateFromInnovation previous current

-- The exact innovation needed by a target is unique, but calculating it
-- from that target does not supply an independently predictive law.
requiredInnovationUnique : (previous current delta : Point) →
  update previous delta ≡ current →
  delta ≡ innovation previous current
requiredInnovationUnique previous current delta e =
  trans (sym (innovationFromUpdate previous delta))
    (cong (innovation previous) e)

freeInnovationCannotIdentify : (previous left right : Point) →
  (left ≡ right → ⊥) →
  ((x y : Point) →
    Σ Point (λ delta → update previous delta ≡ x) →
    Σ Point (λ delta → update previous delta ≡ y) →
    x ≡ y) → ⊥
freeInnovationCannotIdentify previous left right distinct unique =
  distinct (unique left right (freeInnovationAdmits previous left)
    (freeInnovationAdmits previous right))


-- H31: pull a genuine source admissibility predicate back along the
-- temporal update. The admissible innovations and admissible outputs
-- are inverse charts, not two independent sources of constraints.
AdmissibleOutput : (Point → Set) → Set
AdmissibleOutput allowed = Σ Point allowed

AdmissibleInnovation : Point → (Point → Set) → Set
AdmissibleInnovation previous allowed =
  Σ Point (λ delta → allowed (update previous delta))

innovationToOutput : (previous : Point) (allowed : Point → Set) →
  AdmissibleInnovation previous allowed → AdmissibleOutput allowed
innovationToOutput previous allowed (delta , evidence) =
  update previous delta , evidence

outputToInnovation : (previous : Point) (allowed : Point → Set) →
  AdmissibleOutput allowed → AdmissibleInnovation previous allowed
outputToInnovation previous allowed (current , evidence) =
  innovation previous current ,
  subst allowed (sym (updateFromInnovation previous current)) evidence

-- Value-coordinate inverse laws; no proof-irrelevance premise required.
outputRoundTripValue : (previous : Point) (allowed : Point → Set) →
  (x : AdmissibleOutput allowed) →
  fst (innovationToOutput previous allowed
       (outputToInnovation previous allowed x)) ≡ fst x
outputRoundTripValue previous allowed (current , evidence) =
  updateFromInnovation previous current

innovationRoundTripValue : (previous : Point) (allowed : Point → Set) →
  (x : AdmissibleInnovation previous allowed) →
  fst (outputToInnovation previous allowed
       (innovationToOutput previous allowed x)) ≡ fst x
innovationRoundTripValue previous allowed (delta , evidence) =
  innovationFromUpdate previous delta


-- H36: a supplied mixed difference determines the fourth corner, with
-- the same signed innovation inverse. This is a conditional local
-- reconstruction law; neither a source interaction nor global uniqueness
-- is inferred from a coordinate chart.
mixedCorner : Point → Point → Point → Point → Point
mixedCorner a b c d = sub (sub d b) (sub c a)

completeMixedCorner : Point → Point → Point → Point → Point
completeMixedCorner a b c m = add b (add (sub c a) m)

mixedAfterComplete : (a b c m : Point) →
  mixedCorner a b c (completeMixedCorner a b c m) ≡ m
mixedAfterComplete a b c m
  rewrite subAdd b (add (sub c a) m) = subAdd (sub c a) m

completeAfterMixed : (a b c d : Point) →
  completeMixedCorner a b c (mixedCorner a b c d) ≡ d
completeAfterMixed a b c d
  rewrite addSub (sub c a) (sub d b) = addSub b d


-- H37: the signed three-axis interaction is the difference between
-- two mixed faces. Given the lower face and three upper corners,
-- the fourth upper corner is recoverable from the retained cube residual.
-- This is a local BIDI coordinate law, not a Torah prediction theorem.
cubeInteraction : Point → Point → Point → Point →
  Point → Point → Point → Point → Point
cubeInteraction a b c d e f g h =
  sub (mixedCorner e f g h) (mixedCorner a b c d)

completeCubeCorner : Point → Point → Point → Point →
  Point → Point → Point → Point → Point
completeCubeCorner a b c d e f g r =
  completeMixedCorner e f g (add (mixedCorner a b c d) r)

cubeAfterComplete : (a b c d e f g r : Point) →
  cubeInteraction a b c d e f g
    (completeCubeCorner a b c d e f g r) ≡ r
cubeAfterComplete a b c d e f g r
  rewrite mixedAfterComplete e f g (add (mixedCorner a b c d) r) =
  subAdd (mixedCorner a b c d) r

completeAfterCube : (a b c d e f g h : Point) →
  completeCubeCorner a b c d e f g
    (cubeInteraction a b c d e f g h) ≡ h
completeAfterCube a b c d e f g h
  rewrite addSub (mixedCorner a b c d) (mixedCorner e f g h) =
  completeAfterMixed e f g h
