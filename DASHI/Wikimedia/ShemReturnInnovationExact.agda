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
