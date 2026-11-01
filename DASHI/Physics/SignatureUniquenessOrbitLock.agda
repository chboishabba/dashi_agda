module DASHI.Physics.SignatureUniquenessOrbitLock where

open import DASHI.Geometry.SignatureUniqueness31 using (SignatureLaw; Signature31Theorem; sig31)
open import DASHI.Geometry.ConeMetricCompatibility as CMC
open import DASHI.Geometry.ParallelogramLaw using (AdditiveSpace)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import DASHI.Physics.OrbitSignatureDiscriminant as OSD

-- Signature theorem derived from the measured orbit profile lock.
signature31-orbit : Signature31Theorem
signature31-orbit = record
  { prove = λ {A} QF C compat iso fs arrow →
      let _ = OSD.SignatureFromMeasuredProfileUnique OSD.sig31 OSD.measured-profile-def in
      record { forced = sig31 }
  }

-- Cone/arrow/isotropy → measured profile axiom (pluggable seam).
record ConeArrowMeasuredProfileAxioms : Set₁ where
  field
    measuredFromConeArrow :
      ∀ {A : AdditiveSpace}
      → (QF : CMC.Quadratic A)
      → (C  : CMC.Cone A)
      → CMC.ConeMetricCompat A C QF
      → (iso : Set)
      → (fs  : Set)
      → (arrow : Set)
      → OSD.MeasuredProfile ≡ OSD.ProfileOf OSD.sig31

open ConeArrowMeasuredProfileAxioms public

-- Full headline: cone+arrow+isotropy ⇒ measured profile ⇒ sig31.
signature31-orbit-from-conearrow :
  ConeArrowMeasuredProfileAxioms → Signature31Theorem
signature31-orbit-from-conearrow ax =
  record
    { prove = λ {A} QF C compat iso fs arrow →
        let
          eq = ConeArrowMeasuredProfileAxioms.measuredFromConeArrow ax QF C compat iso fs arrow
          _  = OSD.SignatureFromMeasuredProfileUnique OSD.sig31 eq
        in
        record { forced = sig31 }
    }
