module DASHI.Mathematics.Symmetry.TrialecticT9DescentD4NaturalityExact where

-- Transport compatible T4 local sections by gluing to their genuine
-- global T9 observer, acting on positions, and restricting again.
-- This preserves overlap constraints by construction; it does not
-- assert a false same-index local rotation rule.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)
import DASHI.Reasoning.Trialectic369DescentNaturalityExact as Desc
import DASHI.Mathematics.Symmetry.TrialecticT9D4ConfigurationActionExact as D4

rotateFamily : Desc.DyadicMatchingFamily → Desc.DyadicMatchingFamily
rotateFamily f =
  Desc.observerMatchingFamily (D4.rotate (Desc.glueDyadic f))

reflectFamily : Desc.DyadicMatchingFamily → Desc.DyadicMatchingFamily
reflectFamily f =
  Desc.observerMatchingFamily (D4.reflect (Desc.glueDyadic f))

rotateGlobalNaturality :
  (f : Desc.DyadicMatchingFamily) →
  Desc.glueDyadic (rotateFamily f) ≡
  D4.rotate (Desc.glueDyadic f)
rotateGlobalNaturality f =
  Desc.observerGlueRoundTrip (D4.rotate (Desc.glueDyadic f))

reflectGlobalNaturality :
  (f : Desc.DyadicMatchingFamily) →
  Desc.glueDyadic (reflectFamily f) ≡
  D4.reflect (Desc.glueDyadic f)
reflectGlobalNaturality f =
  Desc.observerGlueRoundTrip (D4.reflect (Desc.glueDyadic f))

rotateRestrictedNaturality :
  (f : Desc.DyadicMatchingFamily) →
  rotateFamily f ≡
  Desc.observerMatchingFamily (D4.rotate (Desc.glueDyadic f))
rotateRestrictedNaturality f = refl

-- Direct source-level rechart of the transformed AB/BC/CA restrictions,
-- not merely preservation of total T9 state count.
