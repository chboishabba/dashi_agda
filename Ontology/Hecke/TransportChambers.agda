module Ontology.Hecke.TransportChambers where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool     using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)

import Ontology.Hecke.MultiLaneSignedTransport as HM

------------------------------------------------------------------------
-- Chamber data packages exactly the information needed to recover legality
-- for a chosen mode family. Compression to smaller chamber carriers can be
-- studied later; this layer records the exact theorem surface first.

record ChamberWitnessOn (Mode S C : Set) : Set₁ where
  field
    transport      : HM.MultiLaneSignedTransportOn Mode S
    chamber        : S → C
    legalOnChamber : Mode → C → Bool

    legal-sound :
      ∀ m s →
      HM.MultiLaneSignedTransportOn.legal transport m s ≡ legalOnChamber m (chamber s)

  sameChamber : S → S → Set
  sameChamber x y = chamber x ≡ chamber y

  legal-respects-sameChamber :
    ∀ m x y →
    sameChamber x y →
    HM.MultiLaneSignedTransportOn.legal transport m x ≡
    HM.MultiLaneSignedTransportOn.legal transport m y
  legal-respects-sameChamber m x y chamberEq =
    trans
      (legal-sound m x)
      (trans
        (cong (legalOnChamber m) chamberEq)
        (sym (legal-sound m y)))
