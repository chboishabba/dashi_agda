module Ontology.Hecke.FactorVecMultiLaneDefects where

open import Agda.Builtin.Bool     using (Bool; true; false)
open import Agda.Builtin.Nat      using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)

open import Ontology.GodelLattice using (FactorVec)
open import Ontology.Hecke.Scan as HS
open import Ontology.Hecke.FactorVecSignedScan using
  (factorVecSignedSignature; signatureTrueCount; SignedMotif; factorVecSignedMotif)
open import Ontology.Hecke.FactorVecMultiLaneTransport using
  (PairMode; pairLegal; factorVecMultiLaneTransport)
import Ontology.Hecke.MultiLaneSignedTransport as HM

------------------------------------------------------------------------
-- Compare the signed scan before and after a multi-lane move. This stays on
-- the representation layer and treats defects as changes in scan observables,
-- not as quotient descent.

pairTransportOrStay : PairMode → FactorVec → FactorVec
pairTransportOrStay =
  HM.MultiLaneSignedTransportOn.transportOrStay factorVecMultiLaneTransport

pairPreSignature : PairMode → FactorVec → HS.Sig15
pairPreSignature m v = factorVecSignedSignature v

pairPostSignature : PairMode → FactorVec → HS.Sig15
pairPostSignature m v = factorVecSignedSignature (pairTransportOrStay m v)

bitDiff : Bool → Bool → Nat
bitDiff true  true  = zero
bitDiff false false = zero
bitDiff _     _     = suc zero

bitDiff-refl : ∀ b → bitDiff b b ≡ zero
bitDiff-refl true  = refl
bitDiff-refl false = refl

signatureDrift : HS.Sig15 → HS.Sig15 → Nat
signatureDrift
  (HS.sig15 a2 a3 a5 a7 a11 a13 a17 a19 a23 a29 a31 a41 a47 a59 a71)
  (HS.sig15 b2 b3 b5 b7 b11 b13 b17 b19 b23 b29 b31 b41 b47 b59 b71) =
  bitDiff a2 b2 + bitDiff a3 b3 + bitDiff a5 b5 + bitDiff a7 b7 + bitDiff a11 b11
    + bitDiff a13 b13 + bitDiff a17 b17 + bitDiff a19 b19 + bitDiff a23 b23 + bitDiff a29 b29
    + bitDiff a31 b31 + bitDiff a41 b41 + bitDiff a47 b47 + bitDiff a59 b59 + bitDiff a71 b71

signatureDrift-refl : ∀ s → signatureDrift s s ≡ zero
signatureDrift-refl (HS.sig15 b2 b3 b5 b7 b11 b13 b17 b19 b23 b29 b31 b41 b47 b59 b71)
  rewrite bitDiff-refl b2
        | bitDiff-refl b3
        | bitDiff-refl b5
        | bitDiff-refl b7
        | bitDiff-refl b11
        | bitDiff-refl b13
        | bitDiff-refl b17
        | bitDiff-refl b19
        | bitDiff-refl b23
        | bitDiff-refl b29
        | bitDiff-refl b31
        | bitDiff-refl b41
        | bitDiff-refl b47
        | bitDiff-refl b59
        | bitDiff-refl b71 = refl

pairSignatureDrift : PairMode → FactorVec → Nat
pairSignatureDrift m v = signatureDrift (pairPreSignature m v) (pairPostSignature m v)

data PairDefectClass : Set where
  Stable Repatterning Contractive Expansive : PairDefectClass

compareTrueCounts : Nat → Nat → PairDefectClass
compareTrueCounts zero    zero    = Repatterning
compareTrueCounts zero    (suc _) = Expansive
compareTrueCounts (suc _) zero    = Contractive
compareTrueCounts (suc n) (suc m) = compareTrueCounts n m

pairDefectClass : PairMode → FactorVec → PairDefectClass
pairDefectClass m v with pairSignatureDrift m v
... | zero = Stable
... | suc _ = compareTrueCounts
               (signatureTrueCount (pairPreSignature m v))
               (signatureTrueCount (pairPostSignature m v))

pairPreMotif : PairMode → FactorVec → SignedMotif
pairPreMotif m v = factorVecSignedMotif v

pairPostMotif : PairMode → FactorVec → SignedMotif
pairPostMotif m v = factorVecSignedMotif (pairTransportOrStay m v)

pairTransportOrStay-illegal :
  ∀ m v →
  pairLegal m v ≡ false →
  pairTransportOrStay m v ≡ v
pairTransportOrStay-illegal m v legalEq =
  HM.MultiLaneSignedTransportOn.transportOrStay-sound₂
    factorVecMultiLaneTransport m v
    (HM.MultiLaneSignedTransportOn.illegal-fails
      factorVecMultiLaneTransport m v legalEq)

pairPrePostSignature-illegal :
  ∀ m v →
  pairLegal m v ≡ false →
  pairPreSignature m v ≡ pairPostSignature m v
pairPrePostSignature-illegal m v legalEq rewrite pairTransportOrStay-illegal m v legalEq = refl

pairPrePostMotif-illegal :
  ∀ m v →
  pairLegal m v ≡ false →
  pairPreMotif m v ≡ pairPostMotif m v
pairPrePostMotif-illegal m v legalEq rewrite pairTransportOrStay-illegal m v legalEq = refl

pairSignatureDrift-illegal :
  ∀ m v →
  pairLegal m v ≡ false →
  pairSignatureDrift m v ≡ zero
pairSignatureDrift-illegal m v legalEq
  rewrite pairTransportOrStay-illegal m v legalEq
        | signatureDrift-refl (pairPreSignature m v) = refl

pairDefectClass-illegal :
  ∀ m v →
  pairLegal m v ≡ false →
  pairDefectClass m v ≡ Stable
pairDefectClass-illegal m v legalEq
  rewrite pairSignatureDrift-illegal m v legalEq = refl

record PairDefectProfile : Set where
  constructor pairDefectProfile
  field
    preSignature  : HS.Sig15
    postSignature : HS.Sig15
    drift         : Nat
    preMotif      : SignedMotif
    postMotif     : SignedMotif
    defect        : PairDefectClass

pairDefectProfileOf : PairMode → FactorVec → PairDefectProfile
pairDefectProfileOf m v = pairDefectProfile
  (pairPreSignature m v)
  (pairPostSignature m v)
  (pairSignatureDrift m v)
  (pairPreMotif m v)
  (pairPostMotif m v)
  (pairDefectClass m v)
