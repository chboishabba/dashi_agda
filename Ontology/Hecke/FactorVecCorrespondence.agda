module Ontology.Hecke.FactorVecCorrespondence where

open import Agda.Builtin.Nat using (Nat)

open import MonsterOntos using
  (SSP; p2; p3; p5; p7; p11; p13; p17; p19; p23; p29; p31; p41; p47; p59; p71)
open import Ontology.Hecke.FactorVecInstances using
  (SupportMask; markPrime)
open import Ontology.GodelLattice renaming (v15 to mkVec15)
import Ontology.Hecke.CorrespondenceRepresentation as HC

------------------------------------------------------------------------
-- First concrete finite correspondence class on the support-mask quotient.
-- For a chosen prime p, vary a second marked prime across the full Monster
-- prime basis. This yields a genuine finite correspondence family and a true
-- sum-over-fiber Hecke operator on functions SupportMask -> Nat.

supportMaskCorrespondence : SSP → SupportMask → Ontology.GodelLattice.Vec15 SupportMask
supportMaskCorrespondence p x =
  mkVec15
    (markPrime p2  (markPrime p x))
    (markPrime p3  (markPrime p x))
    (markPrime p5  (markPrime p x))
    (markPrime p7  (markPrime p x))
    (markPrime p11 (markPrime p x))
    (markPrime p13 (markPrime p x))
    (markPrime p17 (markPrime p x))
    (markPrime p19 (markPrime p x))
    (markPrime p23 (markPrime p x))
    (markPrime p29 (markPrime p x))
    (markPrime p31 (markPrime p x))
    (markPrime p41 (markPrime p x))
    (markPrime p47 (markPrime p x))
    (markPrime p59 (markPrime p x))
    (markPrime p71 (markPrime p x))

supportMaskCorrespondenceHecke : HC.PrimeCorrespondenceHeckeOn SupportMask
supportMaskCorrespondenceHecke = record
  { correspondence = supportMaskCorrespondence
  }

supportMaskHeckeAverage : (SupportMask → Nat) → SSP → SupportMask → Nat
supportMaskHeckeAverage =
  HC.PrimeCorrespondenceHeckeOn.operator supportMaskCorrespondenceHecke
