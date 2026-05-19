module Ontology.GodelScalarizationTransportDerived where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open +-*-Solver

open import MonsterOntos using
  (SSP; p2; p3; p5; p7; p11; p13; p17; p19; p23; p29; p31; p41; p47; p59; p71; toNat)
open import Ontology.GodelLattice using (FactorVec)
open import Ontology.GodelLattice renaming (v15 to mkVec15)
open import Ontology.GodelScalarization using
  (G; pow; ScalarTransportStep; scalarTransportStep; signedTransferScalarStep; scalarLaw)
import Ontology.Hecke.FactorVecSignedTransport as ST

just-injective :
  ∀ {A : Set} {x y : A} →
  just x ≡ just y → x ≡ y
just-injective refl = refl

------------------------------------------------------------------------
-- Solver-normalised scalar laws for the 15 concrete cyclic SSP transports.
------------------------------------------------------------------------

GNat : Nat → Nat → Nat → Nat → Nat
      → Nat → Nat → Nat → Nat → Nat
      → Nat → Nat → Nat → Nat → Nat → Nat
GNat A B C D E F H I J K L M N O P =
  A * (B * (C * (D * (E * (F * (H * (I * (J * (K * (L * (M * (N * (O * P)))))))))))))

GPoly : ∀ {n} → Polynomial n → Polynomial n → Polynomial n → Polynomial n → Polynomial n
       → Polynomial n → Polynomial n → Polynomial n → Polynomial n → Polynomial n
       → Polynomial n → Polynomial n → Polynomial n → Polynomial n → Polynomial n → Polynomial n
GPoly A B C D E F H I J K L M N O P =
  A :* (B :* (C :* (D :* (E :* (F :* (H :* (I :* (J :* (K :* (L :* (M :* (N :* (O :* P)))))))))))))

scalar-law-p2 :
  ∀ A B C D E F H I J K L M N O P →
  2 * GNat A (3 * B) C D E F H I J K L M N O P
    ≡
  3 * GNat (2 * A) B C D E F H I J K L M N O P
scalar-law-p2 =
  solve 15 (λ A B C D E F H I J K L M N O P →
    con 2 :* GPoly A (con 3 :* B) C D E F H I J K L M N O P :=
    con 3 :* GPoly (con 2 :* A) B C D E F H I J K L M N O P)
    refl

scalar-law-p3 :
  ∀ A B C D E F H I J K L M N O P →
  3 * GNat A B (5 * C) D E F H I J K L M N O P
    ≡
  5 * GNat A (3 * B) C D E F H I J K L M N O P
scalar-law-p3 =
  solve 15 (λ A B C D E F H I J K L M N O P →
    con 3 :* GPoly A B (con 5 :* C) D E F H I J K L M N O P :=
    con 5 :* GPoly A (con 3 :* B) C D E F H I J K L M N O P)
    refl

scalar-law-p5 :
  ∀ A B C D E F H I J K L M N O P →
  5 * GNat A B C (7 * D) E F H I J K L M N O P
    ≡
  7 * GNat A B (5 * C) D E F H I J K L M N O P
scalar-law-p5 =
  solve 15 (λ A B C D E F H I J K L M N O P →
    con 5 :* GPoly A B C (con 7 :* D) E F H I J K L M N O P :=
    con 7 :* GPoly A B (con 5 :* C) D E F H I J K L M N O P)
    refl

scalar-law-p7 :
  ∀ A B C D E F H I J K L M N O P →
  7 * GNat A B C D (11 * E) F H I J K L M N O P
    ≡
  11 * GNat A B C (7 * D) E F H I J K L M N O P
scalar-law-p7 =
  solve 15 (λ A B C D E F H I J K L M N O P →
    con 7 :* GPoly A B C D (con 11 :* E) F H I J K L M N O P :=
    con 11 :* GPoly A B C (con 7 :* D) E F H I J K L M N O P)
    refl

scalar-law-p11 :
  ∀ A B C D E F H I J K L M N O P →
  11 * GNat A B C D E (13 * F) H I J K L M N O P
    ≡
  13 * GNat A B C D (11 * E) F H I J K L M N O P
scalar-law-p11 =
  solve 15 (λ A B C D E F H I J K L M N O P →
    con 11 :* GPoly A B C D E (con 13 :* F) H I J K L M N O P :=
    con 13 :* GPoly A B C D (con 11 :* E) F H I J K L M N O P)
    refl

scalar-law-p13 :
  ∀ A B C D E F H I J K L M N O P →
  13 * GNat A B C D E F (17 * H) I J K L M N O P
    ≡
  17 * GNat A B C D E (13 * F) H I J K L M N O P
scalar-law-p13 =
  solve 15 (λ A B C D E F H I J K L M N O P →
    con 13 :* GPoly A B C D E F (con 17 :* H) I J K L M N O P :=
    con 17 :* GPoly A B C D E (con 13 :* F) H I J K L M N O P)
    refl

scalar-law-p17 :
  ∀ A B C D E F H I J K L M N O P →
  17 * GNat A B C D E F H (19 * I) J K L M N O P
    ≡
  19 * GNat A B C D E F (17 * H) I J K L M N O P
scalar-law-p17 =
  solve 15 (λ A B C D E F H I J K L M N O P →
    con 17 :* GPoly A B C D E F H (con 19 :* I) J K L M N O P :=
    con 19 :* GPoly A B C D E F (con 17 :* H) I J K L M N O P)
    refl

scalar-law-p19 :
  ∀ A B C D E F H I J K L M N O P →
  19 * GNat A B C D E F H I (23 * J) K L M N O P
    ≡
  23 * GNat A B C D E F H (19 * I) J K L M N O P
scalar-law-p19 =
  solve 15 (λ A B C D E F H I J K L M N O P →
    con 19 :* GPoly A B C D E F H I (con 23 :* J) K L M N O P :=
    con 23 :* GPoly A B C D E F H (con 19 :* I) J K L M N O P)
    refl

scalar-law-p23 :
  ∀ A B C D E F H I J K L M N O P →
  23 * GNat A B C D E F H I J (29 * K) L M N O P
    ≡
  29 * GNat A B C D E F H I (23 * J) K L M N O P
scalar-law-p23 =
  solve 15 (λ A B C D E F H I J K L M N O P →
    con 23 :* GPoly A B C D E F H I J (con 29 :* K) L M N O P :=
    con 29 :* GPoly A B C D E F H I (con 23 :* J) K L M N O P)
    refl

scalar-law-p29 :
  ∀ A B C D E F H I J K L M N O P →
  29 * GNat A B C D E F H I J K (31 * L) M N O P
    ≡
  31 * GNat A B C D E F H I J (29 * K) L M N O P
scalar-law-p29 =
  solve 15 (λ A B C D E F H I J K L M N O P →
    con 29 :* GPoly A B C D E F H I J K (con 31 :* L) M N O P :=
    con 31 :* GPoly A B C D E F H I J (con 29 :* K) L M N O P)
    refl

scalar-law-p31 :
  ∀ A B C D E F H I J K L M N O P →
  31 * GNat A B C D E F H I J K L (41 * M) N O P
    ≡
  41 * GNat A B C D E F H I J K (31 * L) M N O P
scalar-law-p31 =
  solve 15 (λ A B C D E F H I J K L M N O P →
    con 31 :* GPoly A B C D E F H I J K L (con 41 :* M) N O P :=
    con 41 :* GPoly A B C D E F H I J K (con 31 :* L) M N O P)
    refl

scalar-law-p41 :
  ∀ A B C D E F H I J K L M N O P →
  41 * GNat A B C D E F H I J K L M (47 * N) O P
    ≡
  47 * GNat A B C D E F H I J K L (41 * M) N O P
scalar-law-p41 =
  solve 15 (λ A B C D E F H I J K L M N O P →
    con 41 :* GPoly A B C D E F H I J K L M (con 47 :* N) O P :=
    con 47 :* GPoly A B C D E F H I J K L (con 41 :* M) N O P)
    refl

scalar-law-p47 :
  ∀ A B C D E F H I J K L M N O P →
  47 * GNat A B C D E F H I J K L M N (59 * O) P
    ≡
  59 * GNat A B C D E F H I J K L M (47 * N) O P
scalar-law-p47 =
  solve 15 (λ A B C D E F H I J K L M N O P →
    con 47 :* GPoly A B C D E F H I J K L M N (con 59 :* O) P :=
    con 59 :* GPoly A B C D E F H I J K L M (con 47 :* N) O P)
    refl

scalar-law-p59 :
  ∀ A B C D E F H I J K L M N O P →
  59 * GNat A B C D E F H I J K L M N O (71 * P)
    ≡
  71 * GNat A B C D E F H I J K L M N (59 * O) P
scalar-law-p59 =
  solve 15 (λ A B C D E F H I J K L M N O P →
    con 59 :* GPoly A B C D E F H I J K L M N O (con 71 :* P) :=
    con 71 :* GPoly A B C D E F H I J K L M N (con 59 :* O) P)
    refl

scalar-law-p71 :
  ∀ A B C D E F H I J K L M N O P →
  71 * GNat (2 * A) B C D E F H I J K L M N O P
    ≡
  2 * GNat A B C D E F H I J K L M N O (71 * P)
scalar-law-p71 =
  solve 15 (λ A B C D E F H I J K L M N O P →
    con 71 :* GPoly (con 2 :* A) B C D E F H I J K L M N O P :=
    con 2 :* GPoly A B C D E F H I J K L M N O (con 71 :* P))
    refl

derivedSignedTransferScalarStep :
  ∀ (p : SSP) (v target : FactorVec) →
  ST.transferPrime p v ≡ just target →
  ScalarTransportStep p (ST.nextPrime p) v
derivedSignedTransferScalarStep p2 (mkVec15 zero e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) target ()
derivedSignedTransferScalarStep p2 (mkVec15 (suc e2) e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) target refl =
  signedTransferScalarStep refl
    (scalar-law-p2 (pow 2 e2) (pow 3 e3) (pow 5 e5) (pow 7 e7) (pow 11 e11)
      (pow 13 e13) (pow 17 e17) (pow 19 e19) (pow 23 e23) (pow 29 e29)
      (pow 31 e31) (pow 41 e41) (pow 47 e47) (pow 59 e59) (pow 71 e71))
derivedSignedTransferScalarStep p3 (mkVec15 e2 zero e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) target ()
derivedSignedTransferScalarStep p3 (mkVec15 e2 (suc e3) e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) target refl =
  signedTransferScalarStep refl
    (scalar-law-p3 (pow 2 e2) (pow 3 e3) (pow 5 e5) (pow 7 e7) (pow 11 e11)
      (pow 13 e13) (pow 17 e17) (pow 19 e19) (pow 23 e23) (pow 29 e29)
      (pow 31 e31) (pow 41 e41) (pow 47 e47) (pow 59 e59) (pow 71 e71))
derivedSignedTransferScalarStep p5 (mkVec15 e2 e3 zero e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) target ()
derivedSignedTransferScalarStep p5 (mkVec15 e2 e3 (suc e5) e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) target refl =
  signedTransferScalarStep refl
    (scalar-law-p5 (pow 2 e2) (pow 3 e3) (pow 5 e5) (pow 7 e7) (pow 11 e11)
      (pow 13 e13) (pow 17 e17) (pow 19 e19) (pow 23 e23) (pow 29 e29)
      (pow 31 e31) (pow 41 e41) (pow 47 e47) (pow 59 e59) (pow 71 e71))
derivedSignedTransferScalarStep p7 (mkVec15 e2 e3 e5 zero e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) target ()
derivedSignedTransferScalarStep p7 (mkVec15 e2 e3 e5 (suc e7) e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) target refl =
  signedTransferScalarStep refl
    (scalar-law-p7 (pow 2 e2) (pow 3 e3) (pow 5 e5) (pow 7 e7) (pow 11 e11)
      (pow 13 e13) (pow 17 e17) (pow 19 e19) (pow 23 e23) (pow 29 e29)
      (pow 31 e31) (pow 41 e41) (pow 47 e47) (pow 59 e59) (pow 71 e71))
derivedSignedTransferScalarStep p11 (mkVec15 e2 e3 e5 e7 zero e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) target ()
derivedSignedTransferScalarStep p11 (mkVec15 e2 e3 e5 e7 (suc e11) e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) target refl =
  signedTransferScalarStep refl
    (scalar-law-p11 (pow 2 e2) (pow 3 e3) (pow 5 e5) (pow 7 e7) (pow 11 e11)
      (pow 13 e13) (pow 17 e17) (pow 19 e19) (pow 23 e23) (pow 29 e29)
      (pow 31 e31) (pow 41 e41) (pow 47 e47) (pow 59 e59) (pow 71 e71))
derivedSignedTransferScalarStep p13 (mkVec15 e2 e3 e5 e7 e11 zero e17 e19 e23 e29 e31 e41 e47 e59 e71) target ()
derivedSignedTransferScalarStep p13 (mkVec15 e2 e3 e5 e7 e11 (suc e13) e17 e19 e23 e29 e31 e41 e47 e59 e71) target refl =
  signedTransferScalarStep refl
    (scalar-law-p13 (pow 2 e2) (pow 3 e3) (pow 5 e5) (pow 7 e7) (pow 11 e11)
      (pow 13 e13) (pow 17 e17) (pow 19 e19) (pow 23 e23) (pow 29 e29)
      (pow 31 e31) (pow 41 e41) (pow 47 e47) (pow 59 e59) (pow 71 e71))
derivedSignedTransferScalarStep p17 (mkVec15 e2 e3 e5 e7 e11 e13 zero e19 e23 e29 e31 e41 e47 e59 e71) target ()
derivedSignedTransferScalarStep p17 (mkVec15 e2 e3 e5 e7 e11 e13 (suc e17) e19 e23 e29 e31 e41 e47 e59 e71) target refl =
  signedTransferScalarStep refl
    (scalar-law-p17 (pow 2 e2) (pow 3 e3) (pow 5 e5) (pow 7 e7) (pow 11 e11)
      (pow 13 e13) (pow 17 e17) (pow 19 e19) (pow 23 e23) (pow 29 e29)
      (pow 31 e31) (pow 41 e41) (pow 47 e47) (pow 59 e59) (pow 71 e71))
derivedSignedTransferScalarStep p19 (mkVec15 e2 e3 e5 e7 e11 e13 e17 zero e23 e29 e31 e41 e47 e59 e71) target ()
derivedSignedTransferScalarStep p19 (mkVec15 e2 e3 e5 e7 e11 e13 e17 (suc e19) e23 e29 e31 e41 e47 e59 e71) target refl =
  signedTransferScalarStep refl
    (scalar-law-p19 (pow 2 e2) (pow 3 e3) (pow 5 e5) (pow 7 e7) (pow 11 e11)
      (pow 13 e13) (pow 17 e17) (pow 19 e19) (pow 23 e23) (pow 29 e29)
      (pow 31 e31) (pow 41 e41) (pow 47 e47) (pow 59 e59) (pow 71 e71))
derivedSignedTransferScalarStep p23 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 zero e29 e31 e41 e47 e59 e71) target ()
derivedSignedTransferScalarStep p23 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 (suc e23) e29 e31 e41 e47 e59 e71) target refl =
  signedTransferScalarStep refl
    (scalar-law-p23 (pow 2 e2) (pow 3 e3) (pow 5 e5) (pow 7 e7) (pow 11 e11)
      (pow 13 e13) (pow 17 e17) (pow 19 e19) (pow 23 e23) (pow 29 e29)
      (pow 31 e31) (pow 41 e41) (pow 47 e47) (pow 59 e59) (pow 71 e71))
derivedSignedTransferScalarStep p29 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 zero e31 e41 e47 e59 e71) target ()
derivedSignedTransferScalarStep p29 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 (suc e29) e31 e41 e47 e59 e71) target refl =
  signedTransferScalarStep refl
    (scalar-law-p29 (pow 2 e2) (pow 3 e3) (pow 5 e5) (pow 7 e7) (pow 11 e11)
      (pow 13 e13) (pow 17 e17) (pow 19 e19) (pow 23 e23) (pow 29 e29)
      (pow 31 e31) (pow 41 e41) (pow 47 e47) (pow 59 e59) (pow 71 e71))
derivedSignedTransferScalarStep p31 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 zero e41 e47 e59 e71) target ()
derivedSignedTransferScalarStep p31 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 (suc e31) e41 e47 e59 e71) target refl =
  signedTransferScalarStep refl
    (scalar-law-p31 (pow 2 e2) (pow 3 e3) (pow 5 e5) (pow 7 e7) (pow 11 e11)
      (pow 13 e13) (pow 17 e17) (pow 19 e19) (pow 23 e23) (pow 29 e29)
      (pow 31 e31) (pow 41 e41) (pow 47 e47) (pow 59 e59) (pow 71 e71))
derivedSignedTransferScalarStep p41 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 zero e47 e59 e71) target ()
derivedSignedTransferScalarStep p41 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 (suc e41) e47 e59 e71) target refl =
  signedTransferScalarStep refl
    (scalar-law-p41 (pow 2 e2) (pow 3 e3) (pow 5 e5) (pow 7 e7) (pow 11 e11)
      (pow 13 e13) (pow 17 e17) (pow 19 e19) (pow 23 e23) (pow 29 e29)
      (pow 31 e31) (pow 41 e41) (pow 47 e47) (pow 59 e59) (pow 71 e71))
derivedSignedTransferScalarStep p47 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 zero e59 e71) target ()
derivedSignedTransferScalarStep p47 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 (suc e47) e59 e71) target refl =
  signedTransferScalarStep refl
    (scalar-law-p47 (pow 2 e2) (pow 3 e3) (pow 5 e5) (pow 7 e7) (pow 11 e11)
      (pow 13 e13) (pow 17 e17) (pow 19 e19) (pow 23 e23) (pow 29 e29)
      (pow 31 e31) (pow 41 e41) (pow 47 e47) (pow 59 e59) (pow 71 e71))
derivedSignedTransferScalarStep p59 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 zero e71) target ()
derivedSignedTransferScalarStep p59 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 (suc e59) e71) target refl =
  signedTransferScalarStep refl
    (scalar-law-p59 (pow 2 e2) (pow 3 e3) (pow 5 e5) (pow 7 e7) (pow 11 e11)
      (pow 13 e13) (pow 17 e17) (pow 19 e19) (pow 23 e23) (pow 29 e29)
      (pow 31 e31) (pow 41 e41) (pow 47 e47) (pow 59 e59) (pow 71 e71))
derivedSignedTransferScalarStep p71 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 zero) target ()
derivedSignedTransferScalarStep p71 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 (suc e71)) target refl =
  signedTransferScalarStep refl
    (scalar-law-p71 (pow 2 e2) (pow 3 e3) (pow 5 e5) (pow 7 e7) (pow 11 e11)
      (pow 13 e13) (pow 17 e17) (pow 19 e19) (pow 23 e23) (pow 29 e29)
      (pow 31 e31) (pow 41 e41) (pow 47 e47) (pow 59 e59) (pow 71 e71))

derivedSignedTransferScalarLaw :
  ∀ (p : SSP) (v target : FactorVec) →
  ST.transferPrime p v ≡ just target →
  toNat p * G target ≡ toNat (ST.nextPrime p) * G v
derivedSignedTransferScalarLaw p2 (mkVec15 zero e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) target ()
derivedSignedTransferScalarLaw p2 (mkVec15 (suc e2) e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) target refl =
  scalar-law-p2 (pow 2 e2) (pow 3 e3) (pow 5 e5) (pow 7 e7) (pow 11 e11)
    (pow 13 e13) (pow 17 e17) (pow 19 e19) (pow 23 e23) (pow 29 e29)
    (pow 31 e31) (pow 41 e41) (pow 47 e47) (pow 59 e59) (pow 71 e71)
derivedSignedTransferScalarLaw p3 (mkVec15 e2 zero e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) target ()
derivedSignedTransferScalarLaw p3 (mkVec15 e2 (suc e3) e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) target refl =
  scalar-law-p3 (pow 2 e2) (pow 3 e3) (pow 5 e5) (pow 7 e7) (pow 11 e11)
    (pow 13 e13) (pow 17 e17) (pow 19 e19) (pow 23 e23) (pow 29 e29)
    (pow 31 e31) (pow 41 e41) (pow 47 e47) (pow 59 e59) (pow 71 e71)
derivedSignedTransferScalarLaw p5 (mkVec15 e2 e3 zero e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) target ()
derivedSignedTransferScalarLaw p5 (mkVec15 e2 e3 (suc e5) e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) target refl =
  scalar-law-p5 (pow 2 e2) (pow 3 e3) (pow 5 e5) (pow 7 e7) (pow 11 e11)
    (pow 13 e13) (pow 17 e17) (pow 19 e19) (pow 23 e23) (pow 29 e29)
    (pow 31 e31) (pow 41 e41) (pow 47 e47) (pow 59 e59) (pow 71 e71)
derivedSignedTransferScalarLaw p7 (mkVec15 e2 e3 e5 zero e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) target ()
derivedSignedTransferScalarLaw p7 (mkVec15 e2 e3 e5 (suc e7) e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) target refl =
  scalar-law-p7 (pow 2 e2) (pow 3 e3) (pow 5 e5) (pow 7 e7) (pow 11 e11)
    (pow 13 e13) (pow 17 e17) (pow 19 e19) (pow 23 e23) (pow 29 e29)
    (pow 31 e31) (pow 41 e41) (pow 47 e47) (pow 59 e59) (pow 71 e71)
derivedSignedTransferScalarLaw p11 (mkVec15 e2 e3 e5 e7 zero e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) target ()
derivedSignedTransferScalarLaw p11 (mkVec15 e2 e3 e5 e7 (suc e11) e13 e17 e19 e23 e29 e31 e41 e47 e59 e71) target refl =
  scalar-law-p11 (pow 2 e2) (pow 3 e3) (pow 5 e5) (pow 7 e7) (pow 11 e11)
    (pow 13 e13) (pow 17 e17) (pow 19 e19) (pow 23 e23) (pow 29 e29)
    (pow 31 e31) (pow 41 e41) (pow 47 e47) (pow 59 e59) (pow 71 e71)
derivedSignedTransferScalarLaw p13 (mkVec15 e2 e3 e5 e7 e11 zero e17 e19 e23 e29 e31 e41 e47 e59 e71) target ()
derivedSignedTransferScalarLaw p13 (mkVec15 e2 e3 e5 e7 e11 (suc e13) e17 e19 e23 e29 e31 e41 e47 e59 e71) target refl =
  scalar-law-p13 (pow 2 e2) (pow 3 e3) (pow 5 e5) (pow 7 e7) (pow 11 e11)
    (pow 13 e13) (pow 17 e17) (pow 19 e19) (pow 23 e23) (pow 29 e29)
    (pow 31 e31) (pow 41 e41) (pow 47 e47) (pow 59 e59) (pow 71 e71)
derivedSignedTransferScalarLaw p17 (mkVec15 e2 e3 e5 e7 e11 e13 zero e19 e23 e29 e31 e41 e47 e59 e71) target ()
derivedSignedTransferScalarLaw p17 (mkVec15 e2 e3 e5 e7 e11 e13 (suc e17) e19 e23 e29 e31 e41 e47 e59 e71) target refl =
  scalar-law-p17 (pow 2 e2) (pow 3 e3) (pow 5 e5) (pow 7 e7) (pow 11 e11)
    (pow 13 e13) (pow 17 e17) (pow 19 e19) (pow 23 e23) (pow 29 e29)
    (pow 31 e31) (pow 41 e41) (pow 47 e47) (pow 59 e59) (pow 71 e71)
derivedSignedTransferScalarLaw p19 (mkVec15 e2 e3 e5 e7 e11 e13 e17 zero e23 e29 e31 e41 e47 e59 e71) target ()
derivedSignedTransferScalarLaw p19 (mkVec15 e2 e3 e5 e7 e11 e13 e17 (suc e19) e23 e29 e31 e41 e47 e59 e71) target refl =
  scalar-law-p19 (pow 2 e2) (pow 3 e3) (pow 5 e5) (pow 7 e7) (pow 11 e11)
    (pow 13 e13) (pow 17 e17) (pow 19 e19) (pow 23 e23) (pow 29 e29)
    (pow 31 e31) (pow 41 e41) (pow 47 e47) (pow 59 e59) (pow 71 e71)
derivedSignedTransferScalarLaw p23 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 zero e29 e31 e41 e47 e59 e71) target ()
derivedSignedTransferScalarLaw p23 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 (suc e23) e29 e31 e41 e47 e59 e71) target refl =
  scalar-law-p23 (pow 2 e2) (pow 3 e3) (pow 5 e5) (pow 7 e7) (pow 11 e11)
    (pow 13 e13) (pow 17 e17) (pow 19 e19) (pow 23 e23) (pow 29 e29)
    (pow 31 e31) (pow 41 e41) (pow 47 e47) (pow 59 e59) (pow 71 e71)
derivedSignedTransferScalarLaw p29 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 zero e31 e41 e47 e59 e71) target ()
derivedSignedTransferScalarLaw p29 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 (suc e29) e31 e41 e47 e59 e71) target refl =
  scalar-law-p29 (pow 2 e2) (pow 3 e3) (pow 5 e5) (pow 7 e7) (pow 11 e11)
    (pow 13 e13) (pow 17 e17) (pow 19 e19) (pow 23 e23) (pow 29 e29)
    (pow 31 e31) (pow 41 e41) (pow 47 e47) (pow 59 e59) (pow 71 e71)
derivedSignedTransferScalarLaw p31 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 zero e41 e47 e59 e71) target ()
derivedSignedTransferScalarLaw p31 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 (suc e31) e41 e47 e59 e71) target refl =
  scalar-law-p31 (pow 2 e2) (pow 3 e3) (pow 5 e5) (pow 7 e7) (pow 11 e11)
    (pow 13 e13) (pow 17 e17) (pow 19 e19) (pow 23 e23) (pow 29 e29)
    (pow 31 e31) (pow 41 e41) (pow 47 e47) (pow 59 e59) (pow 71 e71)
derivedSignedTransferScalarLaw p41 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 zero e47 e59 e71) target ()
derivedSignedTransferScalarLaw p41 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 (suc e41) e47 e59 e71) target refl =
  scalar-law-p41 (pow 2 e2) (pow 3 e3) (pow 5 e5) (pow 7 e7) (pow 11 e11)
    (pow 13 e13) (pow 17 e17) (pow 19 e19) (pow 23 e23) (pow 29 e29)
    (pow 31 e31) (pow 41 e41) (pow 47 e47) (pow 59 e59) (pow 71 e71)
derivedSignedTransferScalarLaw p47 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 zero e59 e71) target ()
derivedSignedTransferScalarLaw p47 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 (suc e47) e59 e71) target refl =
  scalar-law-p47 (pow 2 e2) (pow 3 e3) (pow 5 e5) (pow 7 e7) (pow 11 e11)
    (pow 13 e13) (pow 17 e17) (pow 19 e19) (pow 23 e23) (pow 29 e29)
    (pow 31 e31) (pow 41 e41) (pow 47 e47) (pow 59 e59) (pow 71 e71)
derivedSignedTransferScalarLaw p59 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 zero e71) target ()
derivedSignedTransferScalarLaw p59 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 (suc e59) e71) target refl =
  scalar-law-p59 (pow 2 e2) (pow 3 e3) (pow 5 e5) (pow 7 e7) (pow 11 e11)
    (pow 13 e13) (pow 17 e17) (pow 19 e19) (pow 23 e23) (pow 29 e29)
    (pow 31 e31) (pow 41 e41) (pow 47 e47) (pow 59 e59) (pow 71 e71)
derivedSignedTransferScalarLaw p71 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 zero) target ()
derivedSignedTransferScalarLaw p71 (mkVec15 e2 e3 e5 e7 e11 e13 e17 e19 e23 e29 e31 e41 e47 e59 (suc e71)) target refl =
  scalar-law-p71 (pow 2 e2) (pow 3 e3) (pow 5 e5) (pow 7 e7) (pow 11 e11)
    (pow 13 e13) (pow 17 e17) (pow 19 e19) (pow 23 e23) (pow 29 e29)
    (pow 31 e31) (pow 41 e41) (pow 47 e47) (pow 59 e59) (pow 71 e71)

transportScalarLaw-derived :
  ∀ (p : SSP) (v target : FactorVec) →
  ST.transferPrime p v ≡ just target →
  toNat p * G target ≡ toNat (ST.nextPrime p) * G v
transportScalarLaw-derived = derivedSignedTransferScalarLaw
