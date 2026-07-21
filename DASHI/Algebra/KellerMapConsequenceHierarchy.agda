module DASHI.Algebra.KellerMapConsequenceHierarchy where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

open import DASHI.Core.OperatorTypes using (Invertible)
open Invertible
open import Verification.JacobianCounterexampleKernel as J
  using
    ( ¬_
    ; Injective
    ; invertibleImpliesInjective
    ; Point3
    ; PolynomialMap3
    ; applyPolynomialMap3
    ; KellerMap3
    ; polynomial
    ; alpogeKellerMap
    ; F-notInjective
    ; PaddedKellerMap
    ; alpogePaddedKellerMap
    ; paddedF-notInjective
    )

------------------------------------------------------------------------
-- The actual conclusion “polynomial automorphism” is stronger than bare
-- set-theoretic invertibility, which is stronger than injectivity.  The
-- counterexample refutes even the weakest of the three universal principles.

record PolynomialAutomorphism3 (map : PolynomialMap3) : Set where
  constructor polynomialAutomorphism3
  field
    inversePolynomial : PolynomialMap3
    leftPolynomialInverse :
      (p : Point3) →
      applyPolynomialMap3 inversePolynomial
        (applyPolynomialMap3 map p)
        ≡ p
    rightPolynomialInverse :
      (p : Point3) →
      applyPolynomialMap3 map
        (applyPolynomialMap3 inversePolynomial p)
        ≡ p

polynomialAutomorphismImpliesInvertible :
  ∀ {map : PolynomialMap3} →
  PolynomialAutomorphism3 map →
  Invertible (applyPolynomialMap3 map)
polynomialAutomorphismImpliesInvertible automorphism =
  record
    { inv = applyPolynomialMap3
        (PolynomialAutomorphism3.inversePolynomial automorphism)
    ; left = PolynomialAutomorphism3.leftPolynomialInverse automorphism
    ; right = PolynomialAutomorphism3.rightPolynomialInverse automorphism
    }

KellerInjectivityPrinciple3 : Set
KellerInjectivityPrinciple3 =
  (K : KellerMap3) →
  Injective (applyPolynomialMap3 (polynomial K))

KellerInvertibilityPrinciple3 : Set
KellerInvertibilityPrinciple3 =
  (K : KellerMap3) →
  Invertible (applyPolynomialMap3 (polynomial K))

KellerPolynomialAutomorphismPrinciple3 : Set
KellerPolynomialAutomorphismPrinciple3 =
  (K : KellerMap3) →
  PolynomialAutomorphism3 (polynomial K)

automorphismPrincipleImpliesInvertibilityPrinciple :
  KellerPolynomialAutomorphismPrinciple3 →
  KellerInvertibilityPrinciple3
automorphismPrincipleImpliesInvertibilityPrinciple principle K =
  polynomialAutomorphismImpliesInvertible (principle K)

invertibilityPrincipleImpliesInjectivityPrinciple :
  KellerInvertibilityPrinciple3 →
  KellerInjectivityPrinciple3
invertibilityPrincipleImpliesInjectivityPrinciple principle K =
  invertibleImpliesInjective (principle K)

kellerInjectivityPrinciple3False :
  ¬ KellerInjectivityPrinciple3
kellerInjectivityPrinciple3False principle =
  F-notInjective (principle alpogeKellerMap)

kellerInvertibilityPrinciple3False :
  ¬ KellerInvertibilityPrinciple3
kellerInvertibilityPrinciple3False principle =
  kellerInjectivityPrinciple3False
    (invertibilityPrincipleImpliesInjectivityPrinciple principle)

kellerPolynomialAutomorphismPrinciple3False :
  ¬ KellerPolynomialAutomorphismPrinciple3
kellerPolynomialAutomorphismPrinciple3False principle =
  kellerInvertibilityPrinciple3False
    (automorphismPrincipleImpliesInvertibilityPrinciple principle)

------------------------------------------------------------------------
-- Identity-coordinate padding: the exact collision refutes injectivity before
-- any stronger inverse or automorphism conclusion can be supplied.

PaddedInjectivityPrinciple : Nat → Set
PaddedInjectivityPrinciple n =
  (K : PaddedKellerMap n) →
  Injective (J.PaddedKellerMap.paddedMap K)

paddedInjectivityPrincipleFalse :
  (n : Nat) →
  ¬ PaddedInjectivityPrinciple n
paddedInjectivityPrincipleFalse n principle =
  paddedF-notInjective n (principle (alpogePaddedKellerMap n))

record KellerConsequenceHierarchyReceipt : Set where
  constructor mkKellerConsequenceHierarchyReceipt
  field
    polynomialAutomorphismImpliesInvertibilityChecked : Bool
    invertibilityImpliesInjectivityChecked : Bool
    injectivityPrincipleRefuted : Bool
    invertibilityPrincipleRefuted : Bool
    polynomialAutomorphismPrincipleRefuted : Bool
    paddingInjectivityRefuted : Bool
    surjectivitySeparatelyDerived : Bool
    surjectivitySeparatelyDerivedIsFalse :
      surjectivitySeparatelyDerived ≡ false
    interpretation : String

kellerConsequenceHierarchyReceipt : KellerConsequenceHierarchyReceipt
kellerConsequenceHierarchyReceipt =
  mkKellerConsequenceHierarchyReceipt
    true true true true true true
    false refl
    "the explicit collision refutes universal injectivity, hence also universal set invertibility and polynomial automorphism; surjectivity and image geometry are separate questions"
