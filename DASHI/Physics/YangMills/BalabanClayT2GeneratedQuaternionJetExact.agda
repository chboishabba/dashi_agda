module DASHI.Physics.YangMills.BalabanClayT2GeneratedQuaternionJetExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (tt)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _≤_; _≤ᵇ_; _/_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Generated polynomial jet for one four-link SU(2) plaquette.
--
-- Brian C. Hall, "Lie Groups, Lie Algebras, and Representations: An
-- Elementary Introduction", second edition, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3.
-- Relationship: SU(2) exponential and BCH comparison.
--
-- DASHI contribution: the list below is generated from exact quaternion
-- multiplication of the second-order link jets.  It does not enumerate an
-- unspecified family of cubic terms by hand.  The transcendental difference
-- between the exact link exponential and this finite jet remains separately
-- visible in the audit receipt.
------------------------------------------------------------------------

data Link4 : Set where
  link0 link1 link2 link3 : Link4

data Coord3 : Set where
  coord0 coord1 coord2 : Coord3

record Variable12 : Set where
  constructor variable
  field
    link : Link4
    coordinate : Coord3

open Variable12 public

data Sign : Set where
  positive negative : Sign

record SignedCoefficient : Set where
  constructor signed
  field
    sign : Sign
    magnitude : ℚ

open SignedCoefficient public

negateSign : Sign → Sign
negateSign positive = negative
negateSign negative = positive

multiplySign : Sign → Sign → Sign
multiplySign positive positive = positive
multiplySign positive negative = negative
multiplySign negative positive = negative
multiplySign negative negative = positive

negateCoefficient : SignedCoefficient → SignedCoefficient
negateCoefficient (signed sign magnitude) = signed (negateSign sign) magnitude

multiplyCoefficient : SignedCoefficient → SignedCoefficient → SignedCoefficient
multiplyCoefficient (signed leftSign leftMagnitude) (signed rightSign rightMagnitude) =
  signed (multiplySign leftSign rightSign) (leftMagnitude * rightMagnitude)

record JetTerm : Set where
  constructor term
  field
    coefficient : SignedCoefficient
    variables : List Variable12

open JetTerm public

Polynomial : Set
Polynomial = List JetTerm

infixr 5 _++_
_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

concatMap : ∀ {A B : Set} → (A → List B) → List A → List B
concatMap f [] = []
concatMap f (x ∷ xs) = f x ++ concatMap f xs

oneTerm : JetTerm
oneTerm = term (signed positive (+ 1 / 1)) []

variableTerm : SignedCoefficient → Link4 → Coord3 → JetTerm
variableTerm coefficient link coordinate =
  term coefficient (variable link coordinate ∷ [])

quadraticVariableTerm : SignedCoefficient → Link4 → Coord3 → JetTerm
quadraticVariableTerm coefficient link coordinate =
  term coefficient
    (variable link coordinate ∷ variable link coordinate ∷ [])

negateTerm : JetTerm → JetTerm
negateTerm (term coefficient variables) = term (negateCoefficient coefficient) variables

multiplyTerm : JetTerm → JetTerm → JetTerm
multiplyTerm (term leftCoefficient leftVariables) (term rightCoefficient rightVariables) =
  term (multiplyCoefficient leftCoefficient rightCoefficient)
    (leftVariables ++ rightVariables)

zeroPolynomial : Polynomial
zeroPolynomial = []

onePolynomial : Polynomial
onePolynomial = oneTerm ∷ []

addPolynomial : Polynomial → Polynomial → Polynomial
addPolynomial = _++_

negatePolynomial : Polynomial → Polynomial
negatePolynomial = map negateTerm

multiplyPolynomial : Polynomial → Polynomial → Polynomial
multiplyPolynomial left right =
  concatMap (λ leftTerm → map (multiplyTerm leftTerm) right) left

record QuaternionJet : Set where
  constructor quaternionJet
  field
    scalarJet vectorJet0 vectorJet1 vectorJet2 : Polynomial

open QuaternionJet public

scalarLinkJet : Link4 → Polynomial
scalarLinkJet link =
  oneTerm ∷
  quadraticVariableTerm (signed negative (+ 1 / 8)) link coord0 ∷
  quadraticVariableTerm (signed negative (+ 1 / 8)) link coord1 ∷
  quadraticVariableTerm (signed negative (+ 1 / 8)) link coord2 ∷ []

vectorLinkJet : Link4 → Coord3 → Polynomial
vectorLinkJet link coordinate =
  variableTerm (signed positive (+ 1 / 2)) link coordinate ∷ []

linkJet : Link4 → QuaternionJet
linkJet link = quaternionJet
  (scalarLinkJet link)
  (vectorLinkJet link coord0)
  (vectorLinkJet link coord1)
  (vectorLinkJet link coord2)

inverseJet : QuaternionJet → QuaternionJet
inverseJet jet = quaternionJet
  (scalarJet jet)
  (negatePolynomial (vectorJet0 jet))
  (negatePolynomial (vectorJet1 jet))
  (negatePolynomial (vectorJet2 jet))

dotJet : QuaternionJet → QuaternionJet → Polynomial
dotJet left right =
  addPolynomial
    (multiplyPolynomial (vectorJet0 left) (vectorJet0 right))
    (addPolynomial
      (multiplyPolynomial (vectorJet1 left) (vectorJet1 right))
      (multiplyPolynomial (vectorJet2 left) (vectorJet2 right)))

crossJet0 crossJet1 crossJet2 : QuaternionJet → QuaternionJet → Polynomial
crossJet0 left right =
  addPolynomial
    (multiplyPolynomial (vectorJet1 left) (vectorJet2 right))
    (negatePolynomial (multiplyPolynomial (vectorJet2 left) (vectorJet1 right)))
crossJet1 left right =
  addPolynomial
    (multiplyPolynomial (vectorJet2 left) (vectorJet0 right))
    (negatePolynomial (multiplyPolynomial (vectorJet0 left) (vectorJet2 right)))
crossJet2 left right =
  addPolynomial
    (multiplyPolynomial (vectorJet0 left) (vectorJet1 right))
    (negatePolynomial (multiplyPolynomial (vectorJet1 left) (vectorJet0 right)))

multiplyQuaternionJet : QuaternionJet → QuaternionJet → QuaternionJet
multiplyQuaternionJet left right = quaternionJet
  (addPolynomial
    (multiplyPolynomial (scalarJet left) (scalarJet right))
    (negatePolynomial (dotJet left right)))
  (addPolynomial
    (multiplyPolynomial (scalarJet left) (vectorJet0 right))
    (addPolynomial
      (multiplyPolynomial (scalarJet right) (vectorJet0 left))
      (crossJet0 left right)))
  (addPolynomial
    (multiplyPolynomial (scalarJet left) (vectorJet1 right))
    (addPolynomial
      (multiplyPolynomial (scalarJet right) (vectorJet1 left))
      (crossJet1 left right)))
  (addPolynomial
    (multiplyPolynomial (scalarJet left) (vectorJet2 right))
    (addPolynomial
      (multiplyPolynomial (scalarJet right) (vectorJet2 left))
      (crossJet2 left right)))

fourLinkPlaquetteJet : QuaternionJet
fourLinkPlaquetteJet =
  multiplyQuaternionJet
    (multiplyQuaternionJet
      (multiplyQuaternionJet (linkJet link0) (linkJet link1))
      (inverseJet (linkJet link2)))
    (inverseJet (linkJet link3))

atLeastThreeVariables : List Variable12 → Bool
atLeastThreeVariables [] = false
atLeastThreeVariables (_ ∷ []) = false
atLeastThreeVariables (_ ∷ _ ∷ []) = false
atLeastThreeVariables (_ ∷ _ ∷ _ ∷ _) = true

filterCubic : Polynomial → Polynomial
filterCubic [] = []
filterCubic (term ∷ terms) with atLeastThreeVariables (variables term)
... | false = filterCubic terms
... | true = term ∷ filterCubic terms

scalarCubicTerms vector0CubicTerms vector1CubicTerms vector2CubicTerms : Polynomial
scalarCubicTerms = filterCubic (scalarJet fourLinkPlaquetteJet)
vector0CubicTerms = filterCubic (vectorJet0 fourLinkPlaquetteJet)
vector1CubicTerms = filterCubic (vectorJet1 fourLinkPlaquetteJet)
vector2CubicTerms = filterCubic (vectorJet2 fourLinkPlaquetteJet)

sumℚ : List ℚ → ℚ
sumℚ [] = 0ℚ
sumℚ (x ∷ xs) = x + sumℚ xs

coefficientL1 : Polynomial → ℚ
coefficientL1 terms = sumℚ (map (λ term → magnitude (coefficient term)) terms)

generatedScalarCoefficientL1 generatedVectorCoefficientL1 configuredCubicCoefficient : ℚ
generatedScalarCoefficientL1 = + 43089 / 4096
generatedVectorCoefficientL1 = + 3055 / 256
configuredCubicCoefficient = + 1024 / 1

generatedScalarBelow1024 : generatedScalarCoefficientL1 ≤ configuredCubicCoefficient
generatedScalarBelow1024 = ℚP.≤ᵇ⇒≤ tt

generatedVectorBelow1024 : generatedVectorCoefficientL1 ≤ configuredCubicCoefficient
generatedVectorBelow1024 = ℚP.≤ᵇ⇒≤ tt

record GeneratedQuaternionJetAudit : Set₁ where
  field
    scalarEnumerationExact :
      coefficientL1 scalarCubicTerms ≡ generatedScalarCoefficientL1
    vector0EnumerationExact :
      coefficientL1 vector0CubicTerms ≡ generatedVectorCoefficientL1
    vector1EnumerationExact :
      coefficientL1 vector1CubicTerms ≡ generatedVectorCoefficientL1
    vector2EnumerationExact :
      coefficientL1 vector2CubicTerms ≡ generatedVectorCoefficientL1

    exactExponentialMinusSecondOrderJetCubic : Set
    exactQuaternionLogMinusJetCubic : Set
    linearCurlAndQuadraticCommutatorAreRemovedExactly : Set
    configuredPlaquetteChargeIncludesCollars : Set

open GeneratedQuaternionJetAudit public

scalarGeneratedCoefficientBelow1024 :
  GeneratedQuaternionJetAudit → coefficientL1 scalarCubicTerms ≤ configuredCubicCoefficient
scalarGeneratedCoefficientBelow1024 audit =
  subst (λ value → value ≤ configuredCubicCoefficient)
    (scalarEnumerationExact audit) generatedScalarBelow1024

vector0GeneratedCoefficientBelow1024 :
  GeneratedQuaternionJetAudit → coefficientL1 vector0CubicTerms ≤ configuredCubicCoefficient
vector0GeneratedCoefficientBelow1024 audit =
  subst (λ value → value ≤ configuredCubicCoefficient)
    (vector0EnumerationExact audit) generatedVectorBelow1024

vector1GeneratedCoefficientBelow1024 :
  GeneratedQuaternionJetAudit → coefficientL1 vector1CubicTerms ≤ configuredCubicCoefficient
vector1GeneratedCoefficientBelow1024 audit =
  subst (λ value → value ≤ configuredCubicCoefficient)
    (vector1EnumerationExact audit) generatedVectorBelow1024

vector2GeneratedCoefficientBelow1024 :
  GeneratedQuaternionJetAudit → coefficientL1 vector2CubicTerms ≤ configuredCubicCoefficient
vector2GeneratedCoefficientBelow1024 audit =
  subst (λ value → value ≤ configuredCubicCoefficient)
    (vector2EnumerationExact audit) generatedVectorBelow1024

quaternionJetGeneratorLevel : ProofLevel
quaternionJetGeneratorLevel = machineChecked

quaternionJetConfiguredArithmeticLevel : ProofLevel
quaternionJetConfiguredArithmeticLevel = machineChecked

quaternionJetNormalizationAuditInputsLevel : ProofLevel
quaternionJetNormalizationAuditInputsLevel = conditional
