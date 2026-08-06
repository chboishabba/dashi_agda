module DASHI.Physics.YangMills.BalabanP33WilsonPlaquetteScalarSecondVariationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks",
-- Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- DASHI CONTRIBUTION
--
-- Convert the concrete four-link quaternion product second variation into the
-- literal Wilson plaquette Hessian numerator.  In the repository convention
--
--   S_p = 1 - q0(U_0 U_1 U_2 U_3),
--
-- so its second variation is
--
--   -q0((U_0 U_1 U_2 U_3)'').
--
-- The quaternion product theorem supplies exactly sixteen ordered atoms.
-- Componentwise additivity and a finite induction prove that the Wilson scalar
-- second variation is the sum of the sixteen scalar atom contributions
-- `-q0(atom)`.  This closes the ordered-product-to-Wilson-scalar identification;
-- the remaining background analysis is the factorisation and norm estimate of
-- each explicit atom.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map; length)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanRealPolynomialRing using
  (_+R_; -R_; zeroR)
open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  (module RealPolynomialSolver; zeroCoefficient)
open import DASHI.Physics.YangMills.BalabanComputedPolynomialSolver using
  (solveComputed; computed)
open RealPolynomialSolver using
  (Polynomial; con; _:=_; _:+_; :-_)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  (Quaternion; q0)
import DASHI.Physics.YangMills.BalabanP33QuaternionProductSecondVariationExact as Product

zeroP : ∀ {n} → Polynomial n
zeroP = con zeroCoefficient

sumReal : List ℝ → ℝ
sumReal [] = zeroR
sumReal (value ∷ values) = value +R sumReal values

mapComposeExact :
  ∀ {A B C : Set} (outer : B → C) (inner : A → B) values →
  map outer (map inner values)
  ≡ map (λ value → outer (inner value)) values
mapComposeExact outer inner [] = refl
mapComposeExact outer inner (value ∷ values) =
  cong (outer (inner value) ∷_)
    (mapComposeExact outer inner values)

scalarPartSumQuaternion : ∀ values →
  q0 (Product.sumQuaternion values)
  ≡ sumReal (map q0 values)
scalarPartSumQuaternion [] = refl
scalarPartSumQuaternion (value ∷ values) =
  cong (q0 value +R_) (scalarPartSumQuaternion values)

negativeAddDistributes : ∀ left right →
  -R (left +R right) ≡ (-R left) +R (-R right)
negativeAddDistributes =
  solveComputed 2
    (λ left right → :- (left :+ right) := (:- left) :+ (:- right))
    computed

negativeZero : -R zeroR ≡ zeroR
negativeZero =
  solveComputed 0 (:- zeroP := zeroP) computed

negativeFiniteSum : ∀ values →
  -R (sumReal values)
  ≡ sumReal (map -R_ values)
negativeFiniteSum [] = negativeZero
negativeFiniteSum (value ∷ values) =
  trans
    (negativeAddDistributes value (sumReal values))
    (cong ((-R value) +R_) (negativeFiniteSum values))

wilsonAtomContribution : Quaternion → ℝ
wilsonAtomContribution atom = -R (q0 atom)

wilsonSecondVariationNumerator :
  List Product.QuaternionFactorJet → ℝ
wilsonSecondVariationNumerator factors =
  -R (q0 (Product.orderedSecondProduct factors))

wilsonSecondVariationAtomSum :
  List Product.QuaternionFactorJet → ℝ
wilsonSecondVariationAtomSum factors =
  sumReal
    (map wilsonAtomContribution
      (Product.secondVariationTerms factors))

wilsonSecondVariationIsAtomSum : ∀ factors →
  wilsonSecondVariationNumerator factors
  ≡ wilsonSecondVariationAtomSum factors
wilsonSecondVariationIsAtomSum factors =
  trans
    (cong -R_
      (sym (Product.sumSecondVariationTermsExact factors)))
    (trans
      (cong -R_
        (scalarPartSumQuaternion
          (Product.secondVariationTerms factors)))
      (trans
        (negativeFiniteSum
          (map q0 (Product.secondVariationTerms factors)))
        (cong sumReal
          (mapComposeExact -R_ q0
            (Product.secondVariationTerms factors)))))

fourLinkWilsonScalarAtomCountExact :
  ∀ first second third fourth →
  length
    (map wilsonAtomContribution
      (Product.secondVariationTerms
        (Product.fourFactorJets first second third fourth)))
  ≡ 16
fourLinkWilsonScalarAtomCountExact first second third fourth = refl

fourLinkWilsonSecondVariationIsSixteenScalarAtoms :
  ∀ first second third fourth →
  wilsonSecondVariationNumerator
    (Product.fourFactorJets first second third fourth)
  ≡ wilsonSecondVariationAtomSum
      (Product.fourFactorJets first second third fourth)
fourLinkWilsonSecondVariationIsSixteenScalarAtoms =
  λ first second third fourth →
    wilsonSecondVariationIsAtomSum
      (Product.fourFactorJets first second third fourth)

wilsonQuaternionScalarProjectionLevel : ProofLevel
wilsonQuaternionScalarProjectionLevel = machineChecked

wilsonFourLinkScalarSecondVariationLevel : ProofLevel
wilsonFourLinkScalarSecondVariationLevel = machineChecked

wilsonSixteenScalarAtomExpansionLevel : ProofLevel
wilsonSixteenScalarAtomExpansionLevel = machineChecked
