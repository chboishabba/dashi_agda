module DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonFirstVariationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- The canonical rational quaternion Wilson jet already contains the exact
-- noncommutative product recursion `orderedFirstProduct` and its explicit list
-- `firstVariationTerms`.  Promote the scalar Wilson first variation itself:
--
--   D S_p = -q0(D U_p),
--
-- and prove that on a four-link plaquette it is exactly the sum of four scalar
-- product-rule atoms.  This is the first-order analogue of the existing
-- sixteen-atom Hessian theorem and the algebraic precursor to physical
-- plaquette-boundary support.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (map; length)
open import Data.Rational.Base as ℚ using (ℚ; -_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonJetExact as Jet

wilsonFirstVariationNumerator :
  Agda.Builtin.List.List Jet.QuaternionFactorJet → ℚ
wilsonFirstVariationNumerator factors =
  - Jet.q0 (Jet.orderedFirstProduct factors)

wilsonFirstVariationAtomSum :
  Agda.Builtin.List.List Jet.QuaternionFactorJet → ℚ
wilsonFirstVariationAtomSum factors =
  Jet.sumRational
    (map Jet.wilsonAtomContribution (Jet.firstVariationTerms factors))

wilsonFirstVariationIsAtomSum : ∀ factors →
  wilsonFirstVariationNumerator factors
  ≡ wilsonFirstVariationAtomSum factors
wilsonFirstVariationIsAtomSum factors =
  trans
    (cong (λ q → - Jet.q0 q)
      (sym (Jet.sumFirstVariationTermsExact factors)))
    (trans
      (cong -_
        (Jet.scalarPartSumQuaternion (Jet.firstVariationTerms factors)))
      (trans
        (Jet.negativeFiniteSum
          (map Jet.q0 (Jet.firstVariationTerms factors)))
        (cong Jet.sumRational
          (Jet.mapNegatedScalarParts (Jet.firstVariationTerms factors)))))

fourFactorFirstVariationAtomCountExact :
  ∀ first second third fourth →
  length (Jet.firstVariationTerms
    (Jet.fourFactorJets first second third fourth)) ≡ 4
fourFactorFirstVariationAtomCountExact first second third fourth = refl

fourLinkWilsonFirstVariationIsFourScalarAtoms :
  ∀ first second third fourth →
  wilsonFirstVariationNumerator
    (Jet.fourFactorJets first second third fourth)
  ≡ wilsonFirstVariationAtomSum
      (Jet.fourFactorJets first second third fourth)
fourLinkWilsonFirstVariationIsFourScalarAtoms first second third fourth =
  wilsonFirstVariationIsAtomSum
    (Jet.fourFactorJets first second third fourth)

wilsonFirstVariationFourAtomLevel : ProofLevel
wilsonFirstVariationFourAtomLevel = machineChecked
