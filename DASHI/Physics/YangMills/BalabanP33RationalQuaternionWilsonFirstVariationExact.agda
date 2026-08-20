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
-- Promote the already-constructed noncommutative ordered first-product rule
-- to the literal Wilson scalar variation.  For an ordered product of factor
-- jets, the Wilson convention S = 1 - q0(U) gives
--
--   dS = -q0 (orderedFirstProduct factors).
--
-- The existing theorem
--
--   sumQuaternion (firstVariationTerms factors)
--     = orderedFirstProduct factors
--
-- therefore implies an exact finite atom decomposition.  For a four-link
-- plaquette there are exactly four first-variation atoms, one per link
-- occurrence.  This is the source-facing first derivative analogue of the
-- existing sixteen-atom second-variation theorem and is used by the physical
-- plaquette-support producer.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.List.Base using (map; length)
open import Data.Rational.Base as ℚ using (ℚ; -_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonJetExact public

wilsonFirstVariationNumerator :
  List QuaternionFactorJet → ℚ
wilsonFirstVariationNumerator factors =
  - q0 (orderedFirstProduct factors)

wilsonFirstVariationAtomSum :
  List QuaternionFactorJet → ℚ
wilsonFirstVariationAtomSum factors =
  sumRational (map wilsonAtomContribution (firstVariationTerms factors))

wilsonFirstVariationIsAtomSum : ∀ factors →
  wilsonFirstVariationNumerator factors
  ≡ wilsonFirstVariationAtomSum factors
wilsonFirstVariationIsAtomSum factors =
  trans
    (cong (λ q → - q0 q)
      (sym (sumFirstVariationTermsExact factors)))
    (trans
      (cong -_ (scalarPartSumQuaternion (firstVariationTerms factors)))
      (trans
        (negativeFiniteSum (map q0 (firstVariationTerms factors)))
        (cong sumRational
          (mapNegatedScalarParts (firstVariationTerms factors)))))

fourFactorFirstVariationAtomCountExact :
  ∀ first second third fourth →
  length
    (firstVariationTerms
      (fourFactorJets first second third fourth))
  ≡ 4
fourFactorFirstVariationAtomCountExact first second third fourth = refl

fourLinkWilsonFirstVariationIsFourScalarAtoms :
  ∀ first second third fourth →
  wilsonFirstVariationNumerator
    (fourFactorJets first second third fourth)
  ≡ wilsonFirstVariationAtomSum
      (fourFactorJets first second third fourth)
fourLinkWilsonFirstVariationIsFourScalarAtoms first second third fourth =
  wilsonFirstVariationIsAtomSum
    (fourFactorJets first second third fourth)

wilsonFirstVariationAtomDecompositionLevel : ProofLevel
wilsonFirstVariationAtomDecompositionLevel = machineChecked

fourLinkWilsonFirstVariationLocalityLevel : ProofLevel
fourLinkWilsonFirstVariationLocalityLevel = machineChecked
