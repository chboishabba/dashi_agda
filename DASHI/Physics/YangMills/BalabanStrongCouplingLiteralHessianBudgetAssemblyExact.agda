module DASHI.Physics.YangMills.BalabanStrongCouplingLiteralHessianBudgetAssemblyExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong Coupling",
-- Communications in Mathematical Physics 400 (2023), 805--851.
-- DOI: 10.1007/s00220-022-04609-1.
-- arXiv:2204.12737.
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Balaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Assemble the source Hessian coefficient from the literal rational-quaternion
-- product rule rather than accepting 8(d-1) as an unexplained constant.
--
-- The preceding modules prove, constructor by constructor, that the four
-- diagonal and twelve ordered-cross Wilson atoms satisfy
--
--   sum_sigma -q0(atom_sigma) <= 4 (n0+n1+n2+n3).
--
-- Multiplication by a nonnegative group/coupling scale and by the exact
-- oriented-edge incidence 2(d-1) gives
--
--   2(d-1) g sum_sigma -q0(atom_sigma)
--     <= 8 g (d-1) (n0+n1+n2+n3).
--
-- For the Shen--Zhu--Zhu application g=N|beta|.  The theorem below remains
-- exact over rationals and does not assume the missing product-Haar measure,
-- Bakry--Emery theorem, infinite-volume limit or continuum construction.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanStrongCouplingLiteralQuaternionAtomNormExact as Atom
import DASHI.Physics.YangMills.BalabanStrongCouplingLiteralAtomGeneratedProductBridgeExact as Generated
import DASHI.Physics.YangMills.BalabanStrongCouplingLiteralQuaternionScalarBudgetExact as Scalar
import DASHI.Physics.YangMills.BalabanStrongCouplingSixteenAtomIncidenceBudgetExact as Budget

weightedPlaquetteAtomSum :
  ℚ →
  Q.QuaternionFactorJet → Q.QuaternionFactorJet →
  Q.QuaternionFactorJet → Q.QuaternionFactorJet → ℚ
weightedPlaquetteAtomSum groupCoupling jet0 jet1 jet2 jet3 =
  groupCoupling
    * Scalar.sumPlacementScalars
        jet0 jet1 jet2 jet3 Generated.recursivePlacementOrder4

weightedPlaquetteBudget :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
weightedPlaquetteBudget groupCoupling n0 n1 n2 n3 =
  groupCoupling
    * ((+ 4 / 1) * Budget.localInsertionCharge n0 n1 n2 n3)

weightedPlaquetteAtomSumBelowBudget :
  ∀ groupCoupling →
  0ℚ ≤ groupCoupling →
  ∀ jet0 jet1 jet2 jet3
    (profile0 : Atom.UnitJetNormProfile jet0)
    (profile1 : Atom.UnitJetNormProfile jet1)
    (profile2 : Atom.UnitJetNormProfile jet2)
    (profile3 : Atom.UnitJetNormProfile jet3) →
  weightedPlaquetteAtomSum groupCoupling jet0 jet1 jet2 jet3
  ≤ weightedPlaquetteBudget groupCoupling
      (Atom.insertionNormSq profile0)
      (Atom.insertionNormSq profile1)
      (Atom.insertionNormSq profile2)
      (Atom.insertionNormSq profile3)
weightedPlaquetteAtomSumBelowBudget
    groupCoupling groupCouplingNN
    jet0 jet1 jet2 jet3 profile0 profile1 profile2 profile3 =
  Norm.scaleNonnegative groupCoupling groupCouplingNN
    (Scalar.recursiveWilsonScalarSumBelowFourCharges
      jet0 jet1 jet2 jet3 profile0 profile1 profile2 profile3)

orientedEdgeIncidence : ℚ → ℚ
orientedEdgeIncidence dMinusOne = (+ 2 / 1) * dMinusOne

incidentWeightedAtomSum :
  ℚ → ℚ →
  Q.QuaternionFactorJet → Q.QuaternionFactorJet →
  Q.QuaternionFactorJet → Q.QuaternionFactorJet → ℚ
incidentWeightedAtomSum dMinusOne groupCoupling jet0 jet1 jet2 jet3 =
  orientedEdgeIncidence dMinusOne
    * weightedPlaquetteAtomSum groupCoupling jet0 jet1 jet2 jet3

sourceGlobalHessianBudget :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
sourceGlobalHessianBudget dMinusOne groupCoupling n0 n1 n2 n3 =
  (+ 8 / 1) * groupCoupling * dMinusOne
    * Budget.localInsertionCharge n0 n1 n2 n3

literalGlobalHessianCoefficientFromAtoms :
  ∀ dMinusOne groupCoupling →
  0ℚ ≤ dMinusOne →
  0ℚ ≤ groupCoupling →
  ∀ jet0 jet1 jet2 jet3
    (profile0 : Atom.UnitJetNormProfile jet0)
    (profile1 : Atom.UnitJetNormProfile jet1)
    (profile2 : Atom.UnitJetNormProfile jet2)
    (profile3 : Atom.UnitJetNormProfile jet3) →
  incidentWeightedAtomSum
    dMinusOne groupCoupling jet0 jet1 jet2 jet3
  ≤ sourceGlobalHessianBudget dMinusOne groupCoupling
      (Atom.insertionNormSq profile0)
      (Atom.insertionNormSq profile1)
      (Atom.insertionNormSq profile2)
      (Atom.insertionNormSq profile3)
literalGlobalHessianCoefficientFromAtoms
    dMinusOne groupCoupling dMinusOneNN groupCouplingNN
    jet0 jet1 jet2 jet3 profile0 profile1 profile2 profile3 =
  let
    incidenceNN : 0ℚ ≤ orientedEdgeIncidence dMinusOne
    incidenceNN =
      Norm.scaleNonnegative
        (+ 2 / 1)
        (ℚP.nonNegative⁻¹ (+ 2 / 1))
        dMinusOneNN

    localBound =
      weightedPlaquetteAtomSumBelowBudget
        groupCoupling groupCouplingNN
        jet0 jet1 jet2 jet3 profile0 profile1 profile2 profile3

    incidentBound =
      Norm.scaleNonnegative
        (orientedEdgeIncidence dMinusOne)
        incidenceNN
        localBound

    charge =
      Budget.localInsertionCharge
        (Atom.insertionNormSq profile0)
        (Atom.insertionNormSq profile1)
        (Atom.insertionNormSq profile2)
        (Atom.insertionNormSq profile3)

    coefficientExact :
      orientedEdgeIncidence dMinusOne
        * weightedPlaquetteBudget groupCoupling
            (Atom.insertionNormSq profile0)
            (Atom.insertionNormSq profile1)
            (Atom.insertionNormSq profile2)
            (Atom.insertionNormSq profile3)
      ≡ (+ 8 / 1) * groupCoupling * dMinusOne * charge
    coefficientExact =
      ℚRing.solve-∀ groupCoupling dMinusOne charge
  in
  subst
    (λ upper →
      incidentWeightedAtomSum
        dMinusOne groupCoupling jet0 jet1 jet2 jet3
      ≤ upper)
    coefficientExact
    incidentBound

fourDimensionalSourceCoefficientExact :
  ∀ groupCoupling charge →
  (+ 8 / 1) * groupCoupling * (+ 3 / 1) * charge
  ≡ (+ 24 / 1) * groupCoupling * charge
fourDimensionalSourceCoefficientExact groupCoupling charge =
  ℚRing.solve-∀ groupCoupling charge
