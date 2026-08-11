module DASHI.Physics.YangMills.BalabanStrongCouplingLiteralQuaternionAtomNormExact where

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
-- "Confinement of Quarks".
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Compute the exact quaternion norm of every literal four-link Wilson Hessian
-- atom.  For a unit-quaternion right-exponential jet with insertion X,
--
--   value  = U,       N(value)  = 1,
--   first  = U X,     N(first)  = N(X),
--   second = U X^2,   N(second) = N(X)^2,
--
-- and the same three identities hold for an inverse occurrence
-- `(U^-1,-XU^-1,X^2U^-1)`.
--
-- The named sixteen placements then have exact norm squares
--
--   diagonal i : n_i^2,
--   ordered (i,j) : n_i n_j,
--
-- where n_i=N(X_i).  This is proved constructor-by-constructor using the
-- repository's noncommutative rational quaternion multiplication and norm
-- multiplicativity.  No anonymous atom total or analytic norm receipt is used.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 1ℚ; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33WilsonPlaquetteSecondVariationPlacementsExact as Placement

------------------------------------------------------------------------
-- Literal positive and inverse right-exponential jets.
------------------------------------------------------------------------

positiveUnitJet :
  Q.RationalQuaternion → Q.RationalQuaternion → Q.QuaternionFactorJet
positiveUnitJet unit insertion =
  Q.factorJet
    unit
    (unit Q.*q insertion)
    (unit Q.*q (insertion Q.*q insertion))

inverseUnitJet :
  Q.RationalQuaternion → Q.RationalQuaternion → Q.QuaternionFactorJet
inverseUnitJet unit insertion =
  Q.factorJet
    (Norm.conjugate unit)
    (Q.negQ insertion Q.*q Norm.conjugate unit)
    ((insertion Q.*q insertion) Q.*q Norm.conjugate unit)

normSqNegExact : ∀ value →
  Norm.normSq (Q.negQ value) ≡ Norm.normSq value
normSqNegExact (Q.quat q0 q1 q2 q3) =
  ℚRing.solve-∀ q0 q1 q2 q3

record UnitJetNormProfile (jet : Q.QuaternionFactorJet) : Set where
  constructor unitJetNormProfile
  field
    insertionNormSq : ℚ
    valueNormSqOne : Norm.normSq (Q.factorValue jet) ≡ 1ℚ
    firstNormSqExact :
      Norm.normSq (Q.factorFirst jet) ≡ insertionNormSq
    secondNormSqExact :
      Norm.normSq (Q.factorSecond jet)
      ≡ insertionNormSq * insertionNormSq

open UnitJetNormProfile public

positiveUnitJetNormProfile :
  ∀ unit insertion →
  Norm.normSq unit ≡ 1ℚ →
  UnitJetNormProfile (positiveUnitJet unit insertion)
positiveUnitJetNormProfile unit insertion unitNorm =
  let
    insertionNorm = Norm.normSq insertion

    firstExact :
      Norm.normSq (unit Q.*q insertion) ≡ insertionNorm
    firstExact =
      trans
        (Norm.normSqMultiplyExact unit insertion)
        (subst
          (λ selected → selected * insertionNorm ≡ insertionNorm)
          (sym unitNorm)
          (ℚRing.solve-∀ insertionNorm))

    secondExact :
      Norm.normSq (unit Q.*q (insertion Q.*q insertion))
      ≡ insertionNorm * insertionNorm
    secondExact =
      trans
        (Norm.normSqMultiplyExact unit (insertion Q.*q insertion))
        (trans
          (cong (Norm.normSq unit *_)
            (Norm.normSqMultiplyExact insertion insertion))
          (subst
            (λ selected →
              selected * (insertionNorm * insertionNorm)
              ≡ insertionNorm * insertionNorm)
            (sym unitNorm)
            (ℚRing.solve-∀ insertionNorm)))
  in
  unitJetNormProfile insertionNorm unitNorm firstExact secondExact

inverseUnitJetNormProfile :
  ∀ unit insertion →
  Norm.normSq unit ≡ 1ℚ →
  UnitJetNormProfile (inverseUnitJet unit insertion)
inverseUnitJetNormProfile unit insertion unitNorm =
  let
    insertionNorm = Norm.normSq insertion

    inverseNorm : Norm.normSq (Norm.conjugate unit) ≡ 1ℚ
    inverseNorm = trans (Norm.normSqConjugateExact unit) unitNorm

    firstExact :
      Norm.normSq (Q.negQ insertion Q.*q Norm.conjugate unit)
      ≡ insertionNorm
    firstExact =
      trans
        (Norm.normSqMultiplyExact
          (Q.negQ insertion) (Norm.conjugate unit))
        (trans
          (cong (_* Norm.normSq (Norm.conjugate unit))
            (normSqNegExact insertion))
          (subst
            (λ selected → insertionNorm * selected ≡ insertionNorm)
            (sym inverseNorm)
            (ℚRing.solve-∀ insertionNorm)))

    secondExact :
      Norm.normSq
        ((insertion Q.*q insertion) Q.*q Norm.conjugate unit)
      ≡ insertionNorm * insertionNorm
    secondExact =
      trans
        (Norm.normSqMultiplyExact
          (insertion Q.*q insertion) (Norm.conjugate unit))
        (trans
          (cong (_* Norm.normSq (Norm.conjugate unit))
            (Norm.normSqMultiplyExact insertion insertion))
          (subst
            (λ selected →
              (insertionNorm * insertionNorm) * selected
              ≡ insertionNorm * insertionNorm)
            (sym inverseNorm)
            (ℚRing.solve-∀ insertionNorm)))
  in
  unitJetNormProfile insertionNorm inverseNorm firstExact secondExact

------------------------------------------------------------------------
-- Selection profile for the sixteen named placements.
------------------------------------------------------------------------

data FactorSelection : Set where
  valueSelection firstSelection secondSelection : FactorSelection

applySelection :
  FactorSelection → Q.QuaternionFactorJet → Q.RationalQuaternion
applySelection valueSelection jet = Q.factorValue jet
applySelection firstSelection jet = Q.factorFirst jet
applySelection secondSelection jet = Q.factorSecond jet

selectedNormWeight : FactorSelection → ℚ → ℚ
selectedNormWeight valueSelection insertionNorm = 1ℚ
selectedNormWeight firstSelection insertionNorm = insertionNorm
selectedNormWeight secondSelection insertionNorm = insertionNorm * insertionNorm

selectedFactorNormSqExact :
  ∀ jet (profile : UnitJetNormProfile jet) selection →
  Norm.normSq (applySelection selection jet)
  ≡ selectedNormWeight selection (insertionNormSq profile)
selectedFactorNormSqExact jet profile valueSelection = valueNormSqOne profile
selectedFactorNormSqExact jet profile firstSelection = firstNormSqExact profile
selectedFactorNormSqExact jet profile secondSelection = secondNormSqExact profile

selection0 selection1 selection2 selection3 :
  Placement.PlaquetteSecondVariationPlacement4 → FactorSelection
selection0 Placement.secondAt0 = secondSelection
selection0 Placement.secondAt1 = valueSelection
selection0 Placement.secondAt2 = valueSelection
selection0 Placement.secondAt3 = valueSelection
selection0 (Placement.firstFirst Placement.ordered01) = firstSelection
selection0 (Placement.firstFirst Placement.ordered10) = firstSelection
selection0 (Placement.firstFirst Placement.ordered02) = firstSelection
selection0 (Placement.firstFirst Placement.ordered20) = firstSelection
selection0 (Placement.firstFirst Placement.ordered03) = firstSelection
selection0 (Placement.firstFirst Placement.ordered30) = firstSelection
selection0 (Placement.firstFirst Placement.ordered12) = valueSelection
selection0 (Placement.firstFirst Placement.ordered21) = valueSelection
selection0 (Placement.firstFirst Placement.ordered13) = valueSelection
selection0 (Placement.firstFirst Placement.ordered31) = valueSelection
selection0 (Placement.firstFirst Placement.ordered23) = valueSelection
selection0 (Placement.firstFirst Placement.ordered32) = valueSelection

selection1 Placement.secondAt0 = valueSelection
selection1 Placement.secondAt1 = secondSelection
selection1 Placement.secondAt2 = valueSelection
selection1 Placement.secondAt3 = valueSelection
selection1 (Placement.firstFirst Placement.ordered01) = firstSelection
selection1 (Placement.firstFirst Placement.ordered10) = firstSelection
selection1 (Placement.firstFirst Placement.ordered02) = valueSelection
selection1 (Placement.firstFirst Placement.ordered20) = valueSelection
selection1 (Placement.firstFirst Placement.ordered03) = valueSelection
selection1 (Placement.firstFirst Placement.ordered30) = valueSelection
selection1 (Placement.firstFirst Placement.ordered12) = firstSelection
selection1 (Placement.firstFirst Placement.ordered21) = firstSelection
selection1 (Placement.firstFirst Placement.ordered13) = firstSelection
selection1 (Placement.firstFirst Placement.ordered31) = firstSelection
selection1 (Placement.firstFirst Placement.ordered23) = valueSelection
selection1 (Placement.firstFirst Placement.ordered32) = valueSelection

selection2 Placement.secondAt0 = valueSelection
selection2 Placement.secondAt1 = valueSelection
selection2 Placement.secondAt2 = secondSelection
selection2 Placement.secondAt3 = valueSelection
selection2 (Placement.firstFirst Placement.ordered01) = valueSelection
selection2 (Placement.firstFirst Placement.ordered10) = valueSelection
selection2 (Placement.firstFirst Placement.ordered02) = firstSelection
selection2 (Placement.firstFirst Placement.ordered20) = firstSelection
selection2 (Placement.firstFirst Placement.ordered03) = valueSelection
selection2 (Placement.firstFirst Placement.ordered30) = valueSelection
selection2 (Placement.firstFirst Placement.ordered12) = firstSelection
selection2 (Placement.firstFirst Placement.ordered21) = firstSelection
selection2 (Placement.firstFirst Placement.ordered13) = valueSelection
selection2 (Placement.firstFirst Placement.ordered31) = valueSelection
selection2 (Placement.firstFirst Placement.ordered23) = firstSelection
selection2 (Placement.firstFirst Placement.ordered32) = firstSelection

selection3 Placement.secondAt0 = valueSelection
selection3 Placement.secondAt1 = valueSelection
selection3 Placement.secondAt2 = valueSelection
selection3 Placement.secondAt3 = secondSelection
selection3 (Placement.firstFirst Placement.ordered01) = valueSelection
selection3 (Placement.firstFirst Placement.ordered10) = valueSelection
selection3 (Placement.firstFirst Placement.ordered02) = valueSelection
selection3 (Placement.firstFirst Placement.ordered20) = valueSelection
selection3 (Placement.firstFirst Placement.ordered03) = firstSelection
selection3 (Placement.firstFirst Placement.ordered30) = firstSelection
selection3 (Placement.firstFirst Placement.ordered12) = valueSelection
selection3 (Placement.firstFirst Placement.ordered21) = valueSelection
selection3 (Placement.firstFirst Placement.ordered13) = firstSelection
selection3 (Placement.firstFirst Placement.ordered31) = firstSelection
selection3 (Placement.firstFirst Placement.ordered23) = firstSelection
selection3 (Placement.firstFirst Placement.ordered32) = firstSelection

orderedProduct4 :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion → Q.RationalQuaternion
orderedProduct4 factor0 factor1 factor2 factor3 =
  factor0 Q.*q (factor1 Q.*q (factor2 Q.*q (factor3 Q.*q Q.oneQ)))

placementAtom :
  Q.QuaternionFactorJet → Q.QuaternionFactorJet →
  Q.QuaternionFactorJet → Q.QuaternionFactorJet →
  Placement.PlaquetteSecondVariationPlacement4 → Q.RationalQuaternion
placementAtom jet0 jet1 jet2 jet3 placement =
  orderedProduct4
    (applySelection (selection0 placement) jet0)
    (applySelection (selection1 placement) jet1)
    (applySelection (selection2 placement) jet2)
    (applySelection (selection3 placement) jet3)

normSqOneExact : Norm.normSq Q.oneQ ≡ 1ℚ
normSqOneExact = ℚRing.solve []

orderedProduct4NormSqExact :
  ∀ factor0 factor1 factor2 factor3 →
  Norm.normSq (orderedProduct4 factor0 factor1 factor2 factor3)
  ≡ Norm.normSq factor0 * Norm.normSq factor1
    * Norm.normSq factor2 * Norm.normSq factor3
orderedProduct4NormSqExact factor0 factor1 factor2 factor3 =
  trans
    (Norm.normSqMultiplyExact factor0
      (factor1 Q.*q (factor2 Q.*q (factor3 Q.*q Q.oneQ))))
    (trans
      (cong (Norm.normSq factor0 *_)
        (Norm.normSqMultiplyExact factor1
          (factor2 Q.*q (factor3 Q.*q Q.oneQ))))
      (trans
        (cong (λ selected →
          Norm.normSq factor0 * (Norm.normSq factor1 * selected))
          (Norm.normSqMultiplyExact factor2 (factor3 Q.*q Q.oneQ)))
        (trans
          (cong (λ selected →
            Norm.normSq factor0
              * (Norm.normSq factor1
                * (Norm.normSq factor2 * selected)))
            (Norm.normSqMultiplyExact factor3 Q.oneQ))
          (subst
            (λ selected →
              Norm.normSq factor0
                * (Norm.normSq factor1
                  * (Norm.normSq factor2
                    * (Norm.normSq factor3 * selected)))
              ≡ Norm.normSq factor0 * Norm.normSq factor1
                * Norm.normSq factor2 * Norm.normSq factor3)
            (sym normSqOneExact)
            (ℚRing.solve-∀
              (Norm.normSq factor0) (Norm.normSq factor1)
              (Norm.normSq factor2) (Norm.normSq factor3))))))

placementNormWeight :
  Placement.PlaquetteSecondVariationPlacement4 →
  ℚ → ℚ → ℚ → ℚ → ℚ
placementNormWeight Placement.secondAt0 n0 n1 n2 n3 = n0 * n0
placementNormWeight Placement.secondAt1 n0 n1 n2 n3 = n1 * n1
placementNormWeight Placement.secondAt2 n0 n1 n2 n3 = n2 * n2
placementNormWeight Placement.secondAt3 n0 n1 n2 n3 = n3 * n3
placementNormWeight (Placement.firstFirst Placement.ordered01) n0 n1 n2 n3 = n0 * n1
placementNormWeight (Placement.firstFirst Placement.ordered10) n0 n1 n2 n3 = n1 * n0
placementNormWeight (Placement.firstFirst Placement.ordered02) n0 n1 n2 n3 = n0 * n2
placementNormWeight (Placement.firstFirst Placement.ordered20) n0 n1 n2 n3 = n2 * n0
placementNormWeight (Placement.firstFirst Placement.ordered03) n0 n1 n2 n3 = n0 * n3
placementNormWeight (Placement.firstFirst Placement.ordered30) n0 n1 n2 n3 = n3 * n0
placementNormWeight (Placement.firstFirst Placement.ordered12) n0 n1 n2 n3 = n1 * n2
placementNormWeight (Placement.firstFirst Placement.ordered21) n0 n1 n2 n3 = n2 * n1
placementNormWeight (Placement.firstFirst Placement.ordered13) n0 n1 n2 n3 = n1 * n3
placementNormWeight (Placement.firstFirst Placement.ordered31) n0 n1 n2 n3 = n3 * n1
placementNormWeight (Placement.firstFirst Placement.ordered23) n0 n1 n2 n3 = n2 * n3
placementNormWeight (Placement.firstFirst Placement.ordered32) n0 n1 n2 n3 = n3 * n2

placementAtomNormSqExact :
  ∀ jet0 jet1 jet2 jet3
    (profile0 : UnitJetNormProfile jet0)
    (profile1 : UnitJetNormProfile jet1)
    (profile2 : UnitJetNormProfile jet2)
    (profile3 : UnitJetNormProfile jet3)
    placement →
  Norm.normSq (placementAtom jet0 jet1 jet2 jet3 placement)
  ≡ placementNormWeight placement
      (insertionNormSq profile0) (insertionNormSq profile1)
      (insertionNormSq profile2) (insertionNormSq profile3)
placementAtomNormSqExact
    jet0 jet1 jet2 jet3 profile0 profile1 profile2 profile3 placement
  rewrite orderedProduct4NormSqExact
      (applySelection (selection0 placement) jet0)
      (applySelection (selection1 placement) jet1)
      (applySelection (selection2 placement) jet2)
      (applySelection (selection3 placement) jet3)
        | selectedFactorNormSqExact jet0 profile0 (selection0 placement)
        | selectedFactorNormSqExact jet1 profile1 (selection1 placement)
        | selectedFactorNormSqExact jet2 profile2 (selection2 placement)
        | selectedFactorNormSqExact jet3 profile3 (selection3 placement)
  with placement
... | Placement.secondAt0 = ℚRing.solve-∀ (insertionNormSq profile0)
... | Placement.secondAt1 = ℚRing.solve-∀ (insertionNormSq profile1)
... | Placement.secondAt2 = ℚRing.solve-∀ (insertionNormSq profile2)
... | Placement.secondAt3 = ℚRing.solve-∀ (insertionNormSq profile3)
... | Placement.firstFirst Placement.ordered01 =
  ℚRing.solve-∀ (insertionNormSq profile0) (insertionNormSq profile1)
... | Placement.firstFirst Placement.ordered10 =
  ℚRing.solve-∀ (insertionNormSq profile0) (insertionNormSq profile1)
... | Placement.firstFirst Placement.ordered02 =
  ℚRing.solve-∀ (insertionNormSq profile0) (insertionNormSq profile2)
... | Placement.firstFirst Placement.ordered20 =
  ℚRing.solve-∀ (insertionNormSq profile0) (insertionNormSq profile2)
... | Placement.firstFirst Placement.ordered03 =
  ℚRing.solve-∀ (insertionNormSq profile0) (insertionNormSq profile3)
... | Placement.firstFirst Placement.ordered30 =
  ℚRing.solve-∀ (insertionNormSq profile0) (insertionNormSq profile3)
... | Placement.firstFirst Placement.ordered12 =
  ℚRing.solve-∀ (insertionNormSq profile1) (insertionNormSq profile2)
... | Placement.firstFirst Placement.ordered21 =
  ℚRing.solve-∀ (insertionNormSq profile1) (insertionNormSq profile2)
... | Placement.firstFirst Placement.ordered13 =
  ℚRing.solve-∀ (insertionNormSq profile1) (insertionNormSq profile3)
... | Placement.firstFirst Placement.ordered31 =
  ℚRing.solve-∀ (insertionNormSq profile1) (insertionNormSq profile3)
... | Placement.firstFirst Placement.ordered23 =
  ℚRing.solve-∀ (insertionNormSq profile2) (insertionNormSq profile3)
... | Placement.firstFirst Placement.ordered32 =
  ℚRing.solve-∀ (insertionNormSq profile2) (insertionNormSq profile3)

orientedPlaquetteAtom :
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Q.RationalQuaternion → Q.RationalQuaternion →
  Placement.PlaquetteSecondVariationPlacement4 → Q.RationalQuaternion
orientedPlaquetteAtom unit0 insertion0 unit1 insertion1
    unit2 insertion2 unit3 insertion3 placement =
  placementAtom
    (positiveUnitJet unit0 insertion0)
    (positiveUnitJet unit1 insertion1)
    (inverseUnitJet unit2 insertion2)
    (inverseUnitJet unit3 insertion3)
    placement

orientedPlaquetteAtomNormSqExact :
  ∀ unit0 insertion0 unit1 insertion1 unit2 insertion2 unit3 insertion3 →
  Norm.normSq unit0 ≡ 1ℚ → Norm.normSq unit1 ≡ 1ℚ →
  Norm.normSq unit2 ≡ 1ℚ → Norm.normSq unit3 ≡ 1ℚ →
  ∀ placement →
  Norm.normSq
    (orientedPlaquetteAtom
      unit0 insertion0 unit1 insertion1
      unit2 insertion2 unit3 insertion3 placement)
  ≡ placementNormWeight placement
      (Norm.normSq insertion0) (Norm.normSq insertion1)
      (Norm.normSq insertion2) (Norm.normSq insertion3)
orientedPlaquetteAtomNormSqExact
    unit0 insertion0 unit1 insertion1 unit2 insertion2 unit3 insertion3
    unit0Norm unit1Norm unit2Norm unit3Norm placement =
  placementAtomNormSqExact
    (positiveUnitJet unit0 insertion0)
    (positiveUnitJet unit1 insertion1)
    (inverseUnitJet unit2 insertion2)
    (inverseUnitJet unit3 insertion3)
    (positiveUnitJetNormProfile unit0 insertion0 unit0Norm)
    (positiveUnitJetNormProfile unit1 insertion1 unit1Norm)
    (inverseUnitJetNormProfile unit2 insertion2 unit2Norm)
    (inverseUnitJetNormProfile unit3 insertion3 unit3Norm)
    placement
