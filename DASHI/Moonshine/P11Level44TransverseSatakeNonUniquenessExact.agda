module DASHI.Moonshine.P11Level44TransverseSatakeNonUniquenessExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Ralf Schmidt,
-- "Some remarks on local newforms for GL(2)",
-- J. Ramanujan Math. Soc. 17 (2002), 115--147.
--
-- William Casselman,
-- "On some results of Atkin and Lehner", Math. Ann. 201 (1973), 301--314.
-- DOI: 10.1007/BF01428197.
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", GTM 228, Springer, 2005.
-- DOI: 10.1007/978-0-387-27226-9.
--
-- DASHI CONTRIBUTION
--
-- P11Level44TwoAdicTransverseAlignmentExact reduces the compact comparison to
-- two simplest integral alignments that agree on the common two-plane and
-- differ by transverse sign.  P11CasselmanBruhatDegeneracyChartExact now puts
-- the ACTUAL classical U2 on the correctly ordered K_0(4) Casselman cells.
--
-- Conjugate that U2 through BOTH alignments.  The resulting distinct principal
-- full-level-2 candidate operators are
--
--   P+(x,y,z) = (-3x+y+z, -5x+y+2z, 0),
--   P-(x,y,z) = (-x-y+z,    x-y,      0).
--
-- Despite being distinct, they have EXACTLY THE SAME Satake residual:
--
--   (P+^2+2P++2I)(x,y,z)
--     = (z,z,2z)
--     = (P-^2+2P-+2I)(x,y,z).
--
-- Hence both satisfy
--
--   P (P^2+2P+2I)=0,
--
-- both send the deepest basis vector to the same kernel generator (1,1,2)
-- under the Satake quadratic, and both kill that same generator.
--
-- Therefore the full a_2=-2 Satake polynomial, its residual map and its kernel
-- line STILL do not select the transverse sign.  The remaining local producer
-- must consume a finer source-native datum such as a Whittaker/test-vector
-- normalization or an explicitly oriented noncompact matrix coefficient.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer using (ℤ; +_; -[1+_])
import Data.Integer as Int
import Data.Integer.Tactic.RingSolver as ℤRing

import DASHI.Moonshine.P11MarkedLevel44PermutationIntertwinerExact as Principal
import DASHI.Moonshine.P11Level44TwoAdicAveragingNoGoExact as K0
import DASHI.Moonshine.P11Level44TwoAdicFixedSpaceIntersectionExact as Intersection
import DASHI.Moonshine.P11Level44TwoAdicTransverseAlignmentExact as Transverse
import DASHI.Moonshine.P11CasselmanBruhatDegeneracyChartExact as Chart

------------------------------------------------------------------------
-- Actual U2 transported through the two existing transverse alignments.
------------------------------------------------------------------------

plusPrincipalU2 : Principal.Old3 → Principal.Old3
plusPrincipalU2 p =
  Transverse.plusK0ToPrincipal
    (Chart.analyticU2OnK0 (Transverse.plusPrincipalToK0 p))

minusPrincipalU2 : Principal.Old3 → Principal.Old3
minusPrincipalU2 p =
  Transverse.minusK0ToPrincipal
    (Chart.analyticU2OnK0 (Transverse.minusPrincipalToK0 p))

plusPrincipalU2Formula :
  (p : Principal.Old3) →
  plusPrincipalU2 p
  ≡ Principal.old3
      (Int._+_ (Int._+_ (Int._*_ (-[1+ 2 ]) (Principal.x1 p)) (Principal.x2 p)) (Principal.x4 p))
      (Int._+_ (Int._+_ (Int._*_ (-[1+ 4 ]) (Principal.x1 p)) (Principal.x2 p))
        (Int._*_ (+ 2) (Principal.x4 p)))
      (+ 0)
plusPrincipalU2Formula p =
  Transverse.old3Ext _ _
    (ℤRing.solve (Principal.x1 p ∷ Principal.x2 p ∷ Principal.x4 p ∷ []))
    (ℤRing.solve (Principal.x1 p ∷ Principal.x2 p ∷ Principal.x4 p ∷ []))
    (ℤRing.solve (Principal.x1 p ∷ Principal.x2 p ∷ Principal.x4 p ∷ []))

minusPrincipalU2Formula :
  (p : Principal.Old3) →
  minusPrincipalU2 p
  ≡ Principal.old3
      (Int._+_ (Int._+_ (Int._-_ (+ 0) (Principal.x1 p))
        (Int._-_ (+ 0) (Principal.x2 p))) (Principal.x4 p))
      (Int._-_ (Principal.x1 p) (Principal.x2 p))
      (+ 0)
minusPrincipalU2Formula p =
  Transverse.old3Ext _ _
    (ℤRing.solve (Principal.x1 p ∷ Principal.x2 p ∷ Principal.x4 p ∷ []))
    (ℤRing.solve (Principal.x1 p ∷ Principal.x2 p ∷ Principal.x4 p ∷ []))
    (ℤRing.solve (Principal.x1 p ∷ Principal.x2 p ∷ Principal.x4 p ∷ []))

------------------------------------------------------------------------
-- The two transported operators are genuinely distinct.
------------------------------------------------------------------------

plusOnTransverseBasis :
  plusPrincipalU2 Principal.oldBasis2
  ≡ Principal.old3 (+ 1) (+ 1) (+ 0)
plusOnTransverseBasis = refl

minusOnTransverseBasis :
  minusPrincipalU2 Principal.oldBasis2
  ≡ Principal.old3 (-[1+ 0 ]) (-[1+ 0 ]) (+ 0)
minusOnTransverseBasis = refl

plusMinusOperatorsDistinct :
  ((v : Principal.Old3) → plusPrincipalU2 v ≡ minusPrincipalU2 v) → ⊥
plusMinusOperatorsDistinct allEqual with allEqual Principal.oldBasis2
... | ()

------------------------------------------------------------------------
-- Shared Satake quadratic Q(P)=P^2+2P+2I.
------------------------------------------------------------------------

plusSatakeQuadratic : Principal.Old3 → Principal.Old3
plusSatakeQuadratic p =
  Principal.addOld3
    (plusPrincipalU2 (plusPrincipalU2 p))
    (Principal.addOld3
      (Principal.scaleOld3 (+ 2) (plusPrincipalU2 p))
      (Principal.scaleOld3 (+ 2) p))

minusSatakeQuadratic : Principal.Old3 → Principal.Old3
minusSatakeQuadratic p =
  Principal.addOld3
    (minusPrincipalU2 (minusPrincipalU2 p))
    (Principal.addOld3
      (Principal.scaleOld3 (+ 2) (minusPrincipalU2 p))
      (Principal.scaleOld3 (+ 2) p))

plusSatakeQuadraticFormula :
  (p : Principal.Old3) →
  plusSatakeQuadratic p
  ≡ Principal.old3
      (Principal.x4 p)
      (Principal.x4 p)
      (Int._*_ (+ 2) (Principal.x4 p))
plusSatakeQuadraticFormula p =
  Transverse.old3Ext _ _
    (ℤRing.solve (Principal.x1 p ∷ Principal.x2 p ∷ Principal.x4 p ∷ []))
    (ℤRing.solve (Principal.x1 p ∷ Principal.x2 p ∷ Principal.x4 p ∷ []))
    (ℤRing.solve (Principal.x1 p ∷ Principal.x2 p ∷ Principal.x4 p ∷ []))

minusSatakeQuadraticFormula :
  (p : Principal.Old3) →
  minusSatakeQuadratic p
  ≡ Principal.old3
      (Principal.x4 p)
      (Principal.x4 p)
      (Int._*_ (+ 2) (Principal.x4 p))
minusSatakeQuadraticFormula p =
  Transverse.old3Ext _ _
    (ℤRing.solve (Principal.x1 p ∷ Principal.x2 p ∷ Principal.x4 p ∷ []))
    (ℤRing.solve (Principal.x1 p ∷ Principal.x2 p ∷ Principal.x4 p ∷ []))
    (ℤRing.solve (Principal.x1 p ∷ Principal.x2 p ∷ Principal.x4 p ∷ []))

satakeResidualsIdentical :
  (p : Principal.Old3) → plusSatakeQuadratic p ≡ minusSatakeQuadratic p
satakeResidualsIdentical p =
  trans (plusSatakeQuadraticFormula p) (sym (minusSatakeQuadraticFormula p))

------------------------------------------------------------------------
-- Same cubic identity and same kernel line.
------------------------------------------------------------------------

plusCubicSatakeIdentity :
  (p : Principal.Old3) →
  plusPrincipalU2 (plusSatakeQuadratic p)
  ≡ Principal.old3 (+ 0) (+ 0) (+ 0)
plusCubicSatakeIdentity p =
  Transverse.old3Ext _ _
    (ℤRing.solve (Principal.x1 p ∷ Principal.x2 p ∷ Principal.x4 p ∷ []))
    (ℤRing.solve (Principal.x1 p ∷ Principal.x2 p ∷ Principal.x4 p ∷ []))
    (ℤRing.solve (Principal.x1 p ∷ Principal.x2 p ∷ Principal.x4 p ∷ []))

minusCubicSatakeIdentity :
  (p : Principal.Old3) →
  minusPrincipalU2 (minusSatakeQuadratic p)
  ≡ Principal.old3 (+ 0) (+ 0) (+ 0)
minusCubicSatakeIdentity p =
  Transverse.old3Ext _ _
    (ℤRing.solve (Principal.x1 p ∷ Principal.x2 p ∷ Principal.x4 p ∷ []))
    (ℤRing.solve (Principal.x1 p ∷ Principal.x2 p ∷ Principal.x4 p ∷ []))
    (ℤRing.solve (Principal.x1 p ∷ Principal.x2 p ∷ Principal.x4 p ∷ []))

principalKernelGenerator : Principal.Old3
principalKernelGenerator = Principal.old3 (+ 1) (+ 1) (+ 2)

plusKernelGeneratorKilled :
  plusPrincipalU2 principalKernelGenerator
  ≡ Principal.old3 (+ 0) (+ 0) (+ 0)
plusKernelGeneratorKilled = refl

minusKernelGeneratorKilled :
  minusPrincipalU2 principalKernelGenerator
  ≡ Principal.old3 (+ 0) (+ 0) (+ 0)
minusKernelGeneratorKilled = refl

plusDeepestResidualIsKernelGenerator :
  plusSatakeQuadratic Principal.oldBasis4 ≡ principalKernelGenerator
plusDeepestResidualIsKernelGenerator = refl

minusDeepestResidualIsKernelGenerator :
  minusSatakeQuadratic Principal.oldBasis4 ≡ principalKernelGenerator
minusDeepestResidualIsKernelGenerator = refl

------------------------------------------------------------------------
-- On the common plane the common coordinates of P+ and P- agree, while their
-- output defects are opposite.  Satake sees the common output but not its
-- transverse orientation.
------------------------------------------------------------------------

plusMinusCommonOutputAgree :
  (c : Intersection.Common2) →
  Transverse.common
    (Transverse.principalSplit
      (plusPrincipalU2 (Intersection.principalCommon c)))
  ≡ Transverse.common
    (Transverse.principalSplit
      (minusPrincipalU2 (Intersection.principalCommon c)))
plusMinusCommonOutputAgree (Intersection.common2 a b) =
  refl

plusMinusDefectsOppositeOnCommon :
  (c : Intersection.Common2) →
  Transverse.defect
    (Transverse.principalSplit
      (plusPrincipalU2 (Intersection.principalCommon c)))
  ≡ Int.-_
    (Transverse.defect
      (Transverse.principalSplit
        (minusPrincipalU2 (Intersection.principalCommon c))))
plusMinusDefectsOppositeOnCommon (Intersection.common2 a b) =
  ℤRing.solve (a ∷ b ∷ [])

record P11Level44TransverseSatakeNonUniquenessBoundary : Set where
  field
    correctlyOrderedCasselmanU2Consumed : Bool
    plusTransportedOperatorConstructed : Bool
    minusTransportedOperatorConstructed : Bool
    transportedOperatorsDistinct : Bool
    satakeResidualMapsIdentical : Bool
    cubicSatakeIdentityHoldsForBoth : Bool
    kernelGeneratorSameForBoth : Bool
    commonOutputSameTransverseOutputOpposite : Bool
    satakePolynomialSelectsTransverseSign : Bool
    whittakerOrMatrixCoefficientNormalizationStillRequired : Bool

canonicalP11Level44TransverseSatakeNonUniquenessBoundary :
  P11Level44TransverseSatakeNonUniquenessBoundary
canonicalP11Level44TransverseSatakeNonUniquenessBoundary = record
  { correctlyOrderedCasselmanU2Consumed = true
  ; plusTransportedOperatorConstructed = true
  ; minusTransportedOperatorConstructed = true
  ; transportedOperatorsDistinct = true
  ; satakeResidualMapsIdentical = true
  ; cubicSatakeIdentityHoldsForBoth = true
  ; kernelGeneratorSameForBoth = true
  ; commonOutputSameTransverseOutputOpposite = true
  ; satakePolynomialSelectsTransverseSign = false
  ; whittakerOrMatrixCoefficientNormalizationStillRequired = true
  }
