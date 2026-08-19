module DASHI.Moonshine.DuncanSwisherDworkRamifiedA1SharpnessExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Bernard Dwork,
-- "$p$-adic cycles", Publications Mathematiques de l'IHES 37 (1969),
-- 27--115. DOI: 10.1007/BF02684886.
-- Theorem 8.2 and the exceptional Legendre-coordinate discussion at the
-- beginning of Section 7.e, as used by Duncan--Swisher.
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv:2602.09135. DOI: 10.48550/arXiv.2602.09135.
-- Proposition 3.1 and its sharpness proof.
--
-- SOURCE SHAPE
--
-- Duncan--Swisher use Dwork Theorem 8.2 for the ordinary sharp first-pole
-- coefficient, and then Dwork Section 7.e for the exceptional Legendre local
-- coordinates
--
--   J_1 + 744 ~ (lambda-lambda_0)^3  at j=0,
--   J_1 - 984 ~ (lambda-lambda_0)^2  at j=1728.
--
-- The exact sharpness mechanism therefore requires MORE than a ramification
-- integer.  One needs the Dwork depth-one local branch, a valuation-zero local
-- unit, and the source-native factorization of A_1 through the ramified branch.
--
-- DASHI CONTRIBUTION
--
-- The imported source authority below contains NO numeric A_1 depth field.
-- Once its structural local factorization is supplied, the generic ramified
-- valuation theorem derives
--
--   v_p(A_1) = ramification index,
--
-- and only then specializes to 3,2,1.  At p=11 this is further welded to the
-- existing source-native Brandt monodromy weight on the SAME supersingular
-- j-class carrier.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Algebra.RamifiedLocalValuationSharpnessExact as Ramified
import DASHI.Moonshine.DuncanSwisherDeligneAutomorphismDepthBridgeExact as Aut
import DASHI.Moonshine.DuncanSwisherLegendreRamificationDepthExact as Legendre
import DASHI.Moonshine.P11GeometricSupersingularCarrierExact as Geo

record DworkLocalA1Factorization
    (t : Aut.SupersingularAutomorphismType) : Set₁ where
  field
    PadicLocal : Set
    padicValuation : Ramified.MultiplicativeNatValuation PadicLocal

    localUnit : PadicLocal
    dworkSharpBranch : PadicLocal
    A1Coefficient : PadicLocal

    localUnitIsUnit : Ramified.valuation padicValuation localUnit ≡ 0
    dworkOrdinaryBranchSharp :
      Ramified.valuation padicValuation dworkSharpBranch ≡ 1

    localRamifiedFactorization :
      A1Coefficient
      ≡ Ramified.mul padicValuation localUnit
          (Ramified.pow
            padicValuation
            dworkSharpBranch
            (Legendre.legendreJRamificationIndex t))

open DworkLocalA1Factorization public

postulate
  publishedDworkLocalA1Factorization :
    (t : Aut.SupersingularAutomorphismType) → DworkLocalA1Factorization t

asRamifiedSharpCoefficient :
  (t : Aut.SupersingularAutomorphismType) →
  let A = publishedDworkLocalA1Factorization t
  in Ramified.RamifiedSharpCoefficient
      (padicValuation A)
      (Legendre.legendreJRamificationIndex t)
asRamifiedSharpCoefficient t =
  let A = publishedDworkLocalA1Factorization t
  in record
    { Ramified.localUnit = localUnit A
    ; Ramified.localBranch = dworkSharpBranch A
    ; Ramified.coefficient = A1Coefficient A
    ; Ramified.localUnitDepthZero = localUnitIsUnit A
    ; Ramified.localBranchDepthOne = dworkOrdinaryBranchSharp A
    ; Ramified.coefficientFactorization = localRamifiedFactorization A
    }

sharpA1DepthIsRamification :
  (t : Aut.SupersingularAutomorphismType) →
  let A = publishedDworkLocalA1Factorization t
  in Ramified.valuation (padicValuation A) (A1Coefficient A)
      ≡ Legendre.legendreJRamificationIndex t
sharpA1DepthIsRamification t =
  let A = publishedDworkLocalA1Factorization t
  in Ramified.ramifiedSharpCoefficientValuation
      (padicValuation A)
      (Legendre.legendreJRamificationIndex t)
      (asRamifiedSharpCoefficient t)

jZeroA1DepthIsThree :
  let A = publishedDworkLocalA1Factorization Aut.jZeroExceptional
  in Ramified.valuation (padicValuation A) (A1Coefficient A) ≡ 3
jZeroA1DepthIsThree = sharpA1DepthIsRamification Aut.jZeroExceptional

j1728A1DepthIsTwo :
  let A = publishedDworkLocalA1Factorization Aut.j1728Exceptional
  in Ramified.valuation (padicValuation A) (A1Coefficient A) ≡ 2
j1728A1DepthIsTwo = sharpA1DepthIsRamification Aut.j1728Exceptional

ordinaryA1DepthIsOne :
  let A = publishedDworkLocalA1Factorization Aut.ordinaryType
  in Ramified.valuation (padicValuation A) (A1Coefficient A) ≡ 1
ordinaryA1DepthIsOne = sharpA1DepthIsRamification Aut.ordinaryType

sharpA1DepthMatchesExistingFirstPoleDepth :
  (t : Aut.SupersingularAutomorphismType) →
  let A = publishedDworkLocalA1Factorization t
  in Ramified.valuation (padicValuation A) (A1Coefficient A)
      ≡ Aut.deligneFirstPoleDepth t
sharpA1DepthMatchesExistingFirstPoleDepth Aut.jZeroExceptional = jZeroA1DepthIsThree
sharpA1DepthMatchesExistingFirstPoleDepth Aut.j1728Exceptional = j1728A1DepthIsTwo
sharpA1DepthMatchesExistingFirstPoleDepth Aut.ordinaryType = ordinaryA1DepthIsOne

sharpA1DepthDoublesToFullAutomorphismOrder :
  (t : Aut.SupersingularAutomorphismType) →
  let A = publishedDworkLocalA1Factorization t
  in 2 * Ramified.valuation (padicValuation A) (A1Coefficient A)
      ≡ Aut.fullAutomorphismOrder t
sharpA1DepthDoublesToFullAutomorphismOrder t =
  trans
    (cong (λ d → 2 * d) (sharpA1DepthMatchesExistingFirstPoleDepth t))
    (Aut.firstPoleDepthDoublesToFullAutomorphismOrder t)

------------------------------------------------------------------------
-- Same-object p=11 weld: Dwork depth = Legendre ramification = Brandt weight.
------------------------------------------------------------------------

p11A1DepthIsBrandtMonodromyWeight :
  (c : Geo.P11SupersingularJ) →
  let A = publishedDworkLocalA1Factorization (Legendre.p11AutType c)
  in Ramified.valuation (padicValuation A) (A1Coefficient A)
      ≡ Legendre.Stack11.p11MonodromyWeight c
p11A1DepthIsBrandtMonodromyWeight c =
  trans
    (sharpA1DepthIsRamification (Legendre.p11AutType c))
    (Legendre.p11RamificationIsBrandtMonodromyWeight c)

p11JZeroA1DepthWeightIsThree :
  let A = publishedDworkLocalA1Factorization (Legendre.p11AutType Geo.jZeroSS)
  in Ramified.valuation (padicValuation A) (A1Coefficient A) ≡ 3
p11JZeroA1DepthWeightIsThree = jZeroA1DepthIsThree

p11J1728A1DepthWeightIsTwo :
  let A = publishedDworkLocalA1Factorization (Legendre.p11AutType Geo.j1728SS)
  in Ramified.valuation (padicValuation A) (A1Coefficient A) ≡ 2
p11J1728A1DepthWeightIsTwo = j1728A1DepthIsTwo

record DuncanSwisherDworkRamifiedA1SharpnessBoundary : Set where
  field
    dworkOrdinaryBranchDepthOneImported : Bool
    legendreRamifiedLocalFactorizationImported : Bool
    numericA1DepthTableImportedSeparately : Bool
    ramificationToExactA1DepthDerived : Bool
    exactJZeroDepthThreeDerived : Bool
    exactJ1728DepthTwoDerived : Bool
    exactOrdinaryDepthOneDerived : Bool
    depthToAutomorphismOrderDerived : Bool
    p11A1DepthEqualsBrandtWeightDerived : Bool
    fullDworkPadicCyclesConstructionReproved : Bool

canonicalDuncanSwisherDworkRamifiedA1SharpnessBoundary :
  DuncanSwisherDworkRamifiedA1SharpnessBoundary
canonicalDuncanSwisherDworkRamifiedA1SharpnessBoundary = record
  { dworkOrdinaryBranchDepthOneImported = true
  ; legendreRamifiedLocalFactorizationImported = true
  ; numericA1DepthTableImportedSeparately = false
  ; ramificationToExactA1DepthDerived = true
  ; exactJZeroDepthThreeDerived = true
  ; exactJ1728DepthTwoDerived = true
  ; exactOrdinaryDepthOneDerived = true
  ; depthToAutomorphismOrderDerived = true
  ; p11A1DepthEqualsBrandtWeightDerived = true
  ; fullDworkPadicCyclesConstructionReproved = false
  }
