module DASHI.Moonshine.P11BrandtAutomorphismWeightExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
-- In the supersingular/Brandt correspondence, automorphism/unit-group mass
-- factors give the natural weighted pairing on ideal/supersingular classes.
--
-- John Voight,
-- "Supersingular elliptic curves", Chapter 42 of the same book.
-- DOI: 10.1007/978-3-030-56694-4_42.
-- Example 42.3.11 gives the p=11 reduced automorphism orders 3 and 2 for the
-- j=0 and j=1728 classes.
--
-- Giulio Codogni and Guido Maria Lido,
-- "Spectral theory of isogeny graphs", Journal of Number Theory 286 (2026),
-- 131--184.
-- DOI: 10.1016/j.jnt.2026.02.006.
-- Their adjacency formalism explicitly retains the extra-automorphism weights
-- rather than assuming the raw multiplicity matrix is symmetric.
--
-- DASHI CONTRIBUTION
--
-- Explain the previously empirical weights (2,3) from the geometric
-- automorphism data.  The reduced automorphism masses are
--
--   j=0    : 3,
--   j=1728 : 2.
--
-- The Brandt pairing uses reciprocal automorphism mass.  Clearing the common
-- denominator 6 therefore gives integral pairing weights
--
--   6/3 = 2,
--   6/2 = 3.
--
-- These are exactly the weights under which the p=11, ell=2 multiplicity
-- matrix [[0,3],[2,1]] satisfies detailed balance.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_)
  renaming (_*_ to _*ℤ_)

import DASHI.Moonshine.P11GeometricSupersingularCarrierExact as Geo
import DASHI.Moonshine.P11ClassicalTwoIsogenyCorrespondenceExact as P11
import DASHI.Moonshine.P11ClassicalTwoIsogenySpectralExact as Spectral

------------------------------------------------------------------------
-- Cleared reciprocal automorphism mass.
------------------------------------------------------------------------

commonAutomorphismMassDenominator : Nat
commonAutomorphismMassDenominator = 6

clearedReciprocalWeight : Geo.P11SupersingularJ → Nat
clearedReciprocalWeight Geo.jZeroSS = 2
clearedReciprocalWeight Geo.j1728SS = 3

jZeroWeightFromAutomorphismMass :
  clearedReciprocalWeight Geo.jZeroSS
  * Geo.reducedAutomorphismOrder Geo.jZeroSS
  ≡ commonAutomorphismMassDenominator
jZeroWeightFromAutomorphismMass = refl

j1728WeightFromAutomorphismMass :
  clearedReciprocalWeight Geo.j1728SS
  * Geo.reducedAutomorphismOrder Geo.j1728SS
  ≡ commonAutomorphismMassDenominator
j1728WeightFromAutomorphismMass = refl

------------------------------------------------------------------------
-- The old spectral weights are now recovered from the source-certified
-- geometric automorphism classes rather than stored as unexplained constants.
------------------------------------------------------------------------

jZeroWeightRecoversSpectralWeight :
  (+ (clearedReciprocalWeight Geo.jZeroSS) : ℤ) ≡ Spectral.weightJ0
jZeroWeightRecoversSpectralWeight = refl

j1728WeightRecoversSpectralWeight :
  (+ (clearedReciprocalWeight Geo.j1728SS) : ℤ) ≡ Spectral.weightJ1
j1728WeightRecoversSpectralWeight = refl

------------------------------------------------------------------------
-- Detailed balance for the actual ell=2 Brandt/isogeny multiplicities.
------------------------------------------------------------------------

geometricDetailedBalanceEll2 :
  clearedReciprocalWeight Geo.jZeroSS * P11.multiplicity P11.j0 P11.j1
  ≡
  clearedReciprocalWeight Geo.j1728SS * P11.multiplicity P11.j1 P11.j0
geometricDetailedBalanceEll2 = refl

geometricDetailedBalanceValueIsSix :
  clearedReciprocalWeight Geo.jZeroSS * P11.multiplicity P11.j0 P11.j1
  ≡ 6
geometricDetailedBalanceValueIsSix = refl

------------------------------------------------------------------------
-- Generic two-state Brandt balance interface for subsequent ell.
------------------------------------------------------------------------

record P11BalancedMultiplicityMatrix : Set where
  constructor p11BalancedMatrix
  field
    a00 a01 a10 a11 : Nat
    row0Degree row1Degree : Nat
    row0Exact : a00 + a01 ≡ row0Degree
    row1Exact : a10 + a11 ≡ row1Degree
    automorphismBalance :
      clearedReciprocalWeight Geo.jZeroSS * a01
      ≡ clearedReciprocalWeight Geo.j1728SS * a10

open P11BalancedMultiplicityMatrix public

ell2BalancedMatrix : P11BalancedMultiplicityMatrix
ell2BalancedMatrix =
  p11BalancedMatrix 0 3 2 1 3 3 refl refl refl

record P11BrandtAutomorphismWeightBoundary : Set where
  field
    reducedAutomorphismMassesConsumed : Bool
    reducedAutomorphismMassesConsumedIsTrue :
      reducedAutomorphismMassesConsumed ≡ true

    reciprocalWeightsDerived : Bool
    reciprocalWeightsDerivedIsTrue : reciprocalWeightsDerived ≡ true

    oldTwoThreeWeightsRecovered : Bool
    oldTwoThreeWeightsRecoveredIsTrue : oldTwoThreeWeightsRecovered ≡ true

    ell2DetailedBalanceDerivedFromThoseWeights : Bool
    ell2DetailedBalanceDerivedFromThoseWeightsIsTrue :
      ell2DetailedBalanceDerivedFromThoseWeights ≡ true

    arbitraryPBrandtWeightTheoremConstructedHere : Bool
    arbitraryPBrandtWeightTheoremConstructedHereIsFalse :
      arbitraryPBrandtWeightTheoremConstructedHere ≡ false

canonicalP11BrandtAutomorphismWeightBoundary :
  P11BrandtAutomorphismWeightBoundary
canonicalP11BrandtAutomorphismWeightBoundary =
  record
    { reducedAutomorphismMassesConsumed = true
    ; reducedAutomorphismMassesConsumedIsTrue = refl
    ; reciprocalWeightsDerived = true
    ; reciprocalWeightsDerivedIsTrue = refl
    ; oldTwoThreeWeightsRecovered = true
    ; oldTwoThreeWeightsRecoveredIsTrue = refl
    ; ell2DetailedBalanceDerivedFromThoseWeights = true
    ; ell2DetailedBalanceDerivedFromThoseWeightsIsTrue = refl
    ; arbitraryPBrandtWeightTheoremConstructedHere = false
    ; arbitraryPBrandtWeightTheoremConstructedHereIsFalse = refl
    }
