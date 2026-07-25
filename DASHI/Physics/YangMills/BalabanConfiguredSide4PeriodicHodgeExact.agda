module DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicHodgeExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; 1ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (SiteField; sumRational; sumRationalCong)
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using (sq)
open import DASHI.Physics.YangMills.BalabanPath4PlaquetteOrientationExact
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicVectorCalculusExact

------------------------------------------------------------------------
-- Scalar component energies.
------------------------------------------------------------------------

two : ℚ
two = 1ℚ + 1ℚ

forwardDerivativeEnergy : Axis4 → SiteField side4 → ℚ
forwardDerivativeEnergy derivative field =
  siteSum4 (λ site → sq (forwardDifference4 derivative field site))

backwardDerivativeEnergy : Axis4 → SiteField side4 → ℚ
backwardDerivativeEnergy derivative field =
  siteSum4 (λ site → sq (backwardDifference4 derivative field site))

mixedForwardEnergy : Axis4 → Axis4 → SiteField side4 → SiteField side4 → ℚ
mixedForwardEnergy first second hFirst hSecond =
  siteSum4 (λ site →
    forwardDifference4 first hSecond site
    * forwardDifference4 second hFirst site)

mixedBackwardEnergy : Axis4 → Axis4 → SiteField side4 → SiteField side4 → ℚ
mixedBackwardEnergy first second hFirst hSecond =
  siteSum4 (λ site →
    backwardDifference4 first hFirst site
    * backwardDifference4 second hSecond site)

curlPlaneEnergy : PositivePlaquettePlane4 → ScalarBondField4 → ℚ
curlPlaneEnergy plane field =
  siteSum4 (λ site → sq
    (forwardDifference4 (positivePlaneFirst plane)
      (field (positivePlaneSecond plane)) site
    - forwardDifference4 (positivePlaneSecond plane)
      (field (positivePlaneFirst plane)) site))

componentCurlEnergy : ScalarBondField4 → ℚ
componentCurlEnergy field =
  sumRational positivePlaquettePlanes4 (λ plane → curlPlaneEnergy plane field)

componentDivergenceEnergy : ScalarBondField4 → ℚ
componentDivergenceEnergy field =
  siteSum4 (λ site → sq (literalPeriodicDivergenceScalar field site))

componentPeriodicDifferenceEnergy : ScalarBondField4 → ℚ
componentPeriodicDifferenceEnergy field =
  sumRational (allCyclicIndices four) (λ componentAxis →
    sumRational (allCyclicIndices four) (λ derivativeAxis →
      forwardDerivativeEnergy derivativeAxis (field componentAxis)))

------------------------------------------------------------------------
-- Backward and forward diagonal energies agree by periodic reindexing.
------------------------------------------------------------------------

backwardDifferenceAsForwardAtBackward : ∀ axis field site →
  backwardDifference4 axis field site
  ≡ forwardDifference4 axis field (shiftBackward4 axis site)
backwardDifferenceAsForwardAtBackward axis field site
  rewrite forwardAfterBackward4 axis site =
  ℚRing.solve-∀ (field site) (field (shiftBackward4 axis site))

forwardBackwardNormSqExact : ∀ axis field →
  backwardDerivativeEnergy axis field ≡ forwardDerivativeEnergy axis field
forwardBackwardNormSqExact axis field =
  trans
    (siteSum4Cong _ _ (λ site →
      cong₂ _*_
        (backwardDifferenceAsForwardAtBackward axis field site)
        (backwardDifferenceAsForwardAtBackward axis field site)))
    (periodicBackwardReindexing axis
      (λ site → sq (forwardDifference4 axis field site)))

------------------------------------------------------------------------
-- Expand each positive-plane square.
------------------------------------------------------------------------

siteSum4ThreeTerms : ∀ first second third →
  siteSum4 (λ site → first site + (second site + third site))
  ≡ siteSum4 first + (siteSum4 second + siteSum4 third)
siteSum4ThreeTerms first second third =
  trans
    (siteSum4Add first (λ site → second site + third site))
    (cong₂ _+_ refl (siteSum4Add second third))

positivePlaneSquareExpansion : ∀ plane field →
  curlPlaneEnergy plane field
  ≡ forwardDerivativeEnergy (positivePlaneFirst plane)
      (field (positivePlaneSecond plane))
    + (forwardDerivativeEnergy (positivePlaneSecond plane)
        (field (positivePlaneFirst plane))
    - two * mixedForwardEnergy
        (positivePlaneFirst plane) (positivePlaneSecond plane)
        (field (positivePlaneFirst plane))
        (field (positivePlaneSecond plane)))
positivePlaneSquareExpansion plane field =
  trans
    (siteSum4Cong _ _ (λ site → ℚRing.solve-∀
      (forwardDifference4 (positivePlaneFirst plane)
        (field (positivePlaneSecond plane)) site)
      (forwardDifference4 (positivePlaneSecond plane)
        (field (positivePlaneFirst plane)) site)))
    (trans
      (siteSum4ThreeTerms
        (λ site → sq (forwardDifference4 (positivePlaneFirst plane)
          (field (positivePlaneSecond plane)) site))
        (λ site → sq (forwardDifference4 (positivePlaneSecond plane)
          (field (positivePlaneFirst plane)) site))
        (λ site → (- two) *
          (forwardDifference4 (positivePlaneFirst plane)
            (field (positivePlaneSecond plane)) site
          * forwardDifference4 (positivePlaneSecond plane)
            (field (positivePlaneFirst plane)) site)))
      (trans
        (cong₂ _+_ refl
          (cong₂ _+_ refl
            (siteSum4Scale (- two)
              (λ site →
                forwardDifference4 (positivePlaneFirst plane)
                  (field (positivePlaneSecond plane)) site
                * forwardDifference4 (positivePlaneSecond plane)
                  (field (positivePlaneFirst plane)) site))))
        (ℚRing.solve-∀
          (forwardDerivativeEnergy (positivePlaneFirst plane)
            (field (positivePlaneSecond plane)))
          (forwardDerivativeEnergy (positivePlaneSecond plane)
            (field (positivePlaneFirst plane)))
          (mixedForwardEnergy
            (positivePlaneFirst plane) (positivePlaneSecond plane)
            (field (positivePlaneFirst plane))
            (field (positivePlaneSecond plane))))))

componentCurlExpanded : ScalarBondField4 → ℚ
componentCurlExpanded field =
  (forwardDerivativeEnergy axis0 (field axis1)
    + forwardDerivativeEnergy axis1 (field axis0)
    - two * mixedForwardEnergy axis0 axis1 (field axis0) (field axis1))
  + ((forwardDerivativeEnergy axis0 (field axis2)
    + forwardDerivativeEnergy axis2 (field axis0)
    - two * mixedForwardEnergy axis0 axis2 (field axis0) (field axis2))
  + ((forwardDerivativeEnergy axis0 (field axis3)
    + forwardDerivativeEnergy axis3 (field axis0)
    - two * mixedForwardEnergy axis0 axis3 (field axis0) (field axis3))
  + ((forwardDerivativeEnergy axis1 (field axis2)
    + forwardDerivativeEnergy axis2 (field axis1)
    - two * mixedForwardEnergy axis1 axis2 (field axis1) (field axis2))
  + ((forwardDerivativeEnergy axis1 (field axis3)
    + forwardDerivativeEnergy axis3 (field axis1)
    - two * mixedForwardEnergy axis1 axis3 (field axis1) (field axis3))
  + (forwardDerivativeEnergy axis2 (field axis3)
    + forwardDerivativeEnergy axis3 (field axis2)
    - two * mixedForwardEnergy axis2 axis3 (field axis2) (field axis3))))))

componentCurlEnergyExpansion : ∀ field →
  componentCurlEnergy field ≡ componentCurlExpanded field
componentCurlEnergyExpansion field
  rewrite positivePlaneSquareExpansion plane01 field
        | positivePlaneSquareExpansion plane02 field
        | positivePlaneSquareExpansion plane03 field
        | positivePlaneSquareExpansion plane12 field
        | positivePlaneSquareExpansion plane13 field
        | positivePlaneSquareExpansion plane23 field =
  ℚRing.solve-∀
    (curlPlaneEnergy plane01 field)
    (curlPlaneEnergy plane02 field)
    (curlPlaneEnergy plane03 field)
    (curlPlaneEnergy plane12 field)
    (curlPlaneEnergy plane13 field)
    (curlPlaneEnergy plane23 field)

------------------------------------------------------------------------
-- Expand the four-axis divergence square into four diagonal and six mixed terms.
------------------------------------------------------------------------

siteSum4TenTerms : ∀ t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 →
  siteSum4 (λ site →
    t0 site + (t1 site + (t2 site + (t3 site +
    (t4 site + (t5 site + (t6 site + (t7 site + (t8 site + t9 site)))))))))
  ≡ siteSum4 t0 + (siteSum4 t1 + (siteSum4 t2 + (siteSum4 t3 +
    (siteSum4 t4 + (siteSum4 t5 + (siteSum4 t6 +
    (siteSum4 t7 + (siteSum4 t8 + siteSum4 t9))))))))
siteSum4TenTerms t0 t1 t2 t3 t4 t5 t6 t7 t8 t9
  rewrite siteSum4Add t0 (λ site →
      t1 site + (t2 site + (t3 site + (t4 site + (t5 site +
      (t6 site + (t7 site + (t8 site + t9 site))))))))
        | siteSum4Add t1 (λ site →
          t2 site + (t3 site + (t4 site + (t5 site +
          (t6 site + (t7 site + (t8 site + t9 site)))))))
        | siteSum4Add t2 (λ site →
          t3 site + (t4 site + (t5 site +
          (t6 site + (t7 site + (t8 site + t9 site))))))
        | siteSum4Add t3 (λ site →
          t4 site + (t5 site + (t6 site +
          (t7 site + (t8 site + t9 site)))))
        | siteSum4Add t4 (λ site →
          t5 site + (t6 site + (t7 site + (t8 site + t9 site))))
        | siteSum4Add t5 (λ site →
          t6 site + (t7 site + (t8 site + t9 site)))
        | siteSum4Add t6 (λ site → t7 site + (t8 site + t9 site))
        | siteSum4Add t7 (λ site → t8 site + t9 site)
        | siteSum4Add t8 t9 = refl

componentDivergenceExpanded : ScalarBondField4 → ℚ
componentDivergenceExpanded field =
  backwardDerivativeEnergy axis0 (field axis0)
  + (backwardDerivativeEnergy axis1 (field axis1)
  + (backwardDerivativeEnergy axis2 (field axis2)
  + (backwardDerivativeEnergy axis3 (field axis3)
  + (two * mixedBackwardEnergy axis0 axis1 (field axis0) (field axis1)
  + (two * mixedBackwardEnergy axis0 axis2 (field axis0) (field axis2)
  + (two * mixedBackwardEnergy axis0 axis3 (field axis0) (field axis3)
  + (two * mixedBackwardEnergy axis1 axis2 (field axis1) (field axis2)
  + (two * mixedBackwardEnergy axis1 axis3 (field axis1) (field axis3)
  + two * mixedBackwardEnergy axis2 axis3 (field axis2) (field axis3)))))))))

componentDivergenceEnergyExpansion : ∀ field →
  componentDivergenceEnergy field ≡ componentDivergenceExpanded field
componentDivergenceEnergyExpansion field =
  trans
    (siteSum4Cong _ _ (λ site → ℚRing.solve-∀
      (backwardDifference4 axis0 (field axis0) site)
      (backwardDifference4 axis1 (field axis1) site)
      (backwardDifference4 axis2 (field axis2) site)
      (backwardDifference4 axis3 (field axis3) site)))
    (trans
      (siteSum4TenTerms
        (λ site → sq (backwardDifference4 axis0 (field axis0) site))
        (λ site → sq (backwardDifference4 axis1 (field axis1) site))
        (λ site → sq (backwardDifference4 axis2 (field axis2) site))
        (λ site → sq (backwardDifference4 axis3 (field axis3) site))
        (λ site → two * backwardDifference4 axis0 (field axis0) site
          * backwardDifference4 axis1 (field axis1) site)
        (λ site → two * backwardDifference4 axis0 (field axis0) site
          * backwardDifference4 axis2 (field axis2) site)
        (λ site → two * backwardDifference4 axis0 (field axis0) site
          * backwardDifference4 axis3 (field axis3) site)
        (λ site → two * backwardDifference4 axis1 (field axis1) site
          * backwardDifference4 axis2 (field axis2) site)
        (λ site → two * backwardDifference4 axis1 (field axis1) site
          * backwardDifference4 axis3 (field axis3) site)
        (λ site → two * backwardDifference4 axis2 (field axis2) site
          * backwardDifference4 axis3 (field axis3) site))
      (trans
        (cong₂ _+_ refl (cong₂ _+_ refl (cong₂ _+_ refl (cong₂ _+_
          (siteSum4Scale two (λ site →
            backwardDifference4 axis0 (field axis0) site
            * backwardDifference4 axis1 (field axis1) site))
          (cong₂ _+_
            (siteSum4Scale two (λ site →
              backwardDifference4 axis0 (field axis0) site
              * backwardDifference4 axis2 (field axis2) site))
            (cong₂ _+_
              (siteSum4Scale two (λ site →
                backwardDifference4 axis0 (field axis0) site
                * backwardDifference4 axis3 (field axis3) site))
              (cong₂ _+_
                (siteSum4Scale two (λ site →
                  backwardDifference4 axis1 (field axis1) site
                  * backwardDifference4 axis2 (field axis2) site))
                (cong₂ _+_
                  (siteSum4Scale two (λ site →
                    backwardDifference4 axis1 (field axis1) site
                    * backwardDifference4 axis3 (field axis3) site))
                  (siteSum4Scale two (λ site →
                    backwardDifference4 axis2 (field axis2) site
                    * backwardDifference4 axis3 (field axis3) site))))))))))
        refl))

------------------------------------------------------------------------
-- Explicit sixteen-term full difference fold.
------------------------------------------------------------------------

componentPeriodicDifferenceExpanded : ScalarBondField4 → ℚ
componentPeriodicDifferenceExpanded field =
  forwardDerivativeEnergy axis0 (field axis0)
  + (forwardDerivativeEnergy axis1 (field axis0)
  + (forwardDerivativeEnergy axis2 (field axis0)
  + (forwardDerivativeEnergy axis3 (field axis0)
  + (forwardDerivativeEnergy axis0 (field axis1)
  + (forwardDerivativeEnergy axis1 (field axis1)
  + (forwardDerivativeEnergy axis2 (field axis1)
  + (forwardDerivativeEnergy axis3 (field axis1)
  + (forwardDerivativeEnergy axis0 (field axis2)
  + (forwardDerivativeEnergy axis1 (field axis2)
  + (forwardDerivativeEnergy axis2 (field axis2)
  + (forwardDerivativeEnergy axis3 (field axis2)
  + (forwardDerivativeEnergy axis0 (field axis3)
  + (forwardDerivativeEnergy axis1 (field axis3)
  + (forwardDerivativeEnergy axis2 (field axis3)
  + forwardDerivativeEnergy axis3 (field axis3)))))))))))))))

componentPeriodicDifferenceEnergyExpansion : ∀ field →
  componentPeriodicDifferenceEnergy field
  ≡ componentPeriodicDifferenceExpanded field
componentPeriodicDifferenceEnergyExpansion field =
  ℚRing.solve-∀
    (forwardDerivativeEnergy axis0 (field axis0))
    (forwardDerivativeEnergy axis1 (field axis0))
    (forwardDerivativeEnergy axis2 (field axis0))
    (forwardDerivativeEnergy axis3 (field axis0))
    (forwardDerivativeEnergy axis0 (field axis1))
    (forwardDerivativeEnergy axis1 (field axis1))
    (forwardDerivativeEnergy axis2 (field axis1))
    (forwardDerivativeEnergy axis3 (field axis1))
    (forwardDerivativeEnergy axis0 (field axis2))
    (forwardDerivativeEnergy axis1 (field axis2))
    (forwardDerivativeEnergy axis2 (field axis2))
    (forwardDerivativeEnergy axis3 (field axis2))
    (forwardDerivativeEnergy axis0 (field axis3))
    (forwardDerivativeEnergy axis1 (field axis3))
    (forwardDerivativeEnergy axis2 (field axis3))
    (forwardDerivativeEnergy axis3 (field axis3))

------------------------------------------------------------------------
-- Component and three-component periodic Hodge identities.
------------------------------------------------------------------------

fourAxisDiagonalOffDiagonalPartition : ∀ field →
  componentCurlExpanded field + componentDivergenceExpanded field
  ≡ componentPeriodicDifferenceExpanded field
fourAxisDiagonalOffDiagonalPartition field
  rewrite forwardBackwardNormSqExact axis0 (field axis0)
        | forwardBackwardNormSqExact axis1 (field axis1)
        | forwardBackwardNormSqExact axis2 (field axis2)
        | forwardBackwardNormSqExact axis3 (field axis3)
        | curlCrossTermEqualsDivergenceCrossTerm
            axis0 axis1 (field axis0) (field axis1)
        | curlCrossTermEqualsDivergenceCrossTerm
            axis0 axis2 (field axis0) (field axis2)
        | curlCrossTermEqualsDivergenceCrossTerm
            axis0 axis3 (field axis0) (field axis3)
        | curlCrossTermEqualsDivergenceCrossTerm
            axis1 axis2 (field axis1) (field axis2)
        | curlCrossTermEqualsDivergenceCrossTerm
            axis1 axis3 (field axis1) (field axis3)
        | curlCrossTermEqualsDivergenceCrossTerm
            axis2 axis3 (field axis2) (field axis3) =
  ℚRing.solve-∀
    (forwardDerivativeEnergy axis0 (field axis0))
    (forwardDerivativeEnergy axis1 (field axis0))
    (forwardDerivativeEnergy axis2 (field axis0))
    (forwardDerivativeEnergy axis3 (field axis0))
    (forwardDerivativeEnergy axis0 (field axis1))
    (forwardDerivativeEnergy axis1 (field axis1))
    (forwardDerivativeEnergy axis2 (field axis1))
    (forwardDerivativeEnergy axis3 (field axis1))
    (forwardDerivativeEnergy axis0 (field axis2))
    (forwardDerivativeEnergy axis1 (field axis2))
    (forwardDerivativeEnergy axis2 (field axis2))
    (forwardDerivativeEnergy axis3 (field axis2))
    (forwardDerivativeEnergy axis0 (field axis3))
    (forwardDerivativeEnergy axis1 (field axis3))
    (forwardDerivativeEnergy axis2 (field axis3))
    (forwardDerivativeEnergy axis3 (field axis3))
    (mixedBackwardEnergy axis0 axis1 (field axis0) (field axis1))
    (mixedBackwardEnergy axis0 axis2 (field axis0) (field axis2))
    (mixedBackwardEnergy axis0 axis3 (field axis0) (field axis3))
    (mixedBackwardEnergy axis1 axis2 (field axis1) (field axis2))
    (mixedBackwardEnergy axis1 axis3 (field axis1) (field axis3))
    (mixedBackwardEnergy axis2 axis3 (field axis2) (field axis3))

componentDiscreteCurlDivergenceHodgeIdentity : ∀ field →
  componentCurlEnergy field + componentDivergenceEnergy field
  ≡ componentPeriodicDifferenceEnergy field
componentDiscreteCurlDivergenceHodgeIdentity field =
  trans
    (cong₂ _+_
      (componentCurlEnergyExpansion field)
      (componentDivergenceEnergyExpansion field))
    (trans
      (fourAxisDiagonalOffDiagonalPartition field)
      (sym (componentPeriodicDifferenceEnergyExpansion field)))

configuredSide4PeriodicHodgeIdentityLevel : ProofLevel
configuredSide4PeriodicHodgeIdentityLevel = machineChecked
