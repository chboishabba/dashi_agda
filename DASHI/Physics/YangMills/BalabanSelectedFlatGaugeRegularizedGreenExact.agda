module DASHI.Physics.YangMills.BalabanSelectedFlatGaugeRegularizedGreenExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Construct a literal two-sided Green inverse for the identity-background
-- gauge multiplier Gram after adding only the three global constant-mode
-- projectors.  The raw flat Gram is
--
--        K_0 = L_gauge,0 L_gauge,0^* = -Delta_periodic
--
-- componentwise.  Adding the global mean projector gives exactly the already
-- machine-checked configured scalar operator
--
--        K_0^reg = -Delta_periodic + P_const.
--
-- The repository already contains its explicit 256-site Fourier Green kernel.
-- This module proves that the *actual selected gauge matrix* reduces to that
-- scalar operator and transports the scalar Green left/right inverse to all
-- three su(2) multiplier components.  No inverse is supplied as an axiom and
-- no matrix rank theorem is used.
--
-- This is a regularized flat reference operator.  It is not asserted to be the
-- Moore--Penrose inverse of the raw background-dependent Gram away from the
-- identity; the holonomy guard shows why that identification would be unsafe.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicVectorCalculusExact as Vec
import DASHI.Physics.YangMills.BalabanPath4SU2ConfiguredScalarReductionExact as Scalar
import DASHI.Physics.YangMills.BalabanSide4ScalarGreenConvolutionExact as Green
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatGaugeDivergenceIdentificationExact as FlatGauge
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeAdjointGramFloorExact as FlatAdjoint

GaugeMultiplier : Set
GaugeMultiplier = FlatAdjoint.GaugeMultiplier

------------------------------------------------------------------------
-- The actual flat Gram is the scalar periodic Laplacian componentwise.
------------------------------------------------------------------------

flatGaugeGramApply : GaugeMultiplier → GaugeMultiplier
flatGaugeGramApply multiplier =
  FlatAdjoint.identityGaugeConstraintApply
    (FlatAdjoint.actualFlatGaugeAdjoint multiplier)

negativeGradientDivergenceIsLocalLaplacian : ∀ gauge site →
  Vec.literalPeriodicDivergenceScalar
    (Vec.literalNegativeForwardGradientScalar gauge) site
  ≡ Scalar.siteLocalLaplacian gauge site
negativeGradientDivergenceIsLocalLaplacian gauge site =
  Sums.sumRationalCong
    (DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier.allCyclicIndices
      DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier.four)
    (λ axis →
      Vec.backwardDifference4 axis
        (Vec.literalNegativeForwardGradientScalar gauge axis) site)
    (λ axis →
      (gauge site + gauge site)
      - (gauge (Vec.shiftForward4 axis site)
        + gauge (Vec.shiftBackward4 axis site)))
    (λ axis →
      trans
        (ℚRing.solve-∀
          (Vec.backwardDifference4 axis
            (Vec.forwardDifference4 axis gauge) site))
        (trans
          (cong -_
            (Vec.backwardForwardDifferenceCommutes axis axis gauge site))
          (Scalar.negativeForwardBackwardStencil axis gauge site)))

flatGaugeGramApplyExact : ∀ multiplier coordinate site →
  flatGaugeGramApply multiplier (pair coordinate site)
  ≡ Scalar.siteLocalLaplacian
      (FlatAdjoint.multiplierField multiplier coordinate) site
flatGaugeGramApplyExact multiplier coordinate site =
  let
    state = FlatAdjoint.actualFlatGaugeAdjoint multiplier
    decoded = Coordinates.decodePhysicalSU2 state
    gauge = FlatAdjoint.multiplierField multiplier coordinate

    decodedFieldToNegativeGradient : ∀ axis current →
      decoded coordinate (pair axis current)
      ≡ Vec.literalNegativeForwardGradientScalar gauge axis current
    decodedFieldToNegativeGradient axis current =
      FlatAdjoint.actualFlatGaugeAdjointPointwiseExact multiplier
        (pair coordinate (pair axis current))

    divergenceCong :
      Vec.literalPeriodicDivergenceScalar
        (λ axis current → decoded coordinate (pair axis current)) site
      ≡ Vec.literalPeriodicDivergenceScalar
        (Vec.literalNegativeForwardGradientScalar gauge) site
    divergenceCong =
      Sums.sumRationalCong
        (DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier.allCyclicIndices
          DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier.four)
        (λ axis →
          Vec.backwardDifference4 axis
            (λ current → decoded coordinate (pair axis current)) site)
        (λ axis →
          Vec.backwardDifference4 axis
            (Vec.literalNegativeForwardGradientScalar gauge axis) site)
        (λ axis →
          ℚRing.solve-∀
            (decoded coordinate (pair axis site))
            (decoded coordinate
              (pair axis (Vec.shiftBackward4 axis site)))
            (Vec.literalNegativeForwardGradientScalar gauge axis site)
            (Vec.literalNegativeForwardGradientScalar gauge axis
              (Vec.shiftBackward4 axis site)))
  in
  trans
    (FlatAdjoint.identityGaugeConstraintApplyExact state coordinate site)
    (trans divergenceCong
      (negativeGradientDivergenceIsLocalLaplacian gauge site))

------------------------------------------------------------------------
-- Add exactly the constant-mode projection used by the configured scalar Green.
------------------------------------------------------------------------

flatGaugeMeanProjector : GaugeMultiplier → GaugeMultiplier
flatGaugeMeanProjector multiplier (pair coordinate site) =
  DASHI.Physics.YangMills.BalabanPath4AxisAverageExact.average0123
    (FlatAdjoint.multiplierField multiplier coordinate) site

regularizedFlatGaugeGramApply : GaugeMultiplier → GaugeMultiplier
regularizedFlatGaugeGramApply multiplier row =
  flatGaugeGramApply multiplier row + flatGaugeMeanProjector multiplier row

regularizedFlatGaugeGramIsConfiguredSiteOperator : ∀ multiplier coordinate site →
  regularizedFlatGaugeGramApply multiplier (pair coordinate site)
  ≡ Green.configuredSiteOperator
      (FlatAdjoint.multiplierField multiplier coordinate) site
regularizedFlatGaugeGramIsConfiguredSiteOperator multiplier coordinate site =
  cong
    (_+ DASHI.Physics.YangMills.BalabanPath4AxisAverageExact.average0123
      (FlatAdjoint.multiplierField multiplier coordinate) site)
    (flatGaugeGramApplyExact multiplier coordinate site)

------------------------------------------------------------------------
-- Exact componentwise Green inverse.
------------------------------------------------------------------------

regularizedFlatGaugeGreen : GaugeMultiplier → GaugeMultiplier
regularizedFlatGaugeGreen source (pair coordinate site) =
  Green.scalarGreen
    (FlatAdjoint.multiplierField source coordinate) site

regularizedFlatGaugeGreenRightInverse : ∀ source coordinate site →
  regularizedFlatGaugeGramApply
    (regularizedFlatGaugeGreen source) (pair coordinate site)
  ≡ source (pair coordinate site)
regularizedFlatGaugeGreenRightInverse source coordinate site =
  trans
    (regularizedFlatGaugeGramIsConfiguredSiteOperator
      (regularizedFlatGaugeGreen source) coordinate site)
    (Green.configuredSiteGreenRightInverse
      (FlatAdjoint.multiplierField source coordinate) site)

regularizedFlatGaugeGreenLeftInverse : ∀ source coordinate site →
  regularizedFlatGaugeGreen
    (regularizedFlatGaugeGramApply source) (pair coordinate site)
  ≡ source (pair coordinate site)
regularizedFlatGaugeGreenLeftInverse source coordinate site =
  let
    gauge = FlatAdjoint.multiplierField source coordinate

    sourcePointwise : ∀ current →
      FlatAdjoint.multiplierField
        (regularizedFlatGaugeGramApply source) coordinate current
      ≡ Green.configuredSiteOperator gauge current
    sourcePointwise current =
      regularizedFlatGaugeGramIsConfiguredSiteOperator source coordinate current
  in
  trans
    (Green.scalarGreenRespectsPointwise sourcePointwise site)
    (Green.configuredSiteGreenLeftInverse gauge site)

record RegularizedFlatGaugeGreenCertificate : Set where
  field
    operator : GaugeMultiplier → GaugeMultiplier
    green : GaugeMultiplier → GaugeMultiplier
    inverseLeftPointwise : ∀ source coordinate site →
      green (operator source) (pair coordinate site)
      ≡ source (pair coordinate site)
    inverseRightPointwise : ∀ source coordinate site →
      operator (green source) (pair coordinate site)
      ≡ source (pair coordinate site)
open RegularizedFlatGaugeGreenCertificate public

regularizedFlatGaugeGreenCertificate : RegularizedFlatGaugeGreenCertificate
regularizedFlatGaugeGreenCertificate = record
  { operator = regularizedFlatGaugeGramApply
  ; green = regularizedFlatGaugeGreen
  ; inverseLeftPointwise = regularizedFlatGaugeGreenLeftInverse
  ; inverseRightPointwise = regularizedFlatGaugeGreenRightInverse
  }

selectedFlatGaugeRegularizedGramIdentificationLevel : ProofLevel
selectedFlatGaugeRegularizedGramIdentificationLevel = machineChecked

selectedFlatGaugeRegularizedGreenLevel : ProofLevel
selectedFlatGaugeRegularizedGreenLevel = machineChecked
