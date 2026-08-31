module DASHI.Physics.Closure.NSTriadKNSixteenCellKnownGainDiagnosticRound317Exact where

------------------------------------------------------------------------
-- ROUND317 / SYMBOLIC SIXTEEN-CELL KNOWN-GAIN DIAGNOSTIC
--
-- R315 fixes the exact missing squared dyadic gain after heat for each oriented
-- outer critical region.  R316 refines the inner route enough to distinguish
-- the only two currently-owned candidate gain mechanisms:
--
--   homochiral radial-near:
--     a certified amplitude gain delta_radial, hence squared gain 2 delta;
--
--   heterochiral HH->low:
--     R312 relocates one derivative from inner high shell m to inner output p,
--     hence squared gain 2 (m-j_p).
--
-- The other two inner routes receive ZERO automatic gain from the currently
-- owned inner commutator geometry.  This is not a no-go theorem for those
-- routes; it is a least-privilege statement about what has actually been
-- proved so far.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (_∷_; [])
import Data.Rational.Base as ℚ
open ℚ using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNNestedCriticalGainConsumerRound315Exact as R315
import DASHI.Physics.Closure.NSTriadKNNestedInnerGeometryRefinementRound316Exact as R316

one two : ℚ
one = 1ℚ
two = one + one

record KnownGainParameters : Set where
  constructor known-gain-parameters
  field
    shells : R315.OrientedOuterShells
    radialNearAmplitudeGain : ℚ
    innerHHHighShell : ℚ

open KnownGainParameters public

knownSquaredGain : R316.RefinedInnerRoute → KnownGainParameters → ℚ
knownSquaredGain R316.homochiralRadialNear P =
  two * radialNearAmplitudeGain P
knownSquaredGain R316.homochiralRadialSeparated P = 0ℚ
knownSquaredGain R316.heterochiralHHToLow P =
  two * (innerHHHighShell P - R315.pShell (shells P))
knownSquaredGain R316.heterochiralNonHH P = 0ℚ

residualAfterKnownGain :
  R316.RefinedNestedRoute → KnownGainParameters → ℚ
residualAfterKnownGain route P =
  R315.missingSquaredGain (R316.outerRegion route) (shells P)
  - knownSquaredGain (R316.innerRoute route) P

-- The sixteen-cell table is obtained by composition with R316.indexRoute.  No
-- branch gets a stronger mechanism merely because another branch has one.
cellResidual : R316.SixteenCellIndex → KnownGainParameters → ℚ
cellResidual cell P = residualAfterKnownGain (R316.indexRoute cell) P

-- Regression formulas for the two nontrivial mechanisms.
nearGainIsTwiceAmplitudeGain :
  (P : KnownGainParameters) →
  knownSquaredGain R316.homochiralRadialNear P
  ≡ two * radialNearAmplitudeGain P
nearGainIsTwiceAmplitudeGain P = refl

heterochiralHHGainIsDerivativeRelocation :
  (P : KnownGainParameters) →
  knownSquaredGain R316.heterochiralHHToLow P
  ≡ two * (innerHHHighShell P - R315.pShell (shells P))
heterochiralHHGainIsDerivativeRelocation P = refl

separatedHomochiralHasNoAutomaticKnownGain :
  (P : KnownGainParameters) →
  knownSquaredGain R316.homochiralRadialSeparated P ≡ 0ℚ
separatedHomochiralHasNoAutomaticKnownGain P = refl

heterochiralNonHHHasNoAutomaticKnownGain :
  (P : KnownGainParameters) →
  knownSquaredGain R316.heterochiralNonHH P ≡ 0ℚ
heterochiralNonHHHasNoAutomaticKnownGain P = refl

-- Example symbolic formulas showing how the same inner mechanism faces a
-- different backward residual depending on which outer leg carries N_p.
nearForcingLowResidual :
  (P : KnownGainParameters) →
  cellResidual R316.nearLow P
  ≡ (R315.missingSquaredGain
        DASHI.Physics.Closure.NSTriadKNNestedOuterOrientationRefinementRound314Exact.forcingLowFLShoulder
        (shells P))
      - two * radialNearAmplitudeGain P
nearForcingLowResidual P = refl

nearForcingHighResidual :
  (P : KnownGainParameters) →
  cellResidual R316.nearHigh P
  ≡ (R315.missingSquaredGain
        DASHI.Physics.Closure.NSTriadKNNestedOuterOrientationRefinementRound314Exact.forcingHighHLShoulder
        (shells P))
      - two * radialNearAmplitudeGain P
nearForcingHighResidual P = refl

round317SixteenCellSymbolicResidualsComputed : Bool
round317SixteenCellSymbolicResidualsComputed = true

round317NearHomochiralGainKeptConditionalOnRadialCertificate : Bool
round317NearHomochiralGainKeptConditionalOnRadialCertificate = true

round317HeterochiralHHGainUsesOnlyR312Relocation : Bool
round317HeterochiralHHGainUsesOnlyR312Relocation = true

round317SeparatedOrNonHHAutomaticGainInvented : Bool
round317SeparatedOrNonHHAutomaticGainInvented = false

round317AnySixteenCellPhysicalSchurEstimateClosed : Bool
round317AnySixteenCellPhysicalSchurEstimateClosed = false

round317PackageAClosed : Bool
round317PackageAClosed = false

round317ClayPromotion : Bool
round317ClayPromotion = false

round317PackageAClosedIsFalse : round317PackageAClosed ≡ false
round317PackageAClosedIsFalse = refl
