module DASHI.Biology.IITFiveCubeJCoarseFineRelativeBridgeExact where

open import DASHI.Core.Prelude
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import DASHI.Core.CoarseFineRelativeFibreExact as Fibre
import DASHI.Core.CoarseFineDepthDecompositionExact as Depth
import DASHI.Biology.JFineCoarseRelativeScaleExact as JScale
import DASHI.Foundations.JPlusOneScaleBridge as JPlusOne

------------------------------------------------------------------------
-- Exact algebraic transport of the 5^3 F3 lattice decomposition.
--
-- Original numerical owner:
--   scripts/iit_ternary_lattice_scaling.py (periodic 3D x+y+z)
-- New finite same-law audit:
--   scripts/iit_j_coarse_fine_5cube_audit.py
--
-- On 5^3 sites, F has rank 120 and kernel dimension 5.
-- Explicit j(g)(i,j,k) = g(i+j+k mod 5) is the five-slot null section;
-- P(x)(s) sums over 25 sites of fixed i+j+k=s mod 5.
-- The local exact integer/field certificate is
--   Pj=id, Fj=0, PF=0, F^80=id-jP.
--
-- Those source-specific polynomial/125-column receipts are NUMERICAL
-- FINITE-ARITHMETIC evidence until encoded in Agda. This module proves the
-- conditional *coarse/relative-fine reopening theorem* from a supplied
-- algebraic receipt, rather than fabricating a kernel inhabitant for the
-- concrete 125-site matrix.
--
-- Crucial distinction from repo's harmonic JCoarse (9 channels) and JFine
-- (3^9 states): the 5-dimensional profile is a DIFFERENT carrier. '+1'
-- means one independent 5-slot cyclic profile, not a 4th spatial dimension,
-- not an additional scalar, and not 5^3 + 5 independent source dimensions.
------------------------------------------------------------------------

record DiagonalCoarseFiveSplit (V G : Set) : Set₁ where
  constructor diagonal-coarse-five-split
  field
    transition : V → V
    projectedLostProfile : V → G
    embedLostProfile : G → V
    inverseOnRetainedOutput : V → V
    join : V → V → V
    negate : V → V

    -- In the source lattice inverseOnRetainedOutput = F^79, so its
    -- composite with F is the retained projector F^80 = id-jP.
    retainedProjectionEquation :
      (x : V) →
      inverseOnRetainedOutput (transition x)
      ≡ join x (negate (embedLostProfile (projectedLostProfile x)))

    subtractThenRestore :
      (x y : V) → join (join x (negate y)) y ≡ x

open DiagonalCoarseFiveSplit public

exactReopenFromPowerCertificate :
  ∀ {V G} →
  (witness : DiagonalCoarseFiveSplit V G) →
  (x : V) →
  join witness
    (inverseOnRetainedOutput witness (transition witness x))
    (embedLostProfile witness (projectedLostProfile witness x))
  ≡ x
exactReopenFromPowerCertificate witness x =
  trans
    (cong
      (λ retained →
        join witness retained
          (embedLostProfile witness (projectedLostProfile witness x)))
      (retainedProjectionEquation witness x))
    (subtractThenRestore witness x
      (embedLostProfile witness (projectedLostProfile witness x)))

relativeReopening :
  ∀ {V G} →
  DiagonalCoarseFiveSplit V G →
  Fibre.CoarseFineReopening V
relativeReopening {V} {G} witness =
  Fibre.coarseFineReopening
    V G
    (transition witness)
    (projectedLostProfile witness)
    (λ coarse residual →
      join witness
        (inverseOnRetainedOutput witness coarse)
        (embedLostProfile witness residual))
    (exactReopenFromPowerCertificate witness)

-- Two relative-fibre presentations exist for the SAME pair of measurements.
-- For geometric coarse-first semantics choose the five-slot P profile
-- as coarse and the 120-dimensional F image as relative fine. The earlier
-- presentation instead chooses the dynamic F observation as coarse and P
-- as its missing relative residual. Neither is absolute without a consumer.

diagonalCoarseFirstReopening :
  ∀ {V G} →
  DiagonalCoarseFiveSplit V G →
  Fibre.CoarseFineReopening V
diagonalCoarseFirstReopening {V} {G} witness =
  Fibre.coarseFineReopening
    G V
    (projectedLostProfile witness)
    (transition witness)
    (λ diagonalCoarse retainedFine →
      join witness
        (inverseOnRetainedOutput witness retainedFine)
        (embedLostProfile witness diagonalCoarse))
    (exactReopenFromPowerCertificate witness)

retainedPlusLostDimension : Depth.CoarseFineDecomposition
retainedPlusLostDimension =
  Depth.coarse-fine-decomposition 120 5 125 refl

-- A single new *profile packet* has width five; it is not one scalar
-- coordinate, and not the literal +1 arithmetic in the stage/McKay lanes.
oneFiveSlotPacketReconstruction : 120 + 1 * 5 ≡ 125
oneFiveSlotPacketReconstruction = refl

oneFreshCoarseProfileShape : JPlusOne.FreshUnitExtension
oneFreshCoarseProfileShape = record
  { carrierValue = 120
  ; freshValue = 5
  ; joinedValue = 125
  ; joinExact = refl
  ; interpretation =
      "One extra relative profile packet of five trits completes 120 retained dimensions to 125; no fourth spatial axis or J harmonic carrier identity"
  }

sourceDimensionsReconstruct :
  Depth.absoluteComponent retainedPlusLostDimension
  ≡ Depth.coarseComponent retainedPlusLostDimension
      + Depth.relativeFineComponent retainedPlusLostDimension
sourceDimensionsReconstruct =
  Depth.reconstruction retainedPlusLostDimension

oldHarmonicJCoarseIsNine : JScale.jCoarseFrequency ≡ 9
oldHarmonicJCoarseIsNine = refl

oldHarmonicJFineIs19683 : JScale.jFineFrequency ≡ 19683
oldHarmonicJFineIs19683 = refl

fiveSlotProfileNotOldJCoarseNine : 5 ≡ JScale.jCoarseFrequency → ⊥
fiveSlotProfileNotOldJCoarseNine ()

------------------------------------------------------------------------
-- A coarse observation that is F(x) cannot serve consumers that need
-- P(x), unless they retain the relative fine residue. This is a direct
-- reuse of the existing consumer-fibre nonfactorability theorem.
------------------------------------------------------------------------

record ProfileSeparatingPair
    {V G : Set}
    (witness : DiagonalCoarseFiveSplit V G) : Set where
  constructor profile-separating-pair
  field
    x y : V
    sameTransition : transition witness x ≡ transition witness y
    differentProfile :
      projectedLostProfile witness x
      ≡ projectedLostProfile witness y → ⊥
open ProfileSeparatingPair public

profileSensitiveConsumer :
  ∀ {V G} (witness : DiagonalCoarseFiveSplit V G) →
  ProfileSeparatingPair witness →
  Fibre.FineSensitiveConsumer
    (relativeReopening witness)
    (projectedLostProfile witness)
profileSensitiveConsumer witness pair =
  Fibre.fineSensitiveConsumer
    (x pair)
    (y pair)
    (sameTransition pair)
    (differentProfile pair)
    "The transition image collides but the missing diagonal profile differs"

record FiveCubeInterpretationBoundary : Set where
  constructor five-cube-interpretation-boundary
  field
    exactGenericReopeningPaid : Bool
    additive120Plus5Is125 : Bool
    oldNineAnd19683JRolesSeparated : Bool
    concrete125SiteAgdaCertificatePresent : Bool
    newFourthGeometricAxisEstablished : Bool
    IITPhiOrConsciousnessEstablished : Bool

canonicalFiveCubeInterpretationBoundary : FiveCubeInterpretationBoundary
canonicalFiveCubeInterpretationBoundary =
  five-cube-interpretation-boundary true true true false false false
