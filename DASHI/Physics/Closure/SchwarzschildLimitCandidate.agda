module DASHI.Physics.Closure.SchwarzschildLimitCandidate where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Unit using (⊤; tt)

import DASHI.Physics.Closure.DiscreteConnectionCandidateFromCRT as DCRT
import DASHI.Physics.Closure.DiscreteEinsteinTensorCandidate as DET
import DASHI.Physics.Closure.GRNonFlatScalarAlgebraSurface as NF

------------------------------------------------------------------------
-- Schwarzschild-limit candidate surface.
--
-- The repository currently has a flat Minkowski receipt and diagnostic-only
-- CRT/non-flat connection surfaces.  This module therefore records the exact
-- carrier primitives needed before a Schwarzschild limit can be promoted.
-- It does not construct a non-flat metric, Birkhoff theorem, W4 source, or
-- standard GR derivation.

data SchwarzschildLimitCandidateStatus : Set where
  requestSurfaceOnlyNoPromotion :
    SchwarzschildLimitCandidateStatus

data SchwarzschildLimitFirstMissingPrimitive : Set where
  missingRadialValuation :
    SchwarzschildLimitFirstMissingPrimitive
  missingSphericalSymmetryPredicate :
    SchwarzschildLimitFirstMissingPrimitive
  missingW4MassSource :
    SchwarzschildLimitFirstMissingPrimitive
  missingBirkhoffCarrierProof :
    SchwarzschildLimitFirstMissingPrimitive
  missingWeakFieldNewtonianPotential :
    SchwarzschildLimitFirstMissingPrimitive
  missingSchwarzschildMetricMatch :
    SchwarzschildLimitFirstMissingPrimitive

data SchwarzschildLimitUnsupportedClaim : Set where
  unsupportedPromotedNonFlatGR :
    SchwarzschildLimitUnsupportedClaim
  unsupportedStandardSchwarzschildDerivation :
    SchwarzschildLimitUnsupportedClaim
  unsupportedCarrierBirkhoffTheorem :
    SchwarzschildLimitUnsupportedClaim
  unsupportedW4MatterSideClosure :
    SchwarzschildLimitUnsupportedClaim
  unsupportedWeakFieldLimitRecovery :
    SchwarzschildLimitUnsupportedClaim

record SchwarzschildLimitCarrierRequest
  (scalarOps : NF.GRCarrierScalarOperations) : Set₁ where
  open NF.GRCarrierScalarOperations scalarOps

  field
    Carrier :
      Set

    SchwarzschildMetricCarrier :
      Set

    radialValuation :
      Carrier →
      CarrierScalar

    sphericalSymmetryPredicate :
      Carrier →
      Set

    w4MassSource :
      Carrier →
      CarrierScalar

    birkhoffCarrierProof :
      (x : Carrier) →
      sphericalSymmetryPredicate x →
      Set

    weakFieldNewtonianPotential :
      Carrier →
      CarrierScalar

    schwarzschildMetricAt :
      Carrier →
      SchwarzschildMetricCarrier

    metricMatch :
      (x : Carrier) →
      (symmetry : sphericalSymmetryPredicate x) →
      birkhoffCarrierProof x symmetry →
      Set

    requestBoundary :
      List String

record SchwarzschildLimitCandidateDiagnostic : Set₁ where
  field
    status :
      SchwarzschildLimitCandidateStatus

    scalarSurface :
      NF.GRCarrierScalarOperations

    flatEinsteinTensorDiagnostic :
      DET.DiscreteEinsteinTensorCandidateDiagnostic

    connectionFromCRTDiagnostic :
      DCRT.DiscreteConnectionCandidateFromCRTDiagnostic

    firstMissing :
      SchwarzschildLimitFirstMissingPrimitive

    exactMissingPrimitives :
      List SchwarzschildLimitFirstMissingPrimitive

    landedSurface :
      List String

    missingSurface :
      List String

    unsupportedClaims :
      List SchwarzschildLimitUnsupportedClaim

    noPromotionBoundary :
      List String

    nextAdmissibleReceipt :
      String

canonicalSchwarzschildLimitCandidateDiagnostic :
  SchwarzschildLimitCandidateDiagnostic
canonicalSchwarzschildLimitCandidateDiagnostic =
  record
    { status =
        requestSurfaceOnlyNoPromotion
    ; scalarSurface =
        NF.canonicalGRFiniteRCarrierScalarOperations
    ; flatEinsteinTensorDiagnostic =
        DET.canonicalDiscreteEinsteinTensorCandidateDiagnostic
    ; connectionFromCRTDiagnostic =
        DCRT.canonicalDiscreteConnectionCandidateFromCRTDiagnostic
    ; firstMissing =
        missingRadialValuation
    ; exactMissingPrimitives =
        missingRadialValuation
        ∷ missingSphericalSymmetryPredicate
        ∷ missingW4MassSource
        ∷ missingBirkhoffCarrierProof
        ∷ missingWeakFieldNewtonianPotential
        ∷ missingSchwarzschildMetricMatch
        ∷ []
    ; landedSurface =
        "Flat Minkowski quadratic receipt"
        ∷ "Discrete Einstein tensor diagnostic surface"
        ∷ "CRT-derived connection diagnostic with no non-flat connection promotion"
        ∷ "Finite-r carrier scalar operation surface"
        ∷ []
    ; missingSurface =
        "radialValuation : Carrier -> CarrierScalar"
        ∷ "sphericalSymmetryPredicate : Carrier -> Set"
        ∷ "w4MassSource : Carrier -> CarrierScalar"
        ∷ "birkhoffCarrierProof : (x : Carrier) -> sphericalSymmetryPredicate x -> Set"
        ∷ "weakFieldNewtonianPotential : Carrier -> CarrierScalar"
        ∷ "metricMatch : (x : Carrier) -> (symmetry : sphericalSymmetryPredicate x) -> birkhoffCarrierProof x symmetry -> Set"
        ∷ []
    ; unsupportedClaims =
        unsupportedPromotedNonFlatGR
        ∷ unsupportedStandardSchwarzschildDerivation
        ∷ unsupportedCarrierBirkhoffTheorem
        ∷ unsupportedW4MatterSideClosure
        ∷ unsupportedWeakFieldLimitRecovery
        ∷ []
    ; noPromotionBoundary =
        "This module is a Schwarzschild-limit candidate/request surface only"
        ∷ "No GR non-flat promotion is introduced here"
        ∷ "No standard Schwarzschild derivation is imported or claimed"
        ∷ "No W4 matter-side mass source is constructed here"
        ∷ "No Birkhoff theorem is constructed for the carrier"
        ∷ "No weak-field Newtonian limit or metric match theorem is constructed here"
        ∷ []
    ; nextAdmissibleReceipt =
        "SchwarzschildLimitCarrierRequest with radial valuation, spherical symmetry, W4 mass source, carrier Birkhoff proof, weak-field Newtonian potential, and metric match"
    }

schwarzschildLimitExactFirstMissing :
  SchwarzschildLimitCandidateDiagnostic.firstMissing
    canonicalSchwarzschildLimitCandidateDiagnostic
  ≡
  missingRadialValuation
schwarzschildLimitExactFirstMissing = refl

schwarzschildLimitStatusIsRequestOnly :
  SchwarzschildLimitCandidateDiagnostic.status
    canonicalSchwarzschildLimitCandidateDiagnostic
  ≡
  requestSurfaceOnlyNoPromotion
schwarzschildLimitStatusIsRequestOnly = refl

------------------------------------------------------------------------
-- Concrete bounded radial valuation / weak-field adapter.
--
-- This is intentionally weaker than SchwarzschildLimitCarrierRequest.  It
-- supplies a checked finite radial shell carrier, a positive rational radius
-- tag for each shell, a finite-residue radial valuation, and the first-order
-- weak-field lapse table g_tt = 1 - 2 phi.  The "Schwarzschild" side below is
-- only the same linear weak-field lapse shape over the same table, so the
-- match is definitional.  It does not construct a vacuum exterior metric,
-- Birkhoff theorem, W4 source, Ricci-zero theorem, or full metric match.

data RationalRadialShell : Set where
  shell-r2 :
    RationalRadialShell
  shell-r4 :
    RationalRadialShell
  shell-r8 :
    RationalRadialShell

record PositiveRationalRadiusTag : Set where
  constructor positiveRationalRadius
  field
    numerator :
      Nat

    denominatorMinusOne :
      Nat

positiveRationalRadiusDenominator :
  PositiveRationalRadiusTag →
  Nat
positiveRationalRadiusDenominator tag =
  suc (PositiveRationalRadiusTag.denominatorMinusOne tag)

oneN twoN fourN eightN : Nat
oneN = suc zero
twoN = suc oneN
fourN = suc (suc twoN)
eightN = suc (suc (suc (suc fourN)))

rationalShellRadius :
  RationalRadialShell →
  PositiveRationalRadiusTag
rationalShellRadius shell-r2 =
  positiveRationalRadius twoN zero
rationalShellRadius shell-r4 =
  positiveRationalRadius fourN zero
rationalShellRadius shell-r8 =
  positiveRationalRadius eightN zero

rationalShellRadiusDenominatorIsOne :
  (shell : RationalRadialShell) →
  positiveRationalRadiusDenominator (rationalShellRadius shell)
  ≡
  oneN
rationalShellRadiusDenominatorIsOne shell-r2 = refl
rationalShellRadiusDenominatorIsOne shell-r4 = refl
rationalShellRadiusDenominatorIsOne shell-r8 = refl

rationalShellRadialValuation :
  RationalRadialShell →
  NF.GRFiniteRScalar
rationalShellRadialValuation shell-r2 =
  NF.r2
rationalShellRadialValuation shell-r4 =
  NF.r0
rationalShellRadialValuation shell-r8 =
  NF.r0

rationalShellSphericalSymmetry :
  RationalRadialShell →
  Set
rationalShellSphericalSymmetry _ =
  ⊤

rationalShellSymmetryWitness :
  (shell : RationalRadialShell) →
  rationalShellSphericalSymmetry shell
rationalShellSymmetryWitness _ =
  tt

rationalShellMassResidue :
  RationalRadialShell →
  NF.GRFiniteRScalar
rationalShellMassResidue _ =
  NF.r1

rationalShellWeakFieldPotentialResidue :
  RationalRadialShell →
  NF.GRFiniteRScalar
rationalShellWeakFieldPotentialResidue shell-r2 =
  NF.r2
rationalShellWeakFieldPotentialResidue shell-r4 =
  NF.r1
rationalShellWeakFieldPotentialResidue shell-r8 =
  NF.r3

weakFieldLinearLapseResidue :
  RationalRadialShell →
  NF.GRFiniteRScalar
weakFieldLinearLapseResidue shell =
  NF.grFiniteRScalarSub
    NF.r1
    (NF.grFiniteRScalarMul
      NF.r2
      (rationalShellWeakFieldPotentialResidue shell))

schwarzschildLinearLapseResidue :
  RationalRadialShell →
  NF.GRFiniteRScalar
schwarzschildLinearLapseResidue shell =
  NF.grFiniteRScalarSub
    NF.r1
    (NF.grFiniteRScalarMul
      NF.r2
      (rationalShellWeakFieldPotentialResidue shell))

rationalShellWeakFieldLapseMatchesSchwarzschildLinearLapse :
  (shell : RationalRadialShell) →
  weakFieldLinearLapseResidue shell
  ≡
  schwarzschildLinearLapseResidue shell
rationalShellWeakFieldLapseMatchesSchwarzschildLinearLapse _ =
  refl

weakFieldLinearLapseAtR2IsR1 :
  weakFieldLinearLapseResidue shell-r2
  ≡
  NF.r1
weakFieldLinearLapseAtR2IsR1 =
  refl

weakFieldLinearLapseAtR4IsR3 :
  weakFieldLinearLapseResidue shell-r4
  ≡
  NF.r3
weakFieldLinearLapseAtR4IsR3 =
  refl

weakFieldLinearLapseAtR8IsR3 :
  weakFieldLinearLapseResidue shell-r8
  ≡
  NF.r3
weakFieldLinearLapseAtR8IsR3 =
  refl

record RationalShellWeakFieldMatchAdapter : Set₁ where
  field
    scalarSurface :
      NF.GRCarrierScalarOperations

    scalarSurfaceIsCanonicalFiniteR :
      scalarSurface
      ≡
      NF.canonicalGRFiniteRCarrierScalarOperations

    Carrier :
      Set

    radiusTag :
      Carrier →
      PositiveRationalRadiusTag

    radiusDenominatorNonZeroByConstruction :
      (x : Carrier) →
      positiveRationalRadiusDenominator (radiusTag x)
      ≡
      oneN

    radialValuation :
      Carrier →
      NF.GRFiniteRScalar

    sphericalSymmetryPredicate :
      Carrier →
      Set

    sphericalSymmetryWitness :
      (x : Carrier) →
      sphericalSymmetryPredicate x

    finiteMassParameter :
      Carrier →
      NF.GRFiniteRScalar

    weakFieldNewtonianPotential :
      Carrier →
      NF.GRFiniteRScalar

    weakFieldLapse :
      Carrier →
      NF.GRFiniteRScalar

    schwarzschildLinearLapse :
      Carrier →
      NF.GRFiniteRScalar

    weakFieldMetricMatch :
      (x : Carrier) →
      weakFieldLapse x
      ≡
      schwarzschildLinearLapse x

    allLaneEinsteinZeroTableLaw :
      DET.FactorVecSSPAllLaneContractionEinsteinTensorLaw

    landedSurface :
      List String

    missingForVacuumPromotion :
      List SchwarzschildLimitFirstMissingPrimitive

    firstMissingAfterAdapter :
      SchwarzschildLimitFirstMissingPrimitive

    vacuumPromotion :
      Bool

    vacuumPromotionIsFalse :
      vacuumPromotion ≡ false

canonicalRationalShellWeakFieldMatchAdapter :
  RationalShellWeakFieldMatchAdapter
canonicalRationalShellWeakFieldMatchAdapter =
  record
    { scalarSurface =
        NF.canonicalGRFiniteRCarrierScalarOperations
    ; scalarSurfaceIsCanonicalFiniteR =
        refl
    ; Carrier =
        RationalRadialShell
    ; radiusTag =
        rationalShellRadius
    ; radiusDenominatorNonZeroByConstruction =
        rationalShellRadiusDenominatorIsOne
    ; radialValuation =
        rationalShellRadialValuation
    ; sphericalSymmetryPredicate =
        rationalShellSphericalSymmetry
    ; sphericalSymmetryWitness =
        rationalShellSymmetryWitness
    ; finiteMassParameter =
        rationalShellMassResidue
    ; weakFieldNewtonianPotential =
        rationalShellWeakFieldPotentialResidue
    ; weakFieldLapse =
        weakFieldLinearLapseResidue
    ; schwarzschildLinearLapse =
        schwarzschildLinearLapseResidue
    ; weakFieldMetricMatch =
        rationalShellWeakFieldLapseMatchesSchwarzschildLinearLapse
    ; allLaneEinsteinZeroTableLaw =
        DET.canonicalFactorVecSSPAllLaneContractionEinsteinTensorLaw
    ; landedSurface =
        "RationalRadialShell has concrete positive rational radius tags 2/1, 4/1, and 8/1"
        ∷ "radialValuation is a total finite-residue table into GRFiniteRScalar"
        ∷ "sphericalSymmetryPredicate is inhabited on every bounded shell"
        ∷ "weakFieldNewtonianPotential and g_tt = 1 - 2 phi are concrete finite-residue tables"
        ∷ "weakFieldMetricMatch proves equality with the same Schwarzschild-linear lapse adapter by refl"
        ∷ "The existing all-lane Einstein zero-table law is consumed only as a flat local finite algebra receipt"
        ∷ []
    ; missingForVacuumPromotion =
        missingSchwarzschildMetricMatch
        ∷ missingBirkhoffCarrierProof
        ∷ missingW4MassSource
        ∷ []
    ; firstMissingAfterAdapter =
        missingSchwarzschildMetricMatch
    ; vacuumPromotion =
        false
    ; vacuumPromotionIsFalse =
        refl
    }

rationalShellWeakFieldAdapterFirstMissingMetricMatch :
  RationalShellWeakFieldMatchAdapter.firstMissingAfterAdapter
    canonicalRationalShellWeakFieldMatchAdapter
  ≡
  missingSchwarzschildMetricMatch
rationalShellWeakFieldAdapterFirstMissingMetricMatch =
  refl

rationalShellWeakFieldAdapterNoVacuumPromotion :
  RationalShellWeakFieldMatchAdapter.vacuumPromotion
    canonicalRationalShellWeakFieldMatchAdapter
  ≡
  false
rationalShellWeakFieldAdapterNoVacuumPromotion =
  refl
