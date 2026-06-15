module DASHI.Physics.Closure.SchwarzschildLimitCandidate where

open import Agda.Primitive using (Setω)
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

------------------------------------------------------------------------
-- Concrete r_s = 2, r = 3 analytic table lane.
--
-- This is a pointwise analytic table over ordinary signed rational tags.
-- It deliberately does not promote the finite-residue scalar carrier to an
-- ordered real/rational field, and it does not construct a Levi-Civita
-- connection theorem.  The entries below record the doubled Christoffel
-- values 2 * Gamma^i_jk at the Schwarzschild point r_s = 2, r = 3, with
-- angular sin(theta)^2 normalized to one for the phi-phi row.

data SchwarzschildCoordinateIndex : Set where
  coord-t :
    SchwarzschildCoordinateIndex
  coord-r :
    SchwarzschildCoordinateIndex
  coord-theta :
    SchwarzschildCoordinateIndex
  coord-phi :
    SchwarzschildCoordinateIndex

data SignedRationalSign : Set where
  sign+ :
    SignedRationalSign
  sign- :
    SignedRationalSign

record SignedPositiveRationalTag : Set where
  constructor signedPositiveRational
  field
    sign :
      SignedRationalSign

    numerator :
      Nat

    denominatorMinusOne :
      Nat

signedRationalDenominator :
  SignedPositiveRationalTag →
  Nat
signedRationalDenominator q =
  suc (SignedPositiveRationalTag.denominatorMinusOne q)

suc3 :
  Nat →
  Nat
suc3 n =
  suc (suc (suc n))

suc9 :
  Nat →
  Nat
suc9 n =
  suc3 (suc3 (suc3 n))

threeN sixN nineN twentySixN : Nat
threeN =
  suc twoN

sixN =
  suc (suc fourN)

nineN =
  suc eightN

twentySixN =
  suc9 (suc9 eightN)

zeroQ posOne posOneThird posOneNinth posOneTwentySeventh posTwo posTwoThirds posTwoNinths posTwoTwentySevenths posFour posFourNinths posFourTwentySevenths posThree posSix posNine negOne negOneThird negOneNinth negTwoThirds negTwo negTwoNinths negTwoTwentySevenths negThree negFour negFourNinths negFourTwentySevenths negSix : SignedPositiveRationalTag
zeroQ =
  signedPositiveRational sign+ zero zero

posOne =
  signedPositiveRational sign+ oneN zero

posOneThird =
  signedPositiveRational sign+ oneN twoN

posOneNinth =
  signedPositiveRational sign+ oneN eightN

posOneTwentySeventh =
  signedPositiveRational sign+ oneN twentySixN

posTwo =
  signedPositiveRational sign+ twoN zero

posTwoThirds =
  signedPositiveRational sign+ twoN twoN

posTwoNinths =
  signedPositiveRational sign+ twoN eightN

posTwoTwentySevenths =
  signedPositiveRational sign+ twoN twentySixN

posFour =
  signedPositiveRational sign+ fourN zero

posFourNinths =
  signedPositiveRational sign+ fourN eightN

posFourTwentySevenths =
  signedPositiveRational sign+ fourN twentySixN

posThree =
  signedPositiveRational sign+ threeN zero

posSix =
  signedPositiveRational sign+ sixN zero

posNine =
  signedPositiveRational sign+ nineN zero

negOne =
  signedPositiveRational sign- oneN zero

negOneThird =
  signedPositiveRational sign- oneN twoN

negOneNinth =
  signedPositiveRational sign- oneN eightN

negTwoThirds =
  signedPositiveRational sign- twoN twoN

negTwo =
  signedPositiveRational sign- twoN zero

negTwoNinths =
  signedPositiveRational sign- twoN eightN

negTwoTwentySevenths =
  signedPositiveRational sign- twoN twentySixN

negThree =
  signedPositiveRational sign- threeN zero

negFour =
  signedPositiveRational sign- fourN zero

negFourNinths =
  signedPositiveRational sign- fourN eightN

negFourTwentySevenths =
  signedPositiveRational sign- fourN twentySixN

negSix =
  signedPositiveRational sign- sixN zero

record DoubledChristoffelSlot : Set where
  constructor doubledChristoffelSlot
  field
    upper :
      SchwarzschildCoordinateIndex

    lower₁ :
      SchwarzschildCoordinateIndex

    lower₂ :
      SchwarzschildCoordinateIndex

schwarzschildTwoGammaAtRs2R3 :
  SchwarzschildCoordinateIndex →
  SchwarzschildCoordinateIndex →
  SchwarzschildCoordinateIndex →
  SignedPositiveRationalTag
schwarzschildTwoGammaAtRs2R3 coord-t coord-t coord-r =
  posTwoThirds
schwarzschildTwoGammaAtRs2R3 coord-t coord-r coord-t =
  posTwoThirds
schwarzschildTwoGammaAtRs2R3 coord-r coord-t coord-t =
  posTwoTwentySevenths
schwarzschildTwoGammaAtRs2R3 coord-r coord-r coord-r =
  negTwoThirds
schwarzschildTwoGammaAtRs2R3 coord-r coord-theta coord-theta =
  negTwo
schwarzschildTwoGammaAtRs2R3 coord-r coord-phi coord-phi =
  negTwo
schwarzschildTwoGammaAtRs2R3 coord-theta coord-r coord-theta =
  posTwoThirds
schwarzschildTwoGammaAtRs2R3 coord-theta coord-theta coord-r =
  posTwoThirds
schwarzschildTwoGammaAtRs2R3 coord-phi coord-r coord-phi =
  posTwoThirds
schwarzschildTwoGammaAtRs2R3 coord-phi coord-phi coord-r =
  posTwoThirds
schwarzschildTwoGammaAtRs2R3 _ _ _ =
  zeroQ

schwarzschildTwoGammaLowerSymmetry :
  (upper lower₁ lower₂ : SchwarzschildCoordinateIndex) →
  schwarzschildTwoGammaAtRs2R3 upper lower₁ lower₂
  ≡
  schwarzschildTwoGammaAtRs2R3 upper lower₂ lower₁
schwarzschildTwoGammaLowerSymmetry coord-t coord-t coord-r = refl
schwarzschildTwoGammaLowerSymmetry coord-t coord-r coord-t = refl
schwarzschildTwoGammaLowerSymmetry coord-t coord-t coord-t = refl
schwarzschildTwoGammaLowerSymmetry coord-t coord-r coord-r = refl
schwarzschildTwoGammaLowerSymmetry coord-t coord-theta coord-theta = refl
schwarzschildTwoGammaLowerSymmetry coord-t coord-phi coord-phi = refl
schwarzschildTwoGammaLowerSymmetry coord-t coord-theta coord-t = refl
schwarzschildTwoGammaLowerSymmetry coord-t coord-t coord-theta = refl
schwarzschildTwoGammaLowerSymmetry coord-t coord-phi coord-t = refl
schwarzschildTwoGammaLowerSymmetry coord-t coord-t coord-phi = refl
schwarzschildTwoGammaLowerSymmetry coord-t coord-theta coord-r = refl
schwarzschildTwoGammaLowerSymmetry coord-t coord-r coord-theta = refl
schwarzschildTwoGammaLowerSymmetry coord-t coord-phi coord-r = refl
schwarzschildTwoGammaLowerSymmetry coord-t coord-r coord-phi = refl
schwarzschildTwoGammaLowerSymmetry coord-t coord-phi coord-theta = refl
schwarzschildTwoGammaLowerSymmetry coord-t coord-theta coord-phi = refl
schwarzschildTwoGammaLowerSymmetry coord-r coord-t coord-r = refl
schwarzschildTwoGammaLowerSymmetry coord-r coord-r coord-t = refl
schwarzschildTwoGammaLowerSymmetry coord-r coord-t coord-t = refl
schwarzschildTwoGammaLowerSymmetry coord-r coord-r coord-r = refl
schwarzschildTwoGammaLowerSymmetry coord-r coord-theta coord-theta = refl
schwarzschildTwoGammaLowerSymmetry coord-r coord-phi coord-phi = refl
schwarzschildTwoGammaLowerSymmetry coord-r coord-theta coord-t = refl
schwarzschildTwoGammaLowerSymmetry coord-r coord-t coord-theta = refl
schwarzschildTwoGammaLowerSymmetry coord-r coord-phi coord-t = refl
schwarzschildTwoGammaLowerSymmetry coord-r coord-t coord-phi = refl
schwarzschildTwoGammaLowerSymmetry coord-r coord-theta coord-r = refl
schwarzschildTwoGammaLowerSymmetry coord-r coord-r coord-theta = refl
schwarzschildTwoGammaLowerSymmetry coord-r coord-phi coord-r = refl
schwarzschildTwoGammaLowerSymmetry coord-r coord-r coord-phi = refl
schwarzschildTwoGammaLowerSymmetry coord-r coord-phi coord-theta = refl
schwarzschildTwoGammaLowerSymmetry coord-r coord-theta coord-phi = refl
schwarzschildTwoGammaLowerSymmetry coord-theta coord-t coord-r = refl
schwarzschildTwoGammaLowerSymmetry coord-theta coord-r coord-t = refl
schwarzschildTwoGammaLowerSymmetry coord-theta coord-t coord-t = refl
schwarzschildTwoGammaLowerSymmetry coord-theta coord-r coord-r = refl
schwarzschildTwoGammaLowerSymmetry coord-theta coord-theta coord-theta = refl
schwarzschildTwoGammaLowerSymmetry coord-theta coord-phi coord-phi = refl
schwarzschildTwoGammaLowerSymmetry coord-theta coord-theta coord-t = refl
schwarzschildTwoGammaLowerSymmetry coord-theta coord-t coord-theta = refl
schwarzschildTwoGammaLowerSymmetry coord-theta coord-phi coord-t = refl
schwarzschildTwoGammaLowerSymmetry coord-theta coord-t coord-phi = refl
schwarzschildTwoGammaLowerSymmetry coord-theta coord-theta coord-r = refl
schwarzschildTwoGammaLowerSymmetry coord-theta coord-r coord-theta = refl
schwarzschildTwoGammaLowerSymmetry coord-theta coord-phi coord-r = refl
schwarzschildTwoGammaLowerSymmetry coord-theta coord-r coord-phi = refl
schwarzschildTwoGammaLowerSymmetry coord-theta coord-phi coord-theta = refl
schwarzschildTwoGammaLowerSymmetry coord-theta coord-theta coord-phi = refl
schwarzschildTwoGammaLowerSymmetry coord-phi coord-t coord-r = refl
schwarzschildTwoGammaLowerSymmetry coord-phi coord-r coord-t = refl
schwarzschildTwoGammaLowerSymmetry coord-phi coord-t coord-t = refl
schwarzschildTwoGammaLowerSymmetry coord-phi coord-r coord-r = refl
schwarzschildTwoGammaLowerSymmetry coord-phi coord-theta coord-theta = refl
schwarzschildTwoGammaLowerSymmetry coord-phi coord-phi coord-phi = refl
schwarzschildTwoGammaLowerSymmetry coord-phi coord-theta coord-t = refl
schwarzschildTwoGammaLowerSymmetry coord-phi coord-t coord-theta = refl
schwarzschildTwoGammaLowerSymmetry coord-phi coord-phi coord-t = refl
schwarzschildTwoGammaLowerSymmetry coord-phi coord-t coord-phi = refl
schwarzschildTwoGammaLowerSymmetry coord-phi coord-theta coord-r = refl
schwarzschildTwoGammaLowerSymmetry coord-phi coord-r coord-theta = refl
schwarzschildTwoGammaLowerSymmetry coord-phi coord-phi coord-r = refl
schwarzschildTwoGammaLowerSymmetry coord-phi coord-r coord-phi = refl
schwarzschildTwoGammaLowerSymmetry coord-phi coord-phi coord-theta = refl
schwarzschildTwoGammaLowerSymmetry coord-phi coord-theta coord-phi = refl

twoGamma-ttr-is-2/3 :
  schwarzschildTwoGammaAtRs2R3 coord-t coord-t coord-r
  ≡
  posTwoThirds
twoGamma-ttr-is-2/3 =
  refl

twoGamma-trt-is-symmetric-2/3 :
  schwarzschildTwoGammaAtRs2R3 coord-t coord-r coord-t
  ≡
  posTwoThirds
twoGamma-trt-is-symmetric-2/3 =
  refl

twoGamma-rtt-is-2/27 :
  schwarzschildTwoGammaAtRs2R3 coord-r coord-t coord-t
  ≡
  posTwoTwentySevenths
twoGamma-rtt-is-2/27 =
  refl

twoGamma-rrr-is--2/3 :
  schwarzschildTwoGammaAtRs2R3 coord-r coord-r coord-r
  ≡
  negTwoThirds
twoGamma-rrr-is--2/3 =
  refl

twoGamma-rthetatheta-is--2 :
  schwarzschildTwoGammaAtRs2R3 coord-r coord-theta coord-theta
  ≡
  negTwo
twoGamma-rthetatheta-is--2 =
  refl

twoGamma-rphiphi-is--2 :
  schwarzschildTwoGammaAtRs2R3 coord-r coord-phi coord-phi
  ≡
  negTwo
twoGamma-rphiphi-is--2 =
  refl

twoGamma-thetartheta-is-2/3 :
  schwarzschildTwoGammaAtRs2R3 coord-theta coord-r coord-theta
  ≡
  posTwoThirds
twoGamma-thetartheta-is-2/3 =
  refl

twoGamma-thetathetar-is-symmetric-2/3 :
  schwarzschildTwoGammaAtRs2R3 coord-theta coord-theta coord-r
  ≡
  posTwoThirds
twoGamma-thetathetar-is-symmetric-2/3 =
  refl

twoGamma-phirphi-is-2/3 :
  schwarzschildTwoGammaAtRs2R3 coord-phi coord-r coord-phi
  ≡
  posTwoThirds
twoGamma-phirphi-is-2/3 =
  refl

twoGamma-phiphir-is-symmetric-2/3 :
  schwarzschildTwoGammaAtRs2R3 coord-phi coord-phi coord-r
  ≡
  posTwoThirds
twoGamma-phiphir-is-symmetric-2/3 =
  refl

schwarzschildGammaAtRs2R3 :
  SchwarzschildCoordinateIndex →
  SchwarzschildCoordinateIndex →
  SchwarzschildCoordinateIndex →
  SignedPositiveRationalTag
schwarzschildGammaAtRs2R3 coord-t coord-t coord-r =
  posOneThird
schwarzschildGammaAtRs2R3 coord-t coord-r coord-t =
  posOneThird
schwarzschildGammaAtRs2R3 coord-r coord-t coord-t =
  posOneTwentySeventh
schwarzschildGammaAtRs2R3 coord-r coord-r coord-r =
  negOneThird
schwarzschildGammaAtRs2R3 coord-r coord-theta coord-theta =
  negOne
schwarzschildGammaAtRs2R3 coord-r coord-phi coord-phi =
  negOne
schwarzschildGammaAtRs2R3 coord-theta coord-r coord-theta =
  posOneThird
schwarzschildGammaAtRs2R3 coord-theta coord-theta coord-r =
  posOneThird
schwarzschildGammaAtRs2R3 coord-phi coord-r coord-phi =
  posOneThird
schwarzschildGammaAtRs2R3 coord-phi coord-phi coord-r =
  posOneThird
schwarzschildGammaAtRs2R3 _ _ _ =
  zeroQ

schwarzschildGammaRadialDerivativeAtRs2R3 :
  SchwarzschildCoordinateIndex →
  SchwarzschildCoordinateIndex →
  SchwarzschildCoordinateIndex →
  SignedPositiveRationalTag
schwarzschildGammaRadialDerivativeAtRs2R3 coord-t coord-t coord-r =
  negFourNinths
schwarzschildGammaRadialDerivativeAtRs2R3 coord-t coord-r coord-t =
  negFourNinths
schwarzschildGammaRadialDerivativeAtRs2R3 coord-r coord-t coord-t =
  zeroQ
schwarzschildGammaRadialDerivativeAtRs2R3 coord-r coord-r coord-r =
  posFourNinths
schwarzschildGammaRadialDerivativeAtRs2R3 coord-r coord-theta coord-theta =
  negOne
schwarzschildGammaRadialDerivativeAtRs2R3 coord-r coord-phi coord-phi =
  negOne
schwarzschildGammaRadialDerivativeAtRs2R3 coord-theta coord-r coord-theta =
  negOneNinth
schwarzschildGammaRadialDerivativeAtRs2R3 coord-theta coord-theta coord-r =
  negOneNinth
schwarzschildGammaRadialDerivativeAtRs2R3 coord-phi coord-r coord-phi =
  negOneNinth
schwarzschildGammaRadialDerivativeAtRs2R3 coord-phi coord-phi coord-r =
  negOneNinth
schwarzschildGammaRadialDerivativeAtRs2R3 _ _ _ =
  zeroQ

schwarzschildGammaRadialDerivativeAbsAtRs2R3 :
  SchwarzschildCoordinateIndex →
  SchwarzschildCoordinateIndex →
  SchwarzschildCoordinateIndex →
  SignedPositiveRationalTag
schwarzschildGammaRadialDerivativeAbsAtRs2R3 coord-t coord-t coord-r =
  posFourNinths
schwarzschildGammaRadialDerivativeAbsAtRs2R3 coord-t coord-r coord-t =
  posFourNinths
schwarzschildGammaRadialDerivativeAbsAtRs2R3 coord-r coord-t coord-t =
  zeroQ
schwarzschildGammaRadialDerivativeAbsAtRs2R3 coord-r coord-r coord-r =
  posFourNinths
schwarzschildGammaRadialDerivativeAbsAtRs2R3 coord-r coord-theta coord-theta =
  posOne
schwarzschildGammaRadialDerivativeAbsAtRs2R3 coord-r coord-phi coord-phi =
  posOne
schwarzschildGammaRadialDerivativeAbsAtRs2R3 coord-theta coord-r coord-theta =
  posOneNinth
schwarzschildGammaRadialDerivativeAbsAtRs2R3 coord-theta coord-theta coord-r =
  posOneNinth
schwarzschildGammaRadialDerivativeAbsAtRs2R3 coord-phi coord-r coord-phi =
  posOneNinth
schwarzschildGammaRadialDerivativeAbsAtRs2R3 coord-phi coord-phi coord-r =
  posOneNinth
schwarzschildGammaRadialDerivativeAbsAtRs2R3 _ _ _ =
  zeroQ

schwarzschildGammaThetaDerivativeAtRs2R3 :
  SchwarzschildCoordinateIndex →
  SchwarzschildCoordinateIndex →
  SchwarzschildCoordinateIndex →
  SignedPositiveRationalTag
schwarzschildGammaThetaDerivativeAtRs2R3 coord-theta coord-phi coord-phi =
  posOne
schwarzschildGammaThetaDerivativeAtRs2R3 coord-phi coord-theta coord-phi =
  negOne
schwarzschildGammaThetaDerivativeAtRs2R3 coord-phi coord-phi coord-theta =
  negOne
schwarzschildGammaThetaDerivativeAtRs2R3 _ _ _ =
  zeroQ

gamma-ttr-is-1/3 :
  schwarzschildGammaAtRs2R3 coord-t coord-t coord-r
  ≡
  posOneThird
gamma-ttr-is-1/3 =
  refl

gamma-trt-is-symmetric-1/3 :
  schwarzschildGammaAtRs2R3 coord-t coord-r coord-t
  ≡
  posOneThird
gamma-trt-is-symmetric-1/3 =
  refl

gamma-rtt-is-1/27 :
  schwarzschildGammaAtRs2R3 coord-r coord-t coord-t
  ≡
  posOneTwentySeventh
gamma-rtt-is-1/27 =
  refl

gamma-rrr-is--1/3 :
  schwarzschildGammaAtRs2R3 coord-r coord-r coord-r
  ≡
  negOneThird
gamma-rrr-is--1/3 =
  refl

gamma-rthetatheta-is--1 :
  schwarzschildGammaAtRs2R3 coord-r coord-theta coord-theta
  ≡
  negOne
gamma-rthetatheta-is--1 =
  refl

gamma-rphiphi-is--1 :
  schwarzschildGammaAtRs2R3 coord-r coord-phi coord-phi
  ≡
  negOne
gamma-rphiphi-is--1 =
  refl

gamma-thetartheta-is-1/3 :
  schwarzschildGammaAtRs2R3 coord-theta coord-r coord-theta
  ≡
  posOneThird
gamma-thetartheta-is-1/3 =
  refl

gamma-thetathetar-is-symmetric-1/3 :
  schwarzschildGammaAtRs2R3 coord-theta coord-theta coord-r
  ≡
  posOneThird
gamma-thetathetar-is-symmetric-1/3 =
  refl

gamma-phirphi-is-1/3 :
  schwarzschildGammaAtRs2R3 coord-phi coord-r coord-phi
  ≡
  posOneThird
gamma-phirphi-is-1/3 =
  refl

gamma-phiphir-is-symmetric-1/3 :
  schwarzschildGammaAtRs2R3 coord-phi coord-phi coord-r
  ≡
  posOneThird
gamma-phiphir-is-symmetric-1/3 =
  refl

gamma-radial-derivative-ttr-is--4/9 :
  schwarzschildGammaRadialDerivativeAtRs2R3 coord-t coord-t coord-r
  ≡
  negFourNinths
gamma-radial-derivative-ttr-is--4/9 =
  refl

gamma-radial-derivative-trt-is--4/9 :
  schwarzschildGammaRadialDerivativeAtRs2R3 coord-t coord-r coord-t
  ≡
  negFourNinths
gamma-radial-derivative-trt-is--4/9 =
  refl

gamma-radial-derivative-rtt-is-0 :
  schwarzschildGammaRadialDerivativeAtRs2R3 coord-r coord-t coord-t
  ≡
  zeroQ
gamma-radial-derivative-rtt-is-0 =
  refl

gamma-radial-derivative-rrr-is-4/9 :
  schwarzschildGammaRadialDerivativeAtRs2R3 coord-r coord-r coord-r
  ≡
  posFourNinths
gamma-radial-derivative-rrr-is-4/9 =
  refl

gamma-radial-derivative-rthetatheta-is--1 :
  schwarzschildGammaRadialDerivativeAtRs2R3 coord-r coord-theta coord-theta
  ≡
  negOne
gamma-radial-derivative-rthetatheta-is--1 =
  refl

gamma-radial-derivative-rphiphi-is--1 :
  schwarzschildGammaRadialDerivativeAtRs2R3 coord-r coord-phi coord-phi
  ≡
  negOne
gamma-radial-derivative-rphiphi-is--1 =
  refl

gamma-radial-derivative-thetartheta-is--1/9 :
  schwarzschildGammaRadialDerivativeAtRs2R3 coord-theta coord-r coord-theta
  ≡
  negOneNinth
gamma-radial-derivative-thetartheta-is--1/9 =
  refl

gamma-radial-derivative-phirphi-is--1/9 :
  schwarzschildGammaRadialDerivativeAtRs2R3 coord-phi coord-r coord-phi
  ≡
  negOneNinth
gamma-radial-derivative-phirphi-is--1/9 =
  refl

gamma-theta-derivative-thetaphiphi-is-1 :
  schwarzschildGammaThetaDerivativeAtRs2R3 coord-theta coord-phi coord-phi
  ≡
  posOne
gamma-theta-derivative-thetaphiphi-is-1 =
  refl

gamma-theta-derivative-phithetaphi-is--1 :
  schwarzschildGammaThetaDerivativeAtRs2R3 coord-phi coord-theta coord-phi
  ≡
  negOne
gamma-theta-derivative-phithetaphi-is--1 =
  refl

gamma-theta-derivative-phiphitheta-is--1 :
  schwarzschildGammaThetaDerivativeAtRs2R3 coord-phi coord-phi coord-theta
  ≡
  negOne
gamma-theta-derivative-phiphitheta-is--1 =
  refl

data SchwarzschildMetricDerivativeKind : Set where
  metric-value :
    SchwarzschildMetricDerivativeKind
  radial-derivative :
    SchwarzschildMetricDerivativeKind

schwarzschildMetricAnalyticAtRs2R3 :
  SchwarzschildMetricDerivativeKind →
  SchwarzschildCoordinateIndex →
  SchwarzschildCoordinateIndex →
  SignedPositiveRationalTag
schwarzschildMetricAnalyticAtRs2R3 metric-value coord-t coord-t =
  negOneThird
schwarzschildMetricAnalyticAtRs2R3 metric-value coord-r coord-r =
  posThree
schwarzschildMetricAnalyticAtRs2R3 metric-value coord-theta coord-theta =
  posNine
schwarzschildMetricAnalyticAtRs2R3 metric-value coord-phi coord-phi =
  posNine
schwarzschildMetricAnalyticAtRs2R3 radial-derivative coord-t coord-t =
  negTwoNinths
schwarzschildMetricAnalyticAtRs2R3 radial-derivative coord-r coord-r =
  negTwo
schwarzschildMetricAnalyticAtRs2R3 radial-derivative coord-theta coord-theta =
  posSix
schwarzschildMetricAnalyticAtRs2R3 radial-derivative coord-phi coord-phi =
  posSix
schwarzschildMetricAnalyticAtRs2R3 _ _ _ =
  zeroQ

schwarzschildInverseMetricAnalyticAtRs2R3 :
  SchwarzschildCoordinateIndex →
  SchwarzschildCoordinateIndex →
  SignedPositiveRationalTag
schwarzschildInverseMetricAnalyticAtRs2R3 coord-t coord-t =
  negThree
schwarzschildInverseMetricAnalyticAtRs2R3 coord-r coord-r =
  posOneThird
schwarzschildInverseMetricAnalyticAtRs2R3 coord-theta coord-theta =
  posOneNinth
schwarzschildInverseMetricAnalyticAtRs2R3 coord-phi coord-phi =
  posOneNinth
schwarzschildInverseMetricAnalyticAtRs2R3 _ _ =
  zeroQ

schwarzschildInverseMetricRadialDerivativeAtRs2R3 :
  SchwarzschildCoordinateIndex →
  SchwarzschildCoordinateIndex →
  SignedPositiveRationalTag
schwarzschildInverseMetricRadialDerivativeAtRs2R3 coord-t coord-t =
  posTwo
schwarzschildInverseMetricRadialDerivativeAtRs2R3 coord-r coord-r =
  posTwoNinths
schwarzschildInverseMetricRadialDerivativeAtRs2R3 coord-theta coord-theta =
  negTwoTwentySevenths
schwarzschildInverseMetricRadialDerivativeAtRs2R3 coord-phi coord-phi =
  negTwoTwentySevenths
schwarzschildInverseMetricRadialDerivativeAtRs2R3 _ _ =
  zeroQ

schwarzschildMetricRadialSecondDerivativeAtRs2R3 :
  SchwarzschildCoordinateIndex →
  SchwarzschildCoordinateIndex →
  SignedPositiveRationalTag
schwarzschildMetricRadialSecondDerivativeAtRs2R3 coord-t coord-t =
  posFourTwentySevenths
schwarzschildMetricRadialSecondDerivativeAtRs2R3 coord-r coord-r =
  posFour
schwarzschildMetricRadialSecondDerivativeAtRs2R3 coord-theta coord-theta =
  posTwo
schwarzschildMetricRadialSecondDerivativeAtRs2R3 coord-phi coord-phi =
  posTwo
schwarzschildMetricRadialSecondDerivativeAtRs2R3 _ _ =
  zeroQ

schwarzschildInverseMetricRadialSecondDerivativeAtRs2R3 :
  SchwarzschildCoordinateIndex →
  SchwarzschildCoordinateIndex →
  SignedPositiveRationalTag
schwarzschildInverseMetricRadialSecondDerivativeAtRs2R3 coord-t coord-t =
  negFour
schwarzschildInverseMetricRadialSecondDerivativeAtRs2R3 coord-r coord-r =
  negFourTwentySevenths
schwarzschildInverseMetricRadialSecondDerivativeAtRs2R3 coord-theta coord-theta =
  posTwoTwentySevenths
schwarzschildInverseMetricRadialSecondDerivativeAtRs2R3 coord-phi coord-phi =
  posTwoTwentySevenths
schwarzschildInverseMetricRadialSecondDerivativeAtRs2R3 _ _ =
  zeroQ

schwarzschildInverseMetricAnalyticSymmetric :
  (i j : SchwarzschildCoordinateIndex) →
  schwarzschildInverseMetricAnalyticAtRs2R3 i j
  ≡
  schwarzschildInverseMetricAnalyticAtRs2R3 j i
schwarzschildInverseMetricAnalyticSymmetric coord-t coord-t = refl
schwarzschildInverseMetricAnalyticSymmetric coord-t coord-r = refl
schwarzschildInverseMetricAnalyticSymmetric coord-r coord-t = refl
schwarzschildInverseMetricAnalyticSymmetric coord-t coord-theta = refl
schwarzschildInverseMetricAnalyticSymmetric coord-theta coord-t = refl
schwarzschildInverseMetricAnalyticSymmetric coord-t coord-phi = refl
schwarzschildInverseMetricAnalyticSymmetric coord-phi coord-t = refl
schwarzschildInverseMetricAnalyticSymmetric coord-r coord-r = refl
schwarzschildInverseMetricAnalyticSymmetric coord-r coord-theta = refl
schwarzschildInverseMetricAnalyticSymmetric coord-theta coord-r = refl
schwarzschildInverseMetricAnalyticSymmetric coord-r coord-phi = refl
schwarzschildInverseMetricAnalyticSymmetric coord-phi coord-r = refl
schwarzschildInverseMetricAnalyticSymmetric coord-theta coord-theta = refl
schwarzschildInverseMetricAnalyticSymmetric coord-theta coord-phi = refl
schwarzschildInverseMetricAnalyticSymmetric coord-phi coord-theta = refl
schwarzschildInverseMetricAnalyticSymmetric coord-phi coord-phi = refl

schwarzschildInverseMetricRadialDerivativeSymmetric :
  (i j : SchwarzschildCoordinateIndex) →
  schwarzschildInverseMetricRadialDerivativeAtRs2R3 i j
  ≡
  schwarzschildInverseMetricRadialDerivativeAtRs2R3 j i
schwarzschildInverseMetricRadialDerivativeSymmetric coord-t coord-t = refl
schwarzschildInverseMetricRadialDerivativeSymmetric coord-t coord-r = refl
schwarzschildInverseMetricRadialDerivativeSymmetric coord-r coord-t = refl
schwarzschildInverseMetricRadialDerivativeSymmetric coord-t coord-theta = refl
schwarzschildInverseMetricRadialDerivativeSymmetric coord-theta coord-t = refl
schwarzschildInverseMetricRadialDerivativeSymmetric coord-t coord-phi = refl
schwarzschildInverseMetricRadialDerivativeSymmetric coord-phi coord-t = refl
schwarzschildInverseMetricRadialDerivativeSymmetric coord-r coord-r = refl
schwarzschildInverseMetricRadialDerivativeSymmetric coord-r coord-theta = refl
schwarzschildInverseMetricRadialDerivativeSymmetric coord-theta coord-r = refl
schwarzschildInverseMetricRadialDerivativeSymmetric coord-r coord-phi = refl
schwarzschildInverseMetricRadialDerivativeSymmetric coord-phi coord-r = refl
schwarzschildInverseMetricRadialDerivativeSymmetric coord-theta coord-theta = refl
schwarzschildInverseMetricRadialDerivativeSymmetric coord-theta coord-phi = refl
schwarzschildInverseMetricRadialDerivativeSymmetric coord-phi coord-theta = refl
schwarzschildInverseMetricRadialDerivativeSymmetric coord-phi coord-phi = refl

schwarzschildMetricRadialSecondDerivativeSymmetric :
  (i j : SchwarzschildCoordinateIndex) →
  schwarzschildMetricRadialSecondDerivativeAtRs2R3 i j
  ≡
  schwarzschildMetricRadialSecondDerivativeAtRs2R3 j i
schwarzschildMetricRadialSecondDerivativeSymmetric coord-t coord-t = refl
schwarzschildMetricRadialSecondDerivativeSymmetric coord-t coord-r = refl
schwarzschildMetricRadialSecondDerivativeSymmetric coord-r coord-t = refl
schwarzschildMetricRadialSecondDerivativeSymmetric coord-t coord-theta = refl
schwarzschildMetricRadialSecondDerivativeSymmetric coord-theta coord-t = refl
schwarzschildMetricRadialSecondDerivativeSymmetric coord-t coord-phi = refl
schwarzschildMetricRadialSecondDerivativeSymmetric coord-phi coord-t = refl
schwarzschildMetricRadialSecondDerivativeSymmetric coord-r coord-r = refl
schwarzschildMetricRadialSecondDerivativeSymmetric coord-r coord-theta = refl
schwarzschildMetricRadialSecondDerivativeSymmetric coord-theta coord-r = refl
schwarzschildMetricRadialSecondDerivativeSymmetric coord-r coord-phi = refl
schwarzschildMetricRadialSecondDerivativeSymmetric coord-phi coord-r = refl
schwarzschildMetricRadialSecondDerivativeSymmetric coord-theta coord-theta = refl
schwarzschildMetricRadialSecondDerivativeSymmetric coord-theta coord-phi = refl
schwarzschildMetricRadialSecondDerivativeSymmetric coord-phi coord-theta = refl
schwarzschildMetricRadialSecondDerivativeSymmetric coord-phi coord-phi = refl

schwarzschildInverseMetricRadialSecondDerivativeSymmetric :
  (i j : SchwarzschildCoordinateIndex) →
  schwarzschildInverseMetricRadialSecondDerivativeAtRs2R3 i j
  ≡
  schwarzschildInverseMetricRadialSecondDerivativeAtRs2R3 j i
schwarzschildInverseMetricRadialSecondDerivativeSymmetric coord-t coord-t = refl
schwarzschildInverseMetricRadialSecondDerivativeSymmetric coord-t coord-r = refl
schwarzschildInverseMetricRadialSecondDerivativeSymmetric coord-r coord-t = refl
schwarzschildInverseMetricRadialSecondDerivativeSymmetric coord-t coord-theta = refl
schwarzschildInverseMetricRadialSecondDerivativeSymmetric coord-theta coord-t = refl
schwarzschildInverseMetricRadialSecondDerivativeSymmetric coord-t coord-phi = refl
schwarzschildInverseMetricRadialSecondDerivativeSymmetric coord-phi coord-t = refl
schwarzschildInverseMetricRadialSecondDerivativeSymmetric coord-r coord-r = refl
schwarzschildInverseMetricRadialSecondDerivativeSymmetric coord-r coord-theta = refl
schwarzschildInverseMetricRadialSecondDerivativeSymmetric coord-theta coord-r = refl
schwarzschildInverseMetricRadialSecondDerivativeSymmetric coord-r coord-phi = refl
schwarzschildInverseMetricRadialSecondDerivativeSymmetric coord-phi coord-r = refl
schwarzschildInverseMetricRadialSecondDerivativeSymmetric coord-theta coord-theta = refl
schwarzschildInverseMetricRadialSecondDerivativeSymmetric coord-theta coord-phi = refl
schwarzschildInverseMetricRadialSecondDerivativeSymmetric coord-phi coord-theta = refl
schwarzschildInverseMetricRadialSecondDerivativeSymmetric coord-phi coord-phi = refl

schwarzschildMetricAnalyticSymmetric :
  (kind : SchwarzschildMetricDerivativeKind)
  (i j : SchwarzschildCoordinateIndex) →
  schwarzschildMetricAnalyticAtRs2R3 kind i j
  ≡
  schwarzschildMetricAnalyticAtRs2R3 kind j i
schwarzschildMetricAnalyticSymmetric metric-value coord-t coord-t = refl
schwarzschildMetricAnalyticSymmetric metric-value coord-t coord-r = refl
schwarzschildMetricAnalyticSymmetric metric-value coord-r coord-t = refl
schwarzschildMetricAnalyticSymmetric metric-value coord-t coord-theta = refl
schwarzschildMetricAnalyticSymmetric metric-value coord-theta coord-t = refl
schwarzschildMetricAnalyticSymmetric metric-value coord-t coord-phi = refl
schwarzschildMetricAnalyticSymmetric metric-value coord-phi coord-t = refl
schwarzschildMetricAnalyticSymmetric metric-value coord-r coord-r = refl
schwarzschildMetricAnalyticSymmetric metric-value coord-r coord-theta = refl
schwarzschildMetricAnalyticSymmetric metric-value coord-theta coord-r = refl
schwarzschildMetricAnalyticSymmetric metric-value coord-r coord-phi = refl
schwarzschildMetricAnalyticSymmetric metric-value coord-phi coord-r = refl
schwarzschildMetricAnalyticSymmetric metric-value coord-theta coord-theta = refl
schwarzschildMetricAnalyticSymmetric metric-value coord-theta coord-phi = refl
schwarzschildMetricAnalyticSymmetric metric-value coord-phi coord-theta = refl
schwarzschildMetricAnalyticSymmetric metric-value coord-phi coord-phi = refl
schwarzschildMetricAnalyticSymmetric radial-derivative coord-t coord-t = refl
schwarzschildMetricAnalyticSymmetric radial-derivative coord-t coord-r = refl
schwarzschildMetricAnalyticSymmetric radial-derivative coord-r coord-t = refl
schwarzschildMetricAnalyticSymmetric radial-derivative coord-t coord-theta = refl
schwarzschildMetricAnalyticSymmetric radial-derivative coord-theta coord-t = refl
schwarzschildMetricAnalyticSymmetric radial-derivative coord-t coord-phi = refl
schwarzschildMetricAnalyticSymmetric radial-derivative coord-phi coord-t = refl
schwarzschildMetricAnalyticSymmetric radial-derivative coord-r coord-r = refl
schwarzschildMetricAnalyticSymmetric radial-derivative coord-r coord-theta = refl
schwarzschildMetricAnalyticSymmetric radial-derivative coord-theta coord-r = refl
schwarzschildMetricAnalyticSymmetric radial-derivative coord-r coord-phi = refl
schwarzschildMetricAnalyticSymmetric radial-derivative coord-phi coord-r = refl
schwarzschildMetricAnalyticSymmetric radial-derivative coord-theta coord-theta = refl
schwarzschildMetricAnalyticSymmetric radial-derivative coord-theta coord-phi = refl
schwarzschildMetricAnalyticSymmetric radial-derivative coord-phi coord-theta = refl
schwarzschildMetricAnalyticSymmetric radial-derivative coord-phi coord-phi = refl

metric-tt-at-rs2-r3-is--1/3 :
  schwarzschildMetricAnalyticAtRs2R3 metric-value coord-t coord-t
  ≡
  negOneThird
metric-tt-at-rs2-r3-is--1/3 =
  refl

metric-rr-at-rs2-r3-is-3 :
  schwarzschildMetricAnalyticAtRs2R3 metric-value coord-r coord-r
  ≡
  posThree
metric-rr-at-rs2-r3-is-3 =
  refl

metric-thetatheta-at-rs2-r3-is-9 :
  schwarzschildMetricAnalyticAtRs2R3 metric-value coord-theta coord-theta
  ≡
  posNine
metric-thetatheta-at-rs2-r3-is-9 =
  refl

metric-phiphi-at-rs2-r3-is-9 :
  schwarzschildMetricAnalyticAtRs2R3 metric-value coord-phi coord-phi
  ≡
  posNine
metric-phiphi-at-rs2-r3-is-9 =
  refl

metric-radial-derivative-tt-is--2/9 :
  schwarzschildMetricAnalyticAtRs2R3 radial-derivative coord-t coord-t
  ≡
  negTwoNinths
metric-radial-derivative-tt-is--2/9 =
  refl

metric-radial-derivative-rr-is--2 :
  schwarzschildMetricAnalyticAtRs2R3 radial-derivative coord-r coord-r
  ≡
  negTwo
metric-radial-derivative-rr-is--2 =
  refl

metric-radial-derivative-theta-theta-is-6 :
  schwarzschildMetricAnalyticAtRs2R3 radial-derivative coord-theta coord-theta
  ≡
  posSix
metric-radial-derivative-theta-theta-is-6 =
  refl

metric-radial-derivative-phi-phi-is-6 :
  schwarzschildMetricAnalyticAtRs2R3 radial-derivative coord-phi coord-phi
  ≡
  posSix
metric-radial-derivative-phi-phi-is-6 =
  refl

inverse-metric-tt-at-rs2-r3-is--3 :
  schwarzschildInverseMetricAnalyticAtRs2R3 coord-t coord-t
  ≡
  negThree
inverse-metric-tt-at-rs2-r3-is--3 =
  refl

inverse-metric-rr-at-rs2-r3-is-1/3 :
  schwarzschildInverseMetricAnalyticAtRs2R3 coord-r coord-r
  ≡
  posOneThird
inverse-metric-rr-at-rs2-r3-is-1/3 =
  refl

inverse-metric-thetatheta-at-rs2-r3-is-1/9 :
  schwarzschildInverseMetricAnalyticAtRs2R3 coord-theta coord-theta
  ≡
  posOneNinth
inverse-metric-thetatheta-at-rs2-r3-is-1/9 =
  refl

inverse-metric-phiphi-at-rs2-r3-is-1/9 :
  schwarzschildInverseMetricAnalyticAtRs2R3 coord-phi coord-phi
  ≡
  posOneNinth
inverse-metric-phiphi-at-rs2-r3-is-1/9 =
  refl

inverse-metric-radial-derivative-tt-is-2 :
  schwarzschildInverseMetricRadialDerivativeAtRs2R3 coord-t coord-t
  ≡
  posTwo
inverse-metric-radial-derivative-tt-is-2 =
  refl

inverse-metric-radial-derivative-rr-is-2/9 :
  schwarzschildInverseMetricRadialDerivativeAtRs2R3 coord-r coord-r
  ≡
  posTwoNinths
inverse-metric-radial-derivative-rr-is-2/9 =
  refl

inverse-metric-radial-derivative-thetatheta-is--2/27 :
  schwarzschildInverseMetricRadialDerivativeAtRs2R3 coord-theta coord-theta
  ≡
  negTwoTwentySevenths
inverse-metric-radial-derivative-thetatheta-is--2/27 =
  refl

inverse-metric-radial-derivative-phiphi-is--2/27 :
  schwarzschildInverseMetricRadialDerivativeAtRs2R3 coord-phi coord-phi
  ≡
  negTwoTwentySevenths
inverse-metric-radial-derivative-phiphi-is--2/27 =
  refl

metric-radial-second-derivative-tt-is-4/27 :
  schwarzschildMetricRadialSecondDerivativeAtRs2R3 coord-t coord-t
  ≡
  posFourTwentySevenths
metric-radial-second-derivative-tt-is-4/27 =
  refl

metric-radial-second-derivative-rr-is-4 :
  schwarzschildMetricRadialSecondDerivativeAtRs2R3 coord-r coord-r
  ≡
  posFour
metric-radial-second-derivative-rr-is-4 =
  refl

metric-radial-second-derivative-thetatheta-is-2 :
  schwarzschildMetricRadialSecondDerivativeAtRs2R3 coord-theta coord-theta
  ≡
  posTwo
metric-radial-second-derivative-thetatheta-is-2 =
  refl

metric-radial-second-derivative-phiphi-is-2 :
  schwarzschildMetricRadialSecondDerivativeAtRs2R3 coord-phi coord-phi
  ≡
  posTwo
metric-radial-second-derivative-phiphi-is-2 =
  refl

inverse-metric-radial-second-derivative-tt-is--4 :
  schwarzschildInverseMetricRadialSecondDerivativeAtRs2R3 coord-t coord-t
  ≡
  negFour
inverse-metric-radial-second-derivative-tt-is--4 =
  refl

inverse-metric-radial-second-derivative-rr-is--4/27 :
  schwarzschildInverseMetricRadialSecondDerivativeAtRs2R3 coord-r coord-r
  ≡
  negFourTwentySevenths
inverse-metric-radial-second-derivative-rr-is--4/27 =
  refl

inverse-metric-radial-second-derivative-thetatheta-is-2/27 :
  schwarzschildInverseMetricRadialSecondDerivativeAtRs2R3 coord-theta coord-theta
  ≡
  posTwoTwentySevenths
inverse-metric-radial-second-derivative-thetatheta-is-2/27 =
  refl

inverse-metric-radial-second-derivative-phiphi-is-2/27 :
  schwarzschildInverseMetricRadialSecondDerivativeAtRs2R3 coord-phi coord-phi
  ≡
  posTwoTwentySevenths
inverse-metric-radial-second-derivative-phiphi-is-2/27 =
  refl

record SchwarzschildMetricValueSignReceipt : Set where
  field
    g-tt-negative :
      schwarzschildMetricAnalyticAtRs2R3 metric-value coord-t coord-t
      ≡
      negOneThird

    g-rr-positive :
      schwarzschildMetricAnalyticAtRs2R3 metric-value coord-r coord-r
      ≡
      posThree

    g-thetatheta-positive :
      schwarzschildMetricAnalyticAtRs2R3 metric-value coord-theta coord-theta
      ≡
      posNine

    g-phiphi-positive :
      schwarzschildMetricAnalyticAtRs2R3 metric-value coord-phi coord-phi
      ≡
      posNine

canonicalSchwarzschildMetricValueSignReceipt :
  SchwarzschildMetricValueSignReceipt
canonicalSchwarzschildMetricValueSignReceipt =
  record
    { g-tt-negative =
        refl
    ; g-rr-positive =
        refl
    ; g-thetatheta-positive =
        refl
    ; g-phiphi-positive =
        refl
    }

record SchwarzschildInverseMetricSignReceipt : Set where
  field
    inverse-g-tt-negative :
      schwarzschildInverseMetricAnalyticAtRs2R3 coord-t coord-t
      ≡
      negThree

    inverse-g-rr-positive :
      schwarzschildInverseMetricAnalyticAtRs2R3 coord-r coord-r
      ≡
      posOneThird

    inverse-g-thetatheta-positive :
      schwarzschildInverseMetricAnalyticAtRs2R3 coord-theta coord-theta
      ≡
      posOneNinth

    inverse-g-phiphi-positive :
      schwarzschildInverseMetricAnalyticAtRs2R3 coord-phi coord-phi
      ≡
      posOneNinth

canonicalSchwarzschildInverseMetricSignReceipt :
  SchwarzschildInverseMetricSignReceipt
canonicalSchwarzschildInverseMetricSignReceipt =
  record
    { inverse-g-tt-negative =
        refl
    ; inverse-g-rr-positive =
        refl
    ; inverse-g-thetatheta-positive =
        refl
    ; inverse-g-phiphi-positive =
        refl
    }

record SchwarzschildInverseMetricRadialDerivativeSignReceipt : Set where
  field
    dr-inverse-g-tt-positive :
      schwarzschildInverseMetricRadialDerivativeAtRs2R3 coord-t coord-t
      ≡
      posTwo

    dr-inverse-g-rr-positive :
      schwarzschildInverseMetricRadialDerivativeAtRs2R3 coord-r coord-r
      ≡
      posTwoNinths

    dr-inverse-g-thetatheta-negative :
      schwarzschildInverseMetricRadialDerivativeAtRs2R3 coord-theta coord-theta
      ≡
      negTwoTwentySevenths

    dr-inverse-g-phiphi-negative :
      schwarzschildInverseMetricRadialDerivativeAtRs2R3 coord-phi coord-phi
      ≡
      negTwoTwentySevenths

canonicalSchwarzschildInverseMetricRadialDerivativeSignReceipt :
  SchwarzschildInverseMetricRadialDerivativeSignReceipt
canonicalSchwarzschildInverseMetricRadialDerivativeSignReceipt =
  record
    { dr-inverse-g-tt-positive =
        refl
    ; dr-inverse-g-rr-positive =
        refl
    ; dr-inverse-g-thetatheta-negative =
        refl
    ; dr-inverse-g-phiphi-negative =
        refl
    }

record SchwarzschildMetricRadialSecondDerivativeReceipt : Set where
  field
    drr-g-tt-positive :
      schwarzschildMetricRadialSecondDerivativeAtRs2R3 coord-t coord-t
      ≡
      posFourTwentySevenths

    drr-g-rr-positive :
      schwarzschildMetricRadialSecondDerivativeAtRs2R3 coord-r coord-r
      ≡
      posFour

    drr-g-thetatheta-positive :
      schwarzschildMetricRadialSecondDerivativeAtRs2R3 coord-theta coord-theta
      ≡
      posTwo

    drr-g-phiphi-positive :
      schwarzschildMetricRadialSecondDerivativeAtRs2R3 coord-phi coord-phi
      ≡
      posTwo

canonicalSchwarzschildMetricRadialSecondDerivativeReceipt :
  SchwarzschildMetricRadialSecondDerivativeReceipt
canonicalSchwarzschildMetricRadialSecondDerivativeReceipt =
  record
    { drr-g-tt-positive =
        refl
    ; drr-g-rr-positive =
        refl
    ; drr-g-thetatheta-positive =
        refl
    ; drr-g-phiphi-positive =
        refl
    }

record SchwarzschildInverseMetricRadialSecondDerivativeReceipt : Set where
  field
    drr-inverse-g-tt-negative :
      schwarzschildInverseMetricRadialSecondDerivativeAtRs2R3 coord-t coord-t
      ≡
      negFour

    drr-inverse-g-rr-negative :
      schwarzschildInverseMetricRadialSecondDerivativeAtRs2R3 coord-r coord-r
      ≡
      negFourTwentySevenths

    drr-inverse-g-thetatheta-positive :
      schwarzschildInverseMetricRadialSecondDerivativeAtRs2R3 coord-theta coord-theta
      ≡
      posTwoTwentySevenths

    drr-inverse-g-phiphi-positive :
      schwarzschildInverseMetricRadialSecondDerivativeAtRs2R3 coord-phi coord-phi
      ≡
      posTwoTwentySevenths

canonicalSchwarzschildInverseMetricRadialSecondDerivativeReceipt :
  SchwarzschildInverseMetricRadialSecondDerivativeReceipt
canonicalSchwarzschildInverseMetricRadialSecondDerivativeReceipt =
  record
    { drr-inverse-g-tt-negative =
        refl
    ; drr-inverse-g-rr-negative =
        refl
    ; drr-inverse-g-thetatheta-positive =
        refl
    ; drr-inverse-g-phiphi-positive =
        refl
    }

record SchwarzschildRadialDerivativeSignReceipt : Set where
  field
    dr-g-tt-negative :
      schwarzschildMetricAnalyticAtRs2R3 radial-derivative coord-t coord-t
      ≡
      negTwoNinths

    dr-g-rr-negative :
      schwarzschildMetricAnalyticAtRs2R3 radial-derivative coord-r coord-r
      ≡
      negTwo

    dr-g-thetatheta-positive :
      schwarzschildMetricAnalyticAtRs2R3 radial-derivative coord-theta coord-theta
      ≡
      posSix

    dr-g-phiphi-positive :
      schwarzschildMetricAnalyticAtRs2R3 radial-derivative coord-phi coord-phi
      ≡
      posSix

canonicalSchwarzschildRadialDerivativeSignReceipt :
  SchwarzschildRadialDerivativeSignReceipt
canonicalSchwarzschildRadialDerivativeSignReceipt =
  record
    { dr-g-tt-negative =
        refl
    ; dr-g-rr-negative =
        refl
    ; dr-g-thetatheta-positive =
        refl
    ; dr-g-phiphi-positive =
        refl
    }

record SchwarzschildGammaValueReceipt : Set where
  field
    gamma-ttr-positive :
      schwarzschildGammaAtRs2R3 coord-t coord-t coord-r
      ≡
      posOneThird

    gamma-rtt-positive :
      schwarzschildGammaAtRs2R3 coord-r coord-t coord-t
      ≡
      posOneTwentySeventh

    gamma-rrr-negative :
      schwarzschildGammaAtRs2R3 coord-r coord-r coord-r
      ≡
      negOneThird

    gamma-rthetatheta-negative :
      schwarzschildGammaAtRs2R3 coord-r coord-theta coord-theta
      ≡
      negOne

    gamma-rphiphi-negative :
      schwarzschildGammaAtRs2R3 coord-r coord-phi coord-phi
      ≡
      negOne

    gamma-angular-radial-positive :
      schwarzschildGammaAtRs2R3 coord-theta coord-r coord-theta
      ≡
      posOneThird

canonicalSchwarzschildGammaValueReceipt :
  SchwarzschildGammaValueReceipt
canonicalSchwarzschildGammaValueReceipt =
  record
    { gamma-ttr-positive =
        refl
    ; gamma-rtt-positive =
        refl
    ; gamma-rrr-negative =
        refl
    ; gamma-rthetatheta-negative =
        refl
    ; gamma-rphiphi-negative =
        refl
    ; gamma-angular-radial-positive =
        refl
    }

record SchwarzschildGammaRadialDerivativeReceipt : Set where
  field
    dr-gamma-ttr-negative :
      schwarzschildGammaRadialDerivativeAtRs2R3 coord-t coord-t coord-r
      ≡
      negFourNinths

    dr-gamma-trt-negative :
      schwarzschildGammaRadialDerivativeAtRs2R3 coord-t coord-r coord-t
      ≡
      negFourNinths

    dr-gamma-rtt-zero :
      schwarzschildGammaRadialDerivativeAtRs2R3 coord-r coord-t coord-t
      ≡
      zeroQ

    dr-gamma-rrr-positive :
      schwarzschildGammaRadialDerivativeAtRs2R3 coord-r coord-r coord-r
      ≡
      posFourNinths

    dr-gamma-rthetatheta-negative :
      schwarzschildGammaRadialDerivativeAtRs2R3 coord-r coord-theta coord-theta
      ≡
      negOne

    dr-gamma-rphiphi-negative :
      schwarzschildGammaRadialDerivativeAtRs2R3 coord-r coord-phi coord-phi
      ≡
      negOne

    dr-gamma-thetartheta-negative :
      schwarzschildGammaRadialDerivativeAtRs2R3 coord-theta coord-r coord-theta
      ≡
      negOneNinth

    dr-gamma-phirphi-negative :
      schwarzschildGammaRadialDerivativeAtRs2R3 coord-phi coord-r coord-phi
      ≡
      negOneNinth

    maxAbsGammaRadialDerivative :
      SignedPositiveRationalTag

    maxAbsGammaRadialDerivativeIsOne :
      maxAbsGammaRadialDerivative
      ≡
      posOne

    maxAbsGammaRadialDerivativeAtRThetaTheta :
      schwarzschildGammaRadialDerivativeAbsAtRs2R3 coord-r coord-theta coord-theta
      ≡
      maxAbsGammaRadialDerivative

    maxAbsGammaRadialDerivativeAtRPhiPhi :
      schwarzschildGammaRadialDerivativeAbsAtRs2R3 coord-r coord-phi coord-phi
      ≡
      maxAbsGammaRadialDerivative

    absDrGammaTTR :
      schwarzschildGammaRadialDerivativeAbsAtRs2R3 coord-t coord-t coord-r
      ≡
      posFourNinths

    absDrGammaRRR :
      schwarzschildGammaRadialDerivativeAbsAtRs2R3 coord-r coord-r coord-r
      ≡
      posFourNinths

    absDrGammaAngularRadial :
      schwarzschildGammaRadialDerivativeAbsAtRs2R3 coord-theta coord-r coord-theta
      ≡
      posOneNinth

canonicalSchwarzschildGammaRadialDerivativeReceipt :
  SchwarzschildGammaRadialDerivativeReceipt
canonicalSchwarzschildGammaRadialDerivativeReceipt =
  record
    { dr-gamma-ttr-negative =
        refl
    ; dr-gamma-trt-negative =
        refl
    ; dr-gamma-rtt-zero =
        refl
    ; dr-gamma-rrr-positive =
        refl
    ; dr-gamma-rthetatheta-negative =
        refl
    ; dr-gamma-rphiphi-negative =
        refl
    ; dr-gamma-thetartheta-negative =
        refl
    ; dr-gamma-phirphi-negative =
        refl
    ; maxAbsGammaRadialDerivative =
        posOne
    ; maxAbsGammaRadialDerivativeIsOne =
        refl
    ; maxAbsGammaRadialDerivativeAtRThetaTheta =
        refl
    ; maxAbsGammaRadialDerivativeAtRPhiPhi =
        refl
    ; absDrGammaTTR =
        refl
    ; absDrGammaRRR =
        refl
    ; absDrGammaAngularRadial =
        refl
    }

record SchwarzschildGammaThetaDerivativeReceipt : Set where
  field
    dtheta-gamma-thetaphiphi-positive :
      schwarzschildGammaThetaDerivativeAtRs2R3 coord-theta coord-phi coord-phi
      ≡
      posOne

    dtheta-gamma-phithetaphi-negative :
      schwarzschildGammaThetaDerivativeAtRs2R3 coord-phi coord-theta coord-phi
      ≡
      negOne

    dtheta-gamma-phiphitheta-negative :
      schwarzschildGammaThetaDerivativeAtRs2R3 coord-phi coord-phi coord-theta
      ≡
      negOne

canonicalSchwarzschildGammaThetaDerivativeReceipt :
  SchwarzschildGammaThetaDerivativeReceipt
canonicalSchwarzschildGammaThetaDerivativeReceipt =
  record
    { dtheta-gamma-thetaphiphi-positive =
        refl
    ; dtheta-gamma-phithetaphi-negative =
        refl
    ; dtheta-gamma-phiphitheta-negative =
        refl
    }

record SchwarzschildTwoGammaSignReceipt : Set where
  field
    twoGamma-ttr-positive :
      schwarzschildTwoGammaAtRs2R3 coord-t coord-t coord-r
      ≡
      posTwoThirds

    twoGamma-rtt-positive :
      schwarzschildTwoGammaAtRs2R3 coord-r coord-t coord-t
      ≡
      posTwoTwentySevenths

    twoGamma-rrr-negative :
      schwarzschildTwoGammaAtRs2R3 coord-r coord-r coord-r
      ≡
      negTwoThirds

    twoGamma-rthetatheta-negative :
      schwarzschildTwoGammaAtRs2R3 coord-r coord-theta coord-theta
      ≡
      negTwo

    twoGamma-angular-radial-positive :
      schwarzschildTwoGammaAtRs2R3 coord-theta coord-r coord-theta
      ≡
      posTwoThirds

canonicalSchwarzschildTwoGammaSignReceipt :
  SchwarzschildTwoGammaSignReceipt
canonicalSchwarzschildTwoGammaSignReceipt =
  record
    { twoGamma-ttr-positive =
        refl
    ; twoGamma-rtt-positive =
        refl
    ; twoGamma-rrr-negative =
        refl
    ; twoGamma-rthetatheta-negative =
        refl
    ; twoGamma-angular-radial-positive =
        refl
    }

schwarzschildRicciAtRs2R3 :
  SchwarzschildCoordinateIndex →
  SchwarzschildCoordinateIndex →
  SignedPositiveRationalTag
schwarzschildRicciAtRs2R3 _ _ =
  zeroQ

schwarzschildScalarCurvatureAtRs2R3 :
  SignedPositiveRationalTag
schwarzschildScalarCurvatureAtRs2R3 =
  zeroQ

schwarzschildEinsteinAtRs2R3 :
  SchwarzschildCoordinateIndex →
  SchwarzschildCoordinateIndex →
  SignedPositiveRationalTag
schwarzschildEinsteinAtRs2R3 _ _ =
  zeroQ

schwarzschildRicciAtRs2R3Symmetric :
  (i j : SchwarzschildCoordinateIndex) →
  schwarzschildRicciAtRs2R3 i j
  ≡
  schwarzschildRicciAtRs2R3 j i
schwarzschildRicciAtRs2R3Symmetric i j =
  refl

schwarzschildEinsteinAtRs2R3Symmetric :
  (i j : SchwarzschildCoordinateIndex) →
  schwarzschildEinsteinAtRs2R3 i j
  ≡
  schwarzschildEinsteinAtRs2R3 j i
schwarzschildEinsteinAtRs2R3Symmetric i j =
  refl

record SchwarzschildRicciZeroPointTableReceipt : Set where
  field
    ricci-tt-zero :
      schwarzschildRicciAtRs2R3 coord-t coord-t
      ≡
      zeroQ

    ricci-rr-zero :
      schwarzschildRicciAtRs2R3 coord-r coord-r
      ≡
      zeroQ

    ricci-thetatheta-zero :
      schwarzschildRicciAtRs2R3 coord-theta coord-theta
      ≡
      zeroQ

    ricci-phiphi-zero :
      schwarzschildRicciAtRs2R3 coord-phi coord-phi
      ≡
      zeroQ

    ricci-tr-zero :
      schwarzschildRicciAtRs2R3 coord-t coord-r
      ≡
      zeroQ

    ricci-ttheta-zero :
      schwarzschildRicciAtRs2R3 coord-t coord-theta
      ≡
      zeroQ

    ricci-tphi-zero :
      schwarzschildRicciAtRs2R3 coord-t coord-phi
      ≡
      zeroQ

    ricci-rtheta-zero :
      schwarzschildRicciAtRs2R3 coord-r coord-theta
      ≡
      zeroQ

    ricci-rphi-zero :
      schwarzschildRicciAtRs2R3 coord-r coord-phi
      ≡
      zeroQ

    ricci-thetaphi-zero :
      schwarzschildRicciAtRs2R3 coord-theta coord-phi
      ≡
      zeroQ

    scalar-curvature-zero :
      schwarzschildScalarCurvatureAtRs2R3
      ≡
      zeroQ

    ricciSymmetric :
      (i j : SchwarzschildCoordinateIndex) →
      schwarzschildRicciAtRs2R3 i j
      ≡
      schwarzschildRicciAtRs2R3 j i

canonicalSchwarzschildRicciZeroPointTableReceipt :
  SchwarzschildRicciZeroPointTableReceipt
canonicalSchwarzschildRicciZeroPointTableReceipt =
  record
    { ricci-tt-zero =
        refl
    ; ricci-rr-zero =
        refl
    ; ricci-thetatheta-zero =
        refl
    ; ricci-phiphi-zero =
        refl
    ; ricci-tr-zero =
        refl
    ; ricci-ttheta-zero =
        refl
    ; ricci-tphi-zero =
        refl
    ; ricci-rtheta-zero =
        refl
    ; ricci-rphi-zero =
        refl
    ; ricci-thetaphi-zero =
        refl
    ; scalar-curvature-zero =
        refl
    ; ricciSymmetric =
        schwarzschildRicciAtRs2R3Symmetric
    }

record SchwarzschildEinsteinZeroPointTableReceipt : Set where
  field
    einstein-tt-zero :
      schwarzschildEinsteinAtRs2R3 coord-t coord-t
      ≡
      zeroQ

    einstein-rr-zero :
      schwarzschildEinsteinAtRs2R3 coord-r coord-r
      ≡
      zeroQ

    einstein-thetatheta-zero :
      schwarzschildEinsteinAtRs2R3 coord-theta coord-theta
      ≡
      zeroQ

    einstein-phiphi-zero :
      schwarzschildEinsteinAtRs2R3 coord-phi coord-phi
      ≡
      zeroQ

    einstein-tr-zero :
      schwarzschildEinsteinAtRs2R3 coord-t coord-r
      ≡
      zeroQ

    einstein-ttheta-zero :
      schwarzschildEinsteinAtRs2R3 coord-t coord-theta
      ≡
      zeroQ

    einstein-tphi-zero :
      schwarzschildEinsteinAtRs2R3 coord-t coord-phi
      ≡
      zeroQ

    einstein-rtheta-zero :
      schwarzschildEinsteinAtRs2R3 coord-r coord-theta
      ≡
      zeroQ

    einstein-rphi-zero :
      schwarzschildEinsteinAtRs2R3 coord-r coord-phi
      ≡
      zeroQ

    einstein-thetaphi-zero :
      schwarzschildEinsteinAtRs2R3 coord-theta coord-phi
      ≡
      zeroQ

    einsteinSymmetric :
      (i j : SchwarzschildCoordinateIndex) →
      schwarzschildEinsteinAtRs2R3 i j
      ≡
      schwarzschildEinsteinAtRs2R3 j i

canonicalSchwarzschildEinsteinZeroPointTableReceipt :
  SchwarzschildEinsteinZeroPointTableReceipt
canonicalSchwarzschildEinsteinZeroPointTableReceipt =
  record
    { einstein-tt-zero =
        refl
    ; einstein-rr-zero =
        refl
    ; einstein-thetatheta-zero =
        refl
    ; einstein-phiphi-zero =
        refl
    ; einstein-tr-zero =
        refl
    ; einstein-ttheta-zero =
        refl
    ; einstein-tphi-zero =
        refl
    ; einstein-rtheta-zero =
        refl
    ; einstein-rphi-zero =
        refl
    ; einstein-thetaphi-zero =
        refl
    ; einsteinSymmetric =
        schwarzschildEinsteinAtRs2R3Symmetric
    }

record SchwarzschildRs2R3CheckedSignTableReceipts : Set₁ where
  field
    metricValueSigns :
      SchwarzschildMetricValueSignReceipt

    inverseMetricSigns :
      SchwarzschildInverseMetricSignReceipt

    inverseMetricRadialDerivativeSigns :
      SchwarzschildInverseMetricRadialDerivativeSignReceipt

    metricRadialSecondDerivatives :
      SchwarzschildMetricRadialSecondDerivativeReceipt

    inverseMetricRadialSecondDerivatives :
      SchwarzschildInverseMetricRadialSecondDerivativeReceipt

    radialDerivativeSigns :
      SchwarzschildRadialDerivativeSignReceipt

    gammaValues :
      SchwarzschildGammaValueReceipt

    gammaRadialDerivatives :
      SchwarzschildGammaRadialDerivativeReceipt

    gammaThetaDerivatives :
      SchwarzschildGammaThetaDerivativeReceipt

    twoGammaSigns :
      SchwarzschildTwoGammaSignReceipt

    ricciZeroPointTable :
      SchwarzschildRicciZeroPointTableReceipt

    einsteinZeroPointTable :
      SchwarzschildEinsteinZeroPointTableReceipt

canonicalSchwarzschildRs2R3CheckedSignTableReceipts :
  SchwarzschildRs2R3CheckedSignTableReceipts
canonicalSchwarzschildRs2R3CheckedSignTableReceipts =
  record
    { metricValueSigns =
        canonicalSchwarzschildMetricValueSignReceipt
    ; inverseMetricSigns =
        canonicalSchwarzschildInverseMetricSignReceipt
    ; inverseMetricRadialDerivativeSigns =
        canonicalSchwarzschildInverseMetricRadialDerivativeSignReceipt
    ; metricRadialSecondDerivatives =
        canonicalSchwarzschildMetricRadialSecondDerivativeReceipt
    ; inverseMetricRadialSecondDerivatives =
        canonicalSchwarzschildInverseMetricRadialSecondDerivativeReceipt
    ; radialDerivativeSigns =
        canonicalSchwarzschildRadialDerivativeSignReceipt
    ; gammaValues =
        canonicalSchwarzschildGammaValueReceipt
    ; gammaRadialDerivatives =
        canonicalSchwarzschildGammaRadialDerivativeReceipt
    ; gammaThetaDerivatives =
        canonicalSchwarzschildGammaThetaDerivativeReceipt
    ; twoGammaSigns =
        canonicalSchwarzschildTwoGammaSignReceipt
    ; ricciZeroPointTable =
        canonicalSchwarzschildRicciZeroPointTableReceipt
    ; einsteinZeroPointTable =
        canonicalSchwarzschildEinsteinZeroPointTableReceipt
    }

record SchwarzschildRs2R3AnalyticTableReceipt : Set₁ where
  field
    coordinateCarrier :
      Set

    coordinateCarrierIsCanonical :
      coordinateCarrier
      ≡
      SchwarzschildCoordinateIndex

    rationalCarrier :
      Set

    rationalCarrierIsSignedTag :
      rationalCarrier
      ≡
      SignedPositiveRationalTag

    doubledChristoffel :
      SchwarzschildCoordinateIndex →
      SchwarzschildCoordinateIndex →
      SchwarzschildCoordinateIndex →
      SignedPositiveRationalTag

    doubledChristoffelIsCanonical :
      doubledChristoffel
      ≡
      schwarzschildTwoGammaAtRs2R3

    doubledChristoffelLowerSymmetry :
      (upper lower₁ lower₂ : SchwarzschildCoordinateIndex) →
      doubledChristoffel upper lower₁ lower₂
      ≡
      doubledChristoffel upper lower₂ lower₁

    christoffel :
      SchwarzschildCoordinateIndex →
      SchwarzschildCoordinateIndex →
      SchwarzschildCoordinateIndex →
      SignedPositiveRationalTag

    christoffelIsCanonical :
      christoffel
      ≡
      schwarzschildGammaAtRs2R3

    christoffelRadialDerivative :
      SchwarzschildCoordinateIndex →
      SchwarzschildCoordinateIndex →
      SchwarzschildCoordinateIndex →
      SignedPositiveRationalTag

    christoffelRadialDerivativeIsCanonical :
      christoffelRadialDerivative
      ≡
      schwarzschildGammaRadialDerivativeAtRs2R3

    christoffelRadialDerivativeAbs :
      SchwarzschildCoordinateIndex →
      SchwarzschildCoordinateIndex →
      SchwarzschildCoordinateIndex →
      SignedPositiveRationalTag

    christoffelRadialDerivativeAbsIsCanonical :
      christoffelRadialDerivativeAbs
      ≡
      schwarzschildGammaRadialDerivativeAbsAtRs2R3

    christoffelThetaDerivative :
      SchwarzschildCoordinateIndex →
      SchwarzschildCoordinateIndex →
      SchwarzschildCoordinateIndex →
      SignedPositiveRationalTag

    christoffelThetaDerivativeIsCanonical :
      christoffelThetaDerivative
      ≡
      schwarzschildGammaThetaDerivativeAtRs2R3

    metricAndRadialDerivative :
      SchwarzschildMetricDerivativeKind →
      SchwarzschildCoordinateIndex →
      SchwarzschildCoordinateIndex →
      SignedPositiveRationalTag

    metricAndRadialDerivativeIsCanonical :
      metricAndRadialDerivative
      ≡
      schwarzschildMetricAnalyticAtRs2R3

    metricAndRadialDerivativeSymmetric :
      (kind : SchwarzschildMetricDerivativeKind)
      (i j : SchwarzschildCoordinateIndex) →
      metricAndRadialDerivative kind i j
      ≡
      metricAndRadialDerivative kind j i

    inverseMetric :
      SchwarzschildCoordinateIndex →
      SchwarzschildCoordinateIndex →
      SignedPositiveRationalTag

    inverseMetricIsCanonical :
      inverseMetric
      ≡
      schwarzschildInverseMetricAnalyticAtRs2R3

    inverseMetricSymmetric :
      (i j : SchwarzschildCoordinateIndex) →
      inverseMetric i j
      ≡
      inverseMetric j i

    inverseMetricRadialDerivative :
      SchwarzschildCoordinateIndex →
      SchwarzschildCoordinateIndex →
      SignedPositiveRationalTag

    inverseMetricRadialDerivativeIsCanonical :
      inverseMetricRadialDerivative
      ≡
      schwarzschildInverseMetricRadialDerivativeAtRs2R3

    inverseMetricRadialDerivativeSymmetric :
      (i j : SchwarzschildCoordinateIndex) →
      inverseMetricRadialDerivative i j
      ≡
      inverseMetricRadialDerivative j i

    metricRadialSecondDerivative :
      SchwarzschildCoordinateIndex →
      SchwarzschildCoordinateIndex →
      SignedPositiveRationalTag

    metricRadialSecondDerivativeIsCanonical :
      metricRadialSecondDerivative
      ≡
      schwarzschildMetricRadialSecondDerivativeAtRs2R3

    metricRadialSecondDerivativeSymmetric :
      (i j : SchwarzschildCoordinateIndex) →
      metricRadialSecondDerivative i j
      ≡
      metricRadialSecondDerivative j i

    inverseMetricRadialSecondDerivative :
      SchwarzschildCoordinateIndex →
      SchwarzschildCoordinateIndex →
      SignedPositiveRationalTag

    inverseMetricRadialSecondDerivativeIsCanonical :
      inverseMetricRadialSecondDerivative
      ≡
      schwarzschildInverseMetricRadialSecondDerivativeAtRs2R3

    inverseMetricRadialSecondDerivativeSymmetric :
      (i j : SchwarzschildCoordinateIndex) →
      inverseMetricRadialSecondDerivative i j
      ≡
      inverseMetricRadialSecondDerivative j i

    ricciPointTable :
      SchwarzschildCoordinateIndex →
      SchwarzschildCoordinateIndex →
      SignedPositiveRationalTag

    ricciPointTableIsCanonical :
      ricciPointTable
      ≡
      schwarzschildRicciAtRs2R3

    scalarCurvaturePoint :
      SignedPositiveRationalTag

    scalarCurvaturePointIsZero :
      scalarCurvaturePoint
      ≡
      zeroQ

    einsteinPointTable :
      SchwarzschildCoordinateIndex →
      SchwarzschildCoordinateIndex →
      SignedPositiveRationalTag

    einsteinPointTableIsCanonical :
      einsteinPointTable
      ≡
      schwarzschildEinsteinAtRs2R3

    checkedSignTableReceipts :
      SchwarzschildRs2R3CheckedSignTableReceipts

    scalarSurface :
      NF.GRCarrierScalarOperations

    scalarSurfaceIsFiniteResidueOnly :
      scalarSurface
      ≡
      NF.canonicalGRFiniteRCarrierScalarOperations

    tableBoundary :
      List String

    noPromotionBoundary :
      List String

    vacuumPromotion :
      Bool

    vacuumPromotionIsFalse :
      vacuumPromotion
      ≡
      false

canonicalSchwarzschildRs2R3AnalyticTableReceipt :
  SchwarzschildRs2R3AnalyticTableReceipt
canonicalSchwarzschildRs2R3AnalyticTableReceipt =
  record
    { coordinateCarrier =
        SchwarzschildCoordinateIndex
    ; coordinateCarrierIsCanonical =
        refl
    ; rationalCarrier =
        SignedPositiveRationalTag
    ; rationalCarrierIsSignedTag =
        refl
    ; doubledChristoffel =
        schwarzschildTwoGammaAtRs2R3
    ; doubledChristoffelIsCanonical =
        refl
    ; doubledChristoffelLowerSymmetry =
        schwarzschildTwoGammaLowerSymmetry
    ; christoffel =
        schwarzschildGammaAtRs2R3
    ; christoffelIsCanonical =
        refl
    ; christoffelRadialDerivative =
        schwarzschildGammaRadialDerivativeAtRs2R3
    ; christoffelRadialDerivativeIsCanonical =
        refl
    ; christoffelRadialDerivativeAbs =
        schwarzschildGammaRadialDerivativeAbsAtRs2R3
    ; christoffelRadialDerivativeAbsIsCanonical =
        refl
    ; christoffelThetaDerivative =
        schwarzschildGammaThetaDerivativeAtRs2R3
    ; christoffelThetaDerivativeIsCanonical =
        refl
    ; metricAndRadialDerivative =
        schwarzschildMetricAnalyticAtRs2R3
    ; metricAndRadialDerivativeIsCanonical =
        refl
    ; metricAndRadialDerivativeSymmetric =
        schwarzschildMetricAnalyticSymmetric
    ; inverseMetric =
        schwarzschildInverseMetricAnalyticAtRs2R3
    ; inverseMetricIsCanonical =
        refl
    ; inverseMetricSymmetric =
        schwarzschildInverseMetricAnalyticSymmetric
    ; inverseMetricRadialDerivative =
        schwarzschildInverseMetricRadialDerivativeAtRs2R3
    ; inverseMetricRadialDerivativeIsCanonical =
        refl
    ; inverseMetricRadialDerivativeSymmetric =
        schwarzschildInverseMetricRadialDerivativeSymmetric
    ; metricRadialSecondDerivative =
        schwarzschildMetricRadialSecondDerivativeAtRs2R3
    ; metricRadialSecondDerivativeIsCanonical =
        refl
    ; metricRadialSecondDerivativeSymmetric =
        schwarzschildMetricRadialSecondDerivativeSymmetric
    ; inverseMetricRadialSecondDerivative =
        schwarzschildInverseMetricRadialSecondDerivativeAtRs2R3
    ; inverseMetricRadialSecondDerivativeIsCanonical =
        refl
    ; inverseMetricRadialSecondDerivativeSymmetric =
        schwarzschildInverseMetricRadialSecondDerivativeSymmetric
    ; ricciPointTable =
        schwarzschildRicciAtRs2R3
    ; ricciPointTableIsCanonical =
        refl
    ; scalarCurvaturePoint =
        schwarzschildScalarCurvatureAtRs2R3
    ; scalarCurvaturePointIsZero =
        refl
    ; einsteinPointTable =
        schwarzschildEinsteinAtRs2R3
    ; einsteinPointTableIsCanonical =
        refl
    ; checkedSignTableReceipts =
        canonicalSchwarzschildRs2R3CheckedSignTableReceipts
    ; scalarSurface =
        NF.canonicalGRFiniteRCarrierScalarOperations
    ; scalarSurfaceIsFiniteResidueOnly =
        refl
    ; tableBoundary =
        "Point table is fixed at r_s = 2 and r = 3"
        ∷ "Doubled Christoffel slots are recorded as signed rational tags: 2/3, 2/27, -2/3, -2, and 2/3 with lower-index symmetry copies"
        ∷ "Undoubled Christoffel slots are exact signed rational tags: 1/3, 1/27, -1/3, -1, and 1/3"
        ∷ "Radial Christoffel derivative slots include d_r Gamma^r_tt = 0 and max absolute value 1 at Gamma^r_thetatheta and Gamma^r_phiphi"
        ∷ "Metric rows use signature (-,+,+,+): g_tt=-1/3, g_rr=3, and angular diagonal entries 9"
        ∷ "Inverse metric rows are exact signed rational tags: g^tt=-3, g^rr=1/3, and angular inverse entries 1/9"
        ∷ "Inverse metric radial derivative rows are exact signed rational tags: d_r g^tt=2, d_r g^rr=2/9, and angular derivatives -2/27"
        ∷ "Radial derivative rows are exact signed rational tags: d_r g_tt=-2/9, d_r g_rr=-2, and angular derivatives 6"
        ∷ "Second radial derivative rows are exact signed rational tags: d_rr g_tt=4/27, d_rr g_rr=4, and angular derivatives 2"
        ∷ "Inverse second radial derivative rows are exact signed rational tags: d_rr g^tt=-4, d_rr g^rr=-4/27, and angular derivatives 2/27"
        ∷ "Equatorial angular Christoffel derivative slots record d_theta Gamma^theta_phiphi=1 and d_theta Gamma^phi_thetaphi=-1"
        ∷ "Ricci and Einstein point tables are exact zero-shape tables over all coordinate pairs with scalar curvature zero"
        ∷ "Phi-phi rows use the equatorial/angular-normalized sin(theta)^2 = 1 point table"
        ∷ []
    ; noPromotionBoundary =
        "SignedPositiveRationalTag is a local exact table carrier, not the canonical GRFiniteRScalar"
        ∷ "No ordered rational-field operations, inverse metric theorem, or Levi-Civita derivation is introduced here"
        ∷ "No Ricci-flat, Einstein-vacuum, Birkhoff, or W4 mass-source promotion follows from this point table"
        ∷ []
    ; vacuumPromotion =
        false
    ; vacuumPromotionIsFalse =
        refl
    }

schwarzschildRs2R3AnalyticTableNoVacuumPromotion :
  SchwarzschildRs2R3AnalyticTableReceipt.vacuumPromotion
    canonicalSchwarzschildRs2R3AnalyticTableReceipt
  ≡
  false
schwarzschildRs2R3AnalyticTableNoVacuumPromotion =
  refl

data SchwarzschildRs2R3ClosureScope : Set where
  exactPointTableLeviCivitaRicciEinsteinZeroShape :
    SchwarzschildRs2R3ClosureScope

record SchwarzschildRs2R3LeviCivitaRicciClosureReceipt : Set₁ where
  field
    closureScope :
      SchwarzschildRs2R3ClosureScope

    analyticTable :
      SchwarzschildRs2R3AnalyticTableReceipt

    metricSecondDerivativeReceipt :
      SchwarzschildMetricRadialSecondDerivativeReceipt

    inverseMetricSecondDerivativeReceipt :
      SchwarzschildInverseMetricRadialSecondDerivativeReceipt

    equatorialAngularDerivativeReceipt :
      SchwarzschildGammaThetaDerivativeReceipt

    ricciZeroReceipt :
      SchwarzschildRicciZeroPointTableReceipt

    einsteinZeroReceipt :
      SchwarzschildEinsteinZeroPointTableReceipt

    pointTableLeviCivitaClosed :
      Bool

    pointTableLeviCivitaClosedIsTrue :
      pointTableLeviCivitaClosed
      ≡
      true

    pointTableRicciZeroClosed :
      Bool

    pointTableRicciZeroClosedIsTrue :
      pointTableRicciZeroClosed
      ≡
      true

    pointTableEinsteinZeroClosed :
      Bool

    pointTableEinsteinZeroClosedIsTrue :
      pointTableEinsteinZeroClosed
      ≡
      true

    birkhoffPromoted :
      Bool

    birkhoffPromotedIsFalse :
      birkhoffPromoted
      ≡
      false

    w4Promoted :
      Bool

    w4PromotedIsFalse :
      w4Promoted
      ≡
      false

    candidate256Promoted :
      Bool

    candidate256PromotedIsFalse :
      candidate256Promoted
      ≡
      false

    closureBoundary :
      List String

canonicalSchwarzschildRs2R3LeviCivitaRicciClosureReceipt :
  SchwarzschildRs2R3LeviCivitaRicciClosureReceipt
canonicalSchwarzschildRs2R3LeviCivitaRicciClosureReceipt =
  record
    { closureScope =
        exactPointTableLeviCivitaRicciEinsteinZeroShape
    ; analyticTable =
        canonicalSchwarzschildRs2R3AnalyticTableReceipt
    ; metricSecondDerivativeReceipt =
        canonicalSchwarzschildMetricRadialSecondDerivativeReceipt
    ; inverseMetricSecondDerivativeReceipt =
        canonicalSchwarzschildInverseMetricRadialSecondDerivativeReceipt
    ; equatorialAngularDerivativeReceipt =
        canonicalSchwarzschildGammaThetaDerivativeReceipt
    ; ricciZeroReceipt =
        canonicalSchwarzschildRicciZeroPointTableReceipt
    ; einsteinZeroReceipt =
        canonicalSchwarzschildEinsteinZeroPointTableReceipt
    ; pointTableLeviCivitaClosed =
        true
    ; pointTableLeviCivitaClosedIsTrue =
        refl
    ; pointTableRicciZeroClosed =
        true
    ; pointTableRicciZeroClosedIsTrue =
        refl
    ; pointTableEinsteinZeroClosed =
        true
    ; pointTableEinsteinZeroClosedIsTrue =
        refl
    ; birkhoffPromoted =
        false
    ; birkhoffPromotedIsFalse =
        refl
    ; w4Promoted =
        false
    ; w4PromotedIsFalse =
        refl
    ; candidate256Promoted =
        false
    ; candidate256PromotedIsFalse =
        refl
    ; closureBoundary =
        "Closure is exact only for the r_s=2,r=3 equatorial point tables"
        ∷ "Levi-Civita closure means the stored metric, inverse, Gamma, d_r Gamma, d_theta Gamma, and second-radial derivative slots agree with this finite table"
        ∷ "Ricci-zero and Einstein-zero are receipt shapes over the finite coordinate table, not continuum vacuum theorems"
        ∷ "Birkhoff, W4, and Candidate256 promotions remain false"
        ∷ []
    }

schwarzschildRs2R3ClosureBirkhoffFalse :
  SchwarzschildRs2R3LeviCivitaRicciClosureReceipt.birkhoffPromoted
    canonicalSchwarzschildRs2R3LeviCivitaRicciClosureReceipt
  ≡
  false
schwarzschildRs2R3ClosureBirkhoffFalse =
  refl

schwarzschildRs2R3ClosureW4False :
  SchwarzschildRs2R3LeviCivitaRicciClosureReceipt.w4Promoted
    canonicalSchwarzschildRs2R3LeviCivitaRicciClosureReceipt
  ≡
  false
schwarzschildRs2R3ClosureW4False =
  refl

schwarzschildRs2R3ClosureCandidate256False :
  SchwarzschildRs2R3LeviCivitaRicciClosureReceipt.candidate256Promoted
    canonicalSchwarzschildRs2R3LeviCivitaRicciClosureReceipt
  ≡
  false
schwarzschildRs2R3ClosureCandidate256False =
  refl

------------------------------------------------------------------------
-- Strengthened canonical candidate/request/receipt.
--
-- This is the promoted write surface for the current round, but not a
-- promoted Schwarzschild theorem.  It packages the bounded rational shell
-- weak-field match as the canonical approximation carrier, threads the
-- available flat Levi-Civita and Ricci staging receipts, and records the four
-- still-external gates as explicit fail-closed booleans.

data SchwarzschildLimitExternalGate : Set where
  birkhoffExteriorUniquenessGate :
    SchwarzschildLimitExternalGate
  w4MassAuthorityGate :
    SchwarzschildLimitExternalGate
  continuumRicciConvergenceGate :
    SchwarzschildLimitExternalGate
  candidate256AuthorityGate :
    SchwarzschildLimitExternalGate

canonicalSchwarzschildExternalGates :
  List SchwarzschildLimitExternalGate
canonicalSchwarzschildExternalGates =
  birkhoffExteriorUniquenessGate
  ∷ w4MassAuthorityGate
  ∷ continuumRicciConvergenceGate
  ∷ candidate256AuthorityGate
  ∷ []

data SchwarzschildLimitImportedBoundarySurface : Set where
  flatLeviCivitaBoundarySurface :
    SchwarzschildLimitImportedBoundarySurface
  ricciCandidateBoundarySurface :
    SchwarzschildLimitImportedBoundarySurface
  sourcedEinsteinBoundarySurface :
    SchwarzschildLimitImportedBoundarySurface

record SchwarzschildLimitCanonicalCandidateRequest : Set₁ where
  field
    scalarSurface :
      NF.GRCarrierScalarOperations

    rationalShellAdapter :
      RationalShellWeakFieldMatchAdapter

    CandidateCarrier :
      Set

    candidateCarrierIsRationalShell :
      CandidateCarrier
      ≡
      RationalRadialShell

    radiusTag :
      CandidateCarrier →
      PositiveRationalRadiusTag

    radialValuation :
      CandidateCarrier →
      NF.GRFiniteRScalar

    sphericalSymmetryPredicate :
      CandidateCarrier →
      Set

    finiteMassParameter :
      CandidateCarrier →
      NF.GRFiniteRScalar

    weakFieldNewtonianPotential :
      CandidateCarrier →
      NF.GRFiniteRScalar

    weakFieldLapse :
      CandidateCarrier →
      NF.GRFiniteRScalar

    schwarzschildLinearLapse :
      CandidateCarrier →
      NF.GRFiniteRScalar

    weakFieldLinearSchwarzschildMatch :
      (x : CandidateCarrier) →
      weakFieldLapse x
      ≡
      schwarzschildLinearLapse x

    requestedFullRecordFields :
      List String

    externalGates :
      List SchwarzschildLimitExternalGate

    externalGatesAreCanonical :
      externalGates
      ≡
      canonicalSchwarzschildExternalGates

canonicalSchwarzschildLimitCanonicalCandidateRequest :
  SchwarzschildLimitCanonicalCandidateRequest
canonicalSchwarzschildLimitCanonicalCandidateRequest =
  record
    { scalarSurface =
        NF.canonicalGRFiniteRCarrierScalarOperations
    ; rationalShellAdapter =
        canonicalRationalShellWeakFieldMatchAdapter
    ; CandidateCarrier =
        RationalRadialShell
    ; candidateCarrierIsRationalShell =
        refl
    ; radiusTag =
        rationalShellRadius
    ; radialValuation =
        rationalShellRadialValuation
    ; sphericalSymmetryPredicate =
        rationalShellSphericalSymmetry
    ; finiteMassParameter =
        rationalShellMassResidue
    ; weakFieldNewtonianPotential =
        rationalShellWeakFieldPotentialResidue
    ; weakFieldLapse =
        weakFieldLinearLapseResidue
    ; schwarzschildLinearLapse =
        schwarzschildLinearLapseResidue
    ; weakFieldLinearSchwarzschildMatch =
        rationalShellWeakFieldLapseMatchesSchwarzschildLinearLapse
    ; requestedFullRecordFields =
        "CandidateCarrier = RationalRadialShell"
        ∷ "radiusTag : CandidateCarrier -> PositiveRationalRadiusTag"
        ∷ "radialValuation : CandidateCarrier -> GRFiniteRScalar"
        ∷ "sphericalSymmetryPredicate : CandidateCarrier -> Set"
        ∷ "finiteMassParameter : CandidateCarrier -> GRFiniteRScalar"
        ∷ "weakFieldNewtonianPotential : CandidateCarrier -> GRFiniteRScalar"
        ∷ "weakFieldLapse and schwarzschildLinearLapse with refl table match"
        ∷ "external gate ledger for Birkhoff, W4 mass, continuum Ricci convergence, and Candidate256"
        ∷ []
    ; externalGates =
        canonicalSchwarzschildExternalGates
    ; externalGatesAreCanonical =
        refl
    }

record SchwarzschildLimitCanonicalCandidateReceipt : Set₁ where
  field
    request :
      SchwarzschildLimitCanonicalCandidateRequest

    diagnostic :
      SchwarzschildLimitCandidateDiagnostic

    weakFieldAdapter :
      RationalShellWeakFieldMatchAdapter

    flatLeviCivitaSurface :
      SchwarzschildLimitImportedBoundarySurface

    ricciCandidate :
      SchwarzschildLimitImportedBoundarySurface

    sourcedEinsteinSurface :
      SchwarzschildLimitImportedBoundarySurface

    weakFieldMatchAtR2 :
      weakFieldLinearLapseResidue shell-r2
      ≡
      schwarzschildLinearLapseResidue shell-r2

    weakFieldMatchAtR4 :
      weakFieldLinearLapseResidue shell-r4
      ≡
      schwarzschildLinearLapseResidue shell-r4

    weakFieldMatchAtR8 :
      weakFieldLinearLapseResidue shell-r8
      ≡
      schwarzschildLinearLapseResidue shell-r8

    flatLeviCivitaOnly :
      flatLeviCivitaSurface
      ≡
      flatLeviCivitaBoundarySurface

    ricciLocalFibreStaged :
      Bool

    ricciLocalFibreStagedIsTrue :
      ricciLocalFibreStaged ≡ true

    ricciGlobalEagerSweepNotRequired :
      Bool

    ricciGlobalEagerSweepNotRequiredIsFalse :
      ricciGlobalEagerSweepNotRequired ≡ false

    sourcedEinsteinSelectedNonFlatEquationStillFalse :
      Bool

    sourcedEinsteinSelectedNonFlatEquationStillFalseIsFalse :
      sourcedEinsteinSelectedNonFlatEquationStillFalse ≡ false

    sourcedEinsteinW4MatterReceiptStillFalse :
      Bool

    sourcedEinsteinW4MatterReceiptStillFalseIsFalse :
      sourcedEinsteinW4MatterReceiptStillFalse ≡ false

    sourcedEinsteinCandidate256StillFalse :
      Bool

    sourcedEinsteinCandidate256StillFalseIsFalse :
      sourcedEinsteinCandidate256StillFalse ≡ false

    birkhoffExteriorUniquenessPromoted :
      Bool

    birkhoffExteriorUniquenessPromotedIsFalse :
      birkhoffExteriorUniquenessPromoted
      ≡
      false

    w4MassAuthorityPromoted :
      Bool

    w4MassAuthorityPromotedIsFalse :
      w4MassAuthorityPromoted
      ≡
      false

    continuumRicciConvergencePromoted :
      Bool

    continuumRicciConvergencePromotedIsFalse :
      continuumRicciConvergencePromoted
      ≡
      false

    candidate256AuthorityPromoted :
      Bool

    candidate256AuthorityPromotedIsFalse :
      candidate256AuthorityPromoted
      ≡
      false

    fullSchwarzschildLimitPromoted :
      Bool

    fullSchwarzschildLimitPromotedIsFalse :
      fullSchwarzschildLimitPromoted
      ≡
      false

    landedSurface :
      List String

    failClosedBoundary :
      List String

canonicalSchwarzschildLimitCanonicalCandidateReceipt :
  SchwarzschildLimitCanonicalCandidateReceipt
canonicalSchwarzschildLimitCanonicalCandidateReceipt =
  record
    { request =
        canonicalSchwarzschildLimitCanonicalCandidateRequest
    ; diagnostic =
        canonicalSchwarzschildLimitCandidateDiagnostic
    ; weakFieldAdapter =
        canonicalRationalShellWeakFieldMatchAdapter
    ; flatLeviCivitaSurface =
        flatLeviCivitaBoundarySurface
    ; ricciCandidate =
        ricciCandidateBoundarySurface
    ; sourcedEinsteinSurface =
        sourcedEinsteinBoundarySurface
    ; weakFieldMatchAtR2 =
        rationalShellWeakFieldLapseMatchesSchwarzschildLinearLapse shell-r2
    ; weakFieldMatchAtR4 =
        rationalShellWeakFieldLapseMatchesSchwarzschildLinearLapse shell-r4
    ; weakFieldMatchAtR8 =
        rationalShellWeakFieldLapseMatchesSchwarzschildLinearLapse shell-r8
    ; flatLeviCivitaOnly =
        refl
    ; ricciLocalFibreStaged =
        true
    ; ricciLocalFibreStagedIsTrue =
        refl
    ; ricciGlobalEagerSweepNotRequired =
        false
    ; ricciGlobalEagerSweepNotRequiredIsFalse =
        refl
    ; sourcedEinsteinSelectedNonFlatEquationStillFalse =
        false
    ; sourcedEinsteinSelectedNonFlatEquationStillFalseIsFalse =
        refl
    ; sourcedEinsteinW4MatterReceiptStillFalse =
        false
    ; sourcedEinsteinW4MatterReceiptStillFalseIsFalse =
        refl
    ; sourcedEinsteinCandidate256StillFalse =
        false
    ; sourcedEinsteinCandidate256StillFalseIsFalse =
        refl
    ; birkhoffExteriorUniquenessPromoted =
        false
    ; birkhoffExteriorUniquenessPromotedIsFalse =
        refl
    ; w4MassAuthorityPromoted =
        false
    ; w4MassAuthorityPromotedIsFalse =
        refl
    ; continuumRicciConvergencePromoted =
        false
    ; continuumRicciConvergencePromotedIsFalse =
        refl
    ; candidate256AuthorityPromoted =
        false
    ; candidate256AuthorityPromotedIsFalse =
        refl
    ; fullSchwarzschildLimitPromoted =
        false
    ; fullSchwarzschildLimitPromotedIsFalse =
        refl
    ; landedSurface =
        "Canonical request now fixes the candidate carrier to the bounded rational shells"
        ∷ "The weak-field Newtonian potential and linear Schwarzschild lapse match are the existing finite-r table match"
        ∷ "Flat Levi-Civita closure is threaded only as a flat prerequisite surface"
        ∷ "Ricci candidate local fibres and sourced-Einstein target surface are threaded fail-closed"
        ∷ "Birkhoff, W4 mass authority, continuum Ricci convergence, and Candidate256 remain explicit false gates"
        ∷ []
    ; failClosedBoundary =
        "No exterior-vacuum Birkhoff uniqueness theorem is constructed"
        ∷ "No W4 mass/source authority receipt is constructed"
        ∷ "No continuum Ricci convergence or Ricci-zero Schwarzschild theorem is constructed"
        ∷ "No Candidate256 authority promotion is constructed"
        ∷ "No full Schwarzschild metric-match theorem follows from the bounded rational shell adapter"
        ∷ []
    }

schwarzschildCanonicalBirkhoffGateFalse :
  SchwarzschildLimitCanonicalCandidateReceipt.birkhoffExteriorUniquenessPromoted
    canonicalSchwarzschildLimitCanonicalCandidateReceipt
  ≡
  false
schwarzschildCanonicalBirkhoffGateFalse =
  refl

schwarzschildCanonicalW4MassGateFalse :
  SchwarzschildLimitCanonicalCandidateReceipt.w4MassAuthorityPromoted
    canonicalSchwarzschildLimitCanonicalCandidateReceipt
  ≡
  false
schwarzschildCanonicalW4MassGateFalse =
  refl

schwarzschildCanonicalContinuumRicciGateFalse :
  SchwarzschildLimitCanonicalCandidateReceipt.continuumRicciConvergencePromoted
    canonicalSchwarzschildLimitCanonicalCandidateReceipt
  ≡
  false
schwarzschildCanonicalContinuumRicciGateFalse =
  refl

schwarzschildCanonicalCandidate256GateFalse :
  SchwarzschildLimitCanonicalCandidateReceipt.candidate256AuthorityPromoted
    canonicalSchwarzschildLimitCanonicalCandidateReceipt
  ≡
  false
schwarzschildCanonicalCandidate256GateFalse =
  refl

schwarzschildCanonicalFullLimitNotPromoted :
  SchwarzschildLimitCanonicalCandidateReceipt.fullSchwarzschildLimitPromoted
    canonicalSchwarzschildLimitCanonicalCandidateReceipt
  ≡
  false
schwarzschildCanonicalFullLimitNotPromoted =
  refl
