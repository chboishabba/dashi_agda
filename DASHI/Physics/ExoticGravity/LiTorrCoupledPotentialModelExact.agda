module DASHI.Physics.ExoticGravity.LiTorrCoupledPotentialModelExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- LI--TORR COUPLED-POTENTIAL MODEL
--
-- Source scope:
--   Ning Li and D. G. Torr, Phys. Rev. D 43, 457 (1991),
--     DOI 10.1103/PhysRevD.43.457.
--   Ning Li and D. G. Torr, Phys. Rev. B 46, 5489 (1992),
--     DOI 10.1103/PhysRevB.46.5489.
--   Douglas G. Torr and Ning Li, Foundations of Physics Letters 6 (1993),
--     "Gravitoelectric-electric coupling via superconductivity".
--
-- This owner records the mathematical CLAIM SHAPE used by Li/Torr.  It does
-- not promote the claimed enhancement into established physics.
------------------------------------------------------------------------

record LiTorrSourceRegistry : Set where
  constructor li-torr-source-registry
  field
    prd1991 prb1992 fopl1993 : String

canonicalLiTorrSourceRegistry : LiTorrSourceRegistry
canonicalLiTorrSourceRegistry = li-torr-source-registry
  "Li & Torr, Phys. Rev. D 43, 457 (1991), DOI 10.1103/PhysRevD.43.457"
  "Li & Torr, Phys. Rev. B 46, 5489 (1992), DOI 10.1103/PhysRevB.46.5489"
  "Torr & Li, Foundations of Physics Letters 6 (1993), Gravitoelectric-electric coupling via superconductivity"

------------------------------------------------------------------------
-- Equation (33) of the 1992 paper has the supercurrent respond to the
-- combined vector-potential coordinate
--
--     A + (m/q) A_g.
--
-- We encode the coordinate and its role without pretending that Agda has
-- proved the continuum field equation itself.
------------------------------------------------------------------------

record CoupledPotentialChart : Set where
  constructor coupled-potential-chart
  field
    electromagneticPotential : String
    gravitomagneticPotential : String
    massChargeRatio : String
    combinedPotential : String
    supercurrentEquationShape : String

canonicalCoupledPotentialChart : CoupledPotentialChart
canonicalCoupledPotentialChart = coupled-potential-chart
  "A(k,omega)"
  "A_g(k,omega)"
  "m/q"
  "A(k,omega) + (m/q) A_g(k,omega)"
  "j_e^s(k,omega) = -Q(k)[A(k,omega) + (m/q)A_g(k,omega)]"

------------------------------------------------------------------------
-- Equations (34)--(35) route the SAME combined coordinate into separate
-- electromagnetic and gravitomagnetic response equations.  This is the
-- important same-object weld: the two channels are coupled through one
-- response coordinate rather than merely appearing in the same paper.
------------------------------------------------------------------------

record CoupledResponseEquations : Set where
  constructor coupled-response-equations
  field
    electromagneticResponseShape : String
    gravitomagneticResponseShape : String
    sameCombinedPotentialFeedsBoth : Bool
    sameCombinedPotentialFeedsBothIsTrue :
      sameCombinedPotentialFeedsBoth ≡ true

canonicalCoupledResponseEquations : CoupledResponseEquations
canonicalCoupledResponseEquations = coupled-response-equations
  "k^2[(mu_r-1)/mu_r] A = -mu Q(k)[A + (m/q)A_g]"
  "k^2[(mu_g,r-1)/mu_g,r] A_g = mu_g Q(k)(m/q)[A + (m/q)A_g]"
  true refl

------------------------------------------------------------------------
-- 1991 boundary-condition result: the electromagnetic and gravitomagnetic
-- potentials/fields are not independent coordinates in the model.  The paper
-- reports exponential attenuation of the combined B + (m/q) B_g coordinate.
------------------------------------------------------------------------

record CombinedFieldAttenuationClaim : Set where
  constructor combined-field-attenuation-claim
  field
    combinedMagneticCoordinate : String
    penetrationLengthCoordinate : String
    exponentialAttenuationClaimed : Bool
    exponentialAttenuationClaimedIsTrue :
      exponentialAttenuationClaimed ≡ true

canonicalCombinedFieldAttenuationClaim : CombinedFieldAttenuationClaim
canonicalCombinedFieldAttenuationClaim = combined-field-attenuation-claim
  "B + (m/q) B_g"
  "lambda"
  true refl

------------------------------------------------------------------------
-- 1993 microscopic narrative.
--
-- The proposed mechanism distinguishes electric-current cancellation from
-- neutral mass-current cancellation.  Charged superelectron/bound-ion
-- currents are claimed to largely cancel electromagnetically, whereas the
-- neutral mass-current contribution is claimed not to cancel because gravity
-- is monopolar.  Coherent lattice-ion angular momentum is then proposed as
-- the source of detectable gravitomagnetic / time-dependent gravitoelectric
-- effects.
------------------------------------------------------------------------

record MicroscopicMechanismClaim : Set where
  constructor microscopic-mechanism-claim
  field
    coherentLatticeIonMotionClaimed : Bool
    coherentLatticeIonMotionClaimedIsTrue :
      coherentLatticeIonMotionClaimed ≡ true

    electricCurrentCancellationClaimed : Bool
    electricCurrentCancellationClaimedIsTrue :
      electricCurrentCancellationClaimed ≡ true

    neutralMassCurrentCancellationClaimed : Bool
    neutralMassCurrentCancellationClaimedIsFalse :
      neutralMassCurrentCancellationClaimed ≡ false

    alignedIonAngularMomentumSourcesGravitomagneticFieldClaimed : Bool
    alignedIonAngularMomentumSourcesGravitomagneticFieldClaimedIsTrue :
      alignedIonAngularMomentumSourcesGravitomagneticFieldClaimed ≡ true

    timeDependentMagneticVectorPotentialSourcesGravitoelectricEffectClaimed : Bool
    timeDependentMagneticVectorPotentialSourcesGravitoelectricEffectClaimedIsTrue :
      timeDependentMagneticVectorPotentialSourcesGravitoelectricEffectClaimed ≡ true

canonicalMicroscopicMechanismClaim : MicroscopicMechanismClaim
canonicalMicroscopicMechanismClaim = microscopic-mechanism-claim
  true refl
  true refl
  false refl
  true refl
  true refl

------------------------------------------------------------------------
-- Evidence firewall.
------------------------------------------------------------------------

record LiTorrTheoryStatusBoundary : Set where
  constructor li-torr-theory-status-boundary
  field
    equationsAreHistoricalPublishedClaims : Bool
    equationsAreHistoricalPublishedClaimsIsTrue :
      equationsAreHistoricalPublishedClaims ≡ true

    historicalPublicationMakesEnhancementEstablished : Bool
    historicalPublicationMakesEnhancementEstablishedIsFalse :
      historicalPublicationMakesEnhancementEstablished ≡ false

    weakFieldGravitomagnetismImpliesSuperconductingEnhancement : Bool
    weakFieldGravitomagnetismImpliesSuperconductingEnhancementIsFalse :
      weakFieldGravitomagnetismImpliesSuperconductingEnhancement ≡ false

canonicalLiTorrTheoryStatusBoundary : LiTorrTheoryStatusBoundary
canonicalLiTorrTheoryStatusBoundary =
  li-torr-theory-status-boundary true refl false refl false refl
