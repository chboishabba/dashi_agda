module DASHI.Empirical.DarkDimensionProspectiveDiscriminatorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Core.RequiredObserverAxisJoinAdequacyExact as AxisJoin
import DASHI.Empirical.GRQuantumPredictionProtocol as Prediction
import DASHI.Empirical.DarkDimensionEmpiricalDiscriminationExact as Discrimination
import DASHI.Physics.Closure.DarkDimensionStringPromotionBoundaryExact as DarkDimension

------------------------------------------------------------------------
-- DARK-DIMENSION PROSPECTIVE DISCRIMINATOR
--
-- Cross-pollination target:
--   * the GR/quantum prediction protocol owns preregistration / holdout /
--     competing-model requirements;
--   * RequiredObserverAxisJoinAdequacyExact owns the product law for
--     transverse observer axes;
--   * IntersectionalNonFactorability owns the proof that one transverse axis
--     cannot recover another once two states collide on the first axis;
--   * DarkDimensionEmpiricalDiscriminationExact owns the retrospective
--     DESI-era fit/comparator boundary.
--
-- This module contributes only the missing prospective *shape*:
--
--   future full-shape cosmology axis
--            ×
--   short-range gravity axis
--            -> joint discriminator carrier.
--
-- No future result, numerical separation, preregistration, or string-theory
-- identity is fabricated.  The target is explicitly open until those receipts
-- exist.
------------------------------------------------------------------------

false≢true : false ≡ true → ⊥
false≢true ()

------------------------------------------------------------------------
-- Orthogonal observer axes.
------------------------------------------------------------------------

data FullShapeCosmologyState : Set where
  fullShapeUnobserved : FullShapeCosmologyState
  nearBAODAOFeatureSupported : FullShapeCosmologyState
  nearBAODAOFeatureDisfavoured : FullShapeCosmologyState

data ShortRangeGravityState : Set where
  shortRangeGravityUnobserved : ShortRangeGravityState
  micronScaleDeviationSupported : ShortRangeGravityState
  micronScaleDeviationDisfavoured : ShortRangeGravityState

record ProspectiveObservationState : Set where
  constructor prospectiveObservationState
  field
    cosmologyState : FullShapeCosmologyState
    gravityState : ShortRangeGravityState

open ProspectiveObservationState public

fullShapeCosmologyAxis : ProspectiveObservationState → FullShapeCosmologyState
fullShapeCosmologyAxis = cosmologyState

shortRangeGravityAxis : ProspectiveObservationState → ShortRangeGravityState
shortRangeGravityAxis = gravityState

jointProspectiveAxis :
  ProspectiveObservationState → FullShapeCosmologyState × ShortRangeGravityState
jointProspectiveAxis =
  AxisJoin.jointAxis fullShapeCosmologyAxis shortRangeGravityAxis

jointAxisRetainsCosmology :
  AxisJoin.RetainsAxis jointProspectiveAxis fullShapeCosmologyAxis
jointAxisRetainsCosmology =
  AxisJoin.jointRetainsLeft fullShapeCosmologyAxis shortRangeGravityAxis

jointAxisRetainsShortRangeGravity :
  AxisJoin.RetainsAxis jointProspectiveAxis shortRangeGravityAxis
jointAxisRetainsShortRangeGravity =
  AxisJoin.jointRetainsRight fullShapeCosmologyAxis shortRangeGravityAxis

------------------------------------------------------------------------
-- Transverse nonfactorability.
--
-- These finite witnesses do not assert that any particular future observation
-- will occur.  They establish the information-geometry fact needed by the
-- prospective design: fixing one axis does not determine the other axis.
------------------------------------------------------------------------

sameCosmologyGravitySupported : ProspectiveObservationState
sameCosmologyGravitySupported =
  prospectiveObservationState
    fullShapeUnobserved
    micronScaleDeviationSupported

sameCosmologyGravityDisfavoured : ProspectiveObservationState
sameCosmologyGravityDisfavoured =
  prospectiveObservationState
    fullShapeUnobserved
    micronScaleDeviationDisfavoured

sameCosmologyDifferentGravityWitness :
  NonFactor.NonFactorabilityWitness
    fullShapeCosmologyAxis
    shortRangeGravityAxis
sameCosmologyDifferentGravityWitness =
  NonFactor.nonFactorabilityWitness
    sameCosmologyGravitySupported
    sameCosmologyGravityDisfavoured
    refl
    (λ ())

cosmologyCannotRecoverShortRangeGravity :
  NonFactor.FactorsThrough
    fullShapeCosmologyAxis
    shortRangeGravityAxis →
  ⊥
cosmologyCannotRecoverShortRangeGravity =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    sameCosmologyDifferentGravityWitness

sameGravityCosmologySupported : ProspectiveObservationState
sameGravityCosmologySupported =
  prospectiveObservationState
    nearBAODAOFeatureSupported
    shortRangeGravityUnobserved

sameGravityCosmologyDisfavoured : ProspectiveObservationState
sameGravityCosmologyDisfavoured =
  prospectiveObservationState
    nearBAODAOFeatureDisfavoured
    shortRangeGravityUnobserved

sameGravityDifferentCosmologyWitness :
  NonFactor.NonFactorabilityWitness
    shortRangeGravityAxis
    fullShapeCosmologyAxis
sameGravityDifferentCosmologyWitness =
  NonFactor.nonFactorabilityWitness
    sameGravityCosmologySupported
    sameGravityCosmologyDisfavoured
    refl
    (λ ())

shortRangeGravityCannotRecoverCosmology :
  NonFactor.FactorsThrough
    shortRangeGravityAxis
    fullShapeCosmologyAxis →
  ⊥
shortRangeGravityCannotRecoverCosmology =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    sameGravityDifferentCosmologyWitness

cosmologyRechartCannotRecoverShortRangeGravity :
  ∀ {Recharted : Set} →
  (rechart : FullShapeCosmologyState → Recharted) →
  NonFactor.FactorsThrough
    (λ state → rechart (fullShapeCosmologyAxis state))
    shortRangeGravityAxis →
  ⊥
cosmologyRechartCannotRecoverShortRangeGravity rechart =
  NonFactor.rechartingCannotRecoverErasedPhenomenon
    rechart
    sameCosmologyDifferentGravityWitness

------------------------------------------------------------------------
-- Source-bound future targets.
------------------------------------------------------------------------

dao2026 : Source.AttributedSource
dao2026 =
  Source.mkDOISource
    "Mathias Garny; Florian Niedermann; Martin S. Sloth"
    "Dark acoustic oscillations as an early-Universe explanation of the DESI anomaly"
    "Physical Review D 114, 043523"
    "2026"
    "10.1103/y31p-9g5k"
    "https://doi.org/10.1103/y31p-9g5k"
    Source.academicArticleSource
    "source for the explicit future full-shape DESI/Euclid scrutiny target for a near-BAO dark-acoustic-oscillation feature; it does not prove the DAO mechanism"
    Source.publicAttribution

lawSmithEtAl2024 : Source.AttributedSource
lawSmithEtAl2024 =
  Source.mkDOISource
    "Jamie A. P. Law-Smith; Georges Obied; Anirudh Prabhu; Cumrun Vafa"
    "Astrophysical constraints on decaying dark gravitons"
    "Journal of High Energy Physics 2024, 47"
    "2024"
    "10.1007/JHEP06(2024)047"
    "https://doi.org/10.1007/JHEP06(2024)047"
    Source.academicArticleSource
    "source for the currently viable Dark-Dimension effective-size range around 1-30 micrometres and dark-graviton observable constraints; it does not by itself specify a laboratory discovery threshold"
    Source.publicAttribution

anchordoquiAntoniadisCunat2024 : Source.AttributedSource
anchordoquiAntoniadisCunat2024 =
  Source.mkDOISource
    "Luis A. Anchordoqui; Ignatios Antoniadis; Jules Cunat"
    "Dark dimension and the standard model landscape"
    "Physical Review D 109, 016028"
    "2024"
    "10.1103/PhysRevD.109.016028"
    "https://doi.org/10.1103/PhysRevD.109.016028"
    Source.academicArticleSource
    "source for the short-range-gravity laboratory boundary R_perp < 30 micrometres cited in a Dark-Dimension realization; null inverse-square-law tests constrain the radius but do not identify string theory"
    Source.publicAttribution

record ProspectiveTarget : Set where
  constructor prospectiveTarget
  field
    targetLabel : String
    targetSource : Source.AttributedSource
    futureObservable : String
    modelSpecificInterpretation : String
    quantitativeSeparationLocked : Bool
    preregisteredBeforeFutureData : Bool
    heldOutFutureObservation : Bool
    targetUniquelyIdentifiesMechanism : Bool
    targetUniquelyIdentifiesStringTheory : Bool

open ProspectiveTarget public

daoFutureFullShapeTarget : ProspectiveTarget
daoFutureFullShapeTarget =
  prospectiveTarget
    "DAO near-BAO full-shape discriminator"
    dao2026
    "future full-shape galaxy-clustering data from DESI and Euclid around the BAO/DAO feature"
    "tests the near-BAO DAO explanation against alternative interpretations of the DESI anomaly"
    false
    false
    true
    false
    false

darkDimensionMicronGravityTarget : ProspectiveTarget
darkDimensionMicronGravityTarget =
  prospectiveTarget
    "Dark-Dimension short-range-gravity discriminator"
    lawSmithEtAl2024
    "future inverse-square-law / short-range gravity sensitivity spanning the source-supported 1-30 micrometre Dark-Dimension range"
    "constrains or supports the mesoscopic extra-dimension realization independently of the DESI evolving-dark-sector fit"
    false
    false
    true
    false
    false

------------------------------------------------------------------------
-- Packet status.  The target axes are selected but the actual predictive
-- separation and preregistration are intentionally still unpaid.
------------------------------------------------------------------------

record ProspectiveDiscriminatorPacket : Set where
  constructor prospectiveDiscriminatorPacket
  field
    cosmologyTargetSpecified : Bool
    shortRangeGravityTargetSpecified : Bool
    transverseJointAxisConstructed : Bool
    competingModelsExplicit : Bool
    quantitativeModelSeparationLocked : Bool
    preregistrationIdentifierRecorded : Bool
    futureDataStillHeldOut : Bool
    uniqueMechanismEstablished : Bool
    stringTheoryIdentityEstablished : Bool
    prospectivePacketLocked : Bool

open ProspectiveDiscriminatorPacket public

canonicalProspectiveDiscriminatorPacket : ProspectiveDiscriminatorPacket
canonicalProspectiveDiscriminatorPacket =
  prospectiveDiscriminatorPacket
    true
    true
    true
    true
    false
    false
    true
    false
    false
    false

prospectivePacketStillOpen :
  prospectivePacketLocked canonicalProspectiveDiscriminatorPacket ≡ false
prospectivePacketStillOpen = refl

------------------------------------------------------------------------
-- Promotion / WrongType firewalls.
------------------------------------------------------------------------

record UniqueMechanismFromCosmologyWitness : Set where
  constructor uniqueMechanismFromCosmologyWitness
  field
    cosmologyUniquePaid :
      uniqueMechanismEstablished canonicalProspectiveDiscriminatorPacket ≡ true

open UniqueMechanismFromCosmologyWitness public

record StringTheoryFromShortRangeGravityWitness : Set where
  constructor stringTheoryFromShortRangeGravityWitness
  field
    shortRangeStringIdentityPaid :
      stringTheoryIdentityEstablished canonicalProspectiveDiscriminatorPacket ≡ true

open StringTheoryFromShortRangeGravityWitness public

record StringTheoryFromJointAxisWitness : Set where
  constructor stringTheoryFromJointAxisWitness
  field
    jointStringIdentityPaid :
      stringTheoryIdentityEstablished canonicalProspectiveDiscriminatorPacket ≡ true

open StringTheoryFromJointAxisWitness public

cosmologyOnlyDoesNotPayUniqueMechanism :
  UniqueMechanismFromCosmologyWitness → ⊥
cosmologyOnlyDoesNotPayUniqueMechanism witness =
  false≢true (cosmologyUniquePaid witness)

shortRangeGravityOnlyDoesNotPayStringTheory :
  StringTheoryFromShortRangeGravityWitness → ⊥
shortRangeGravityOnlyDoesNotPayStringTheory witness =
  false≢true (shortRangeStringIdentityPaid witness)

jointAxisStillDoesNotPayStringTheory :
  StringTheoryFromJointAxisWitness → ⊥
jointAxisStillDoesNotPayStringTheory witness =
  false≢true (jointStringIdentityPaid witness)

------------------------------------------------------------------------
-- Cross-pollination with the strict GR/quantum prediction boundary.
-- Selecting future axes and keeping data held out is progress, but it is not
-- the same object as a DASHI-derived QuantitativeFalsifiablePrediction.
------------------------------------------------------------------------

prospectivePacketDoesNotBecomeDASHIDerivedPrediction :
  Prediction.quantitativePredictionDerived
    Prediction.canonicalPredictionBoundary
  ≡ false
prospectivePacketDoesNotBecomeDASHIDerivedPrediction =
  Prediction.quantitativePredictionDerivedIsFalse
    Prediction.canonicalPredictionBoundary

retrospectiveFitRemainsNonPromoting :
  Discrimination.heldOutPrediction Discrimination.bedroyaReportedFit ≡ false
retrospectiveFitRemainsNonPromoting = refl

stringTheoryPromotionRemainsBlocked :
  DarkDimension.stringTheoryPromotionPermitted
    DarkDimension.canonicalDarkDimensionPromotionStatus
  ≡ false
stringTheoryPromotionRemainsBlocked =
  DarkDimension.stringTheoryPromotionBlocked
