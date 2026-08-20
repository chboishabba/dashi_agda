module DASHI.Geometry.AdaptiveWearableCompilerExact where

------------------------------------------------------------------------
-- ADAPTIVE WEARABLE / GARMENT FORMAL INTERFACE
--
-- This module is the project-neutral mathematical landing surface for the
-- SeaMeInIt architecture.  It does not import SeaMeInIt runtime code and does
-- not claim a cloth-physics theorem.  It makes the important domain objects
-- explicit enough to instantiate the generic governed-transition machinery:
-- body-relative ROM fields, panel actions, discrete curvature burden, material
-- and manufacturing observations, and consumer-indexed authority.
--
-- Geometry / fabrication references:
--
-- Oded Stein, Eitan Grinspun, Keenan Crane,
-- "Developability of Triangle Meshes", ACM TOG 37(4), 2018.
-- DOI: 10.1145/3197517.3201303.
--
-- Nico Pietroni, Corentin Dumery, Raphael Falque, Mark Liu,
-- Teresa A. Vidal-Calleja, Olga Sorkine-Hornung,
-- "Computational Pattern Making from 3D Garment Models", ACM TOG 41(4), 2022.
-- DOI: 10.1145/3528223.3530145.
--
-- David Cohen-Steiner and Jean-Marie Morvan,
-- "Restricted Delaunay Triangulations and Normal Cycle", SoCG 2003.
-- DOI: 10.1145/777792.777839.
--
-- Motion-driven design reference:
-- "Designing Personalized Garments with Body Movement",
-- Computer Graphics Forum, 2023. DOI: 10.1111/cgf.14728.
--
-- These sources calibrate the geometry and garment-design interpretation.  The
-- exact finite definitions below are DASHI constructions.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; _+_)
open import Agda.Builtin.String using (String)
open import Data.Nat using (_⊔_)

import DASHI.Core.ConsumerIndexedGovernedTransitionExact as Governed

------------------------------------------------------------------------
-- 1. Discrete ROM field: keep the sampled pose family explicit.  Probability
--    weights are not invented by the core; max/sum are exact empirical views.
------------------------------------------------------------------------

record EmpiricalROMField (Pose Site : Set) : Set₁ where
  constructor empiricalROMField
  field
    poses : List Pose
    value : Pose → Site → Nat
    fieldName : String
    provenance : List String

open EmpiricalROMField public

romMaxOver :
  ∀ {Pose Site} →
  (Pose → Site → Nat) → List Pose → Site → Nat
romMaxOver field [] site = zero
romMaxOver field (pose ∷ rest) site =
  field pose site ⊔ romMaxOver field rest site

romSumOver :
  ∀ {Pose Site} →
  (Pose → Site → Nat) → List Pose → Site → Nat
romSumOver field [] site = zero
romSumOver field (pose ∷ rest) site =
  field pose site + romSumOver field rest site

romMaximum :
  ∀ {Pose Site} → EmpiricalROMField Pose Site → Site → Nat
romMaximum field = romMaxOver (value field) (poses field)

romTotal :
  ∀ {Pose Site} → EmpiricalROMField Pose Site → Site → Nat
romTotal field = romSumOver (value field) (poses field)

------------------------------------------------------------------------
-- 2. Discrete curvature measure.  `angleBudget` is 2*pi for an interior vertex
--    or the appropriate boundary budget supplied by the mesh policy.  We keep
--    the scalar algebra abstract so exact rational/constructive-real backends
--    may instantiate it without forcing floating point into the theorem layer.
------------------------------------------------------------------------

record AdditiveDifferenceScalar (R : Set) : Set₁ where
  constructor additiveDifferenceScalar
  field
    zeroR : R
    _+R_ : R → R → R
    _-R_ : R → R → R

open AdditiveDifferenceScalar public

sumR :
  ∀ {R : Set} → AdditiveDifferenceScalar R → List R → R
sumR scalar [] = zeroR scalar
sumR scalar (x ∷ xs) = _+R_ scalar x (sumR scalar xs)

record DiscreteAngleDefect
    (Vertex R : Set)
    (scalar : AdditiveDifferenceScalar R) : Set₁ where
  constructor discreteAngleDefect
  field
    angleBudget : Vertex → R
    incidentAngles : Vertex → List R

open DiscreteAngleDefect public

vertexCurvature :
  ∀ {Vertex R}
    {scalar : AdditiveDifferenceScalar R} →
  DiscreteAngleDefect Vertex R scalar → Vertex → R
vertexCurvature {scalar = scalar} geometry vertex =
  _-R_ scalar
    (angleBudget geometry vertex)
    (sumR scalar (incidentAngles geometry vertex))

regionCurvature :
  ∀ {Vertex R}
    {scalar : AdditiveDifferenceScalar R} →
  DiscreteAngleDefect Vertex R scalar → List Vertex → R
regionCurvature {scalar = scalar} geometry vertices =
  sumR scalar (mapCurvature vertices)
  where
    mapCurvature : List Vertex → List R
    mapCurvature [] = []
    mapCurvature (v ∷ vs) = vertexCurvature geometry v ∷ mapCurvature vs

------------------------------------------------------------------------
-- Curvature is not claimed to disappear.  Manufacturing operators choose how
-- the planar-realisation burden is accommodated.
------------------------------------------------------------------------

data CurvatureAccommodation : Set where
  materialStrain : CurvatureAccommodation
  seamCut : CurvatureAccommodation
  dart : CurvatureAccommodation
  gusset : CurvatureAccommodation
  panelSubdivision : CurvatureAccommodation
  shapeApproximation : CurvatureAccommodation

record CurvatureDisposition (Region : Set) : Set where
  constructor curvatureDisposition
  field
    region : Region
    accommodation : CurvatureAccommodation
    evidenceReference : String

------------------------------------------------------------------------
-- 3. Panel action grammar and consumer roles.
------------------------------------------------------------------------

data PanelAction : Set where
  relief drain wedge dartAction lens gussetAction subdivide changeGrain
    changeMaterial : PanelAction

data WearableConsumer : Set where
  seamSearch manufacturing thermalRouting supportZoning : WearableConsumer

record WearableState (Body Panel Fabric Provenance : Set) : Set where
  constructor wearableState
  field
    body : Body
    panel : Panel
    fabric : Fabric
    provenance : Provenance

open WearableState public

record WearableObservation : Set where
  constructor wearableObservation
  field
    maxDistortion : Nat
    meanLikeDistortionNumerator : Nat
    foldoverCount : Nat
    materialBurden : Nat
    seamComplexity : Nat
    serialisable : Bool

open WearableObservation public

------------------------------------------------------------------------
-- 4. Generic compiler instance.  The runtime supplies actual geometry-changing
--    materialisation; the theorem layer supplies consumer/action observations
--    and authority via the shared governed-transition core.
------------------------------------------------------------------------

record AdaptiveWearableCompiler
    (Body Panel Fabric Provenance : Set) : Set₁ where
  constructor adaptiveWearableCompiler
  field
    materialise :
      PanelAction →
      WearableState Body Panel Fabric Provenance →
      WearableState Body Panel Fabric Provenance

    observe :
      WearableConsumer →
      WearableState Body Panel Fabric Provenance →
      WearableObservation

    declaredAction : WearableConsumer → PanelAction → Set

    authority :
      WearableConsumer →
      WearableState Body Panel Fabric Provenance →
      Governed.AuthorityDecision

open AdaptiveWearableCompiler public

asGovernedTransition :
  ∀ {Body Panel Fabric Provenance} →
  AdaptiveWearableCompiler Body Panel Fabric Provenance →
  Governed.ConsumerIndexedGovernedTransition
    (WearableState Body Panel Fabric Provenance)
    PanelAction WearableConsumer WearableObservation
asGovernedTransition compiler =
  Governed.consumerIndexedGovernedTransition
    (materialise compiler)
    (observe compiler)
    (declaredAction compiler)
    (authority compiler)

------------------------------------------------------------------------
-- Boundary: geometric developability, fabric manufacturability and downstream
-- thermal/support suitability are different consumers.  No theorem in this
-- file promotes one consumer's acceptance to another.
------------------------------------------------------------------------
