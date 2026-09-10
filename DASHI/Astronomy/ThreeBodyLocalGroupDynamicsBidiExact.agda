module DASHI.Astronomy.ThreeBodyLocalGroupDynamicsBidiExact where

open import DASHI.Core.Prelude
open import DASHI.Core.AttributedSourceCore
open import DASHI.Astronomy.LocalGroupDigitalTwinBoundaryExact
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Reuse of prior three-body content for the Local Group dynamics lane.
--
-- This module deliberately separates: (1) exact celestial-mechanics source
-- facts, (2) structural analogies used elsewhere in DASHI, and (3) actual
-- Local Group dynamical obligations.  No analogy is allowed to pay a physical
-- Local Group force-law or stability claim.
------------------------------------------------------------------------

chencinerMontgomery2000 : AttributedSource
chencinerMontgomery2000 =
  mkDOISource
    "Alain Chenciner; Richard Montgomery"
    "A remarkable periodic solution of the three-body problem in the case of equal masses"
    "Annals of Mathematics 152(3):881-901"
    "2000"
    "10.2307/2661357"
    "https://doi.org/10.2307/2661357"
    academicArticleSource
    "primary source for the equal-mass planar figure-eight choreography; retained as a celestial-mechanics source, not as evidence for Local Group trajectories"
    publicAttribution

record ThreeBodySourceFact : Set where
  constructor threeBodySourceFact
  field
    source : AttributedSource
    factLabel : String
    factText : String
    localGroupApplicationStatus : String

open ThreeBodySourceFact public

figureEightChoreography : ThreeBodySourceFact
figureEightChoreography =
  threeBodySourceFact
    chencinerMontgomery2000
    "figure-eight choreography"
    "three equal Newtonian point masses in the plane follow the same fixed figure-eight curve with cyclic phase displacement and zero total angular momentum"
    "structural precedent only; does not imply MW/M31/M33 or MW/LMC/Sgr follow a choreography"

lagrangeRelativeEquilibrium : ThreeBodySourceFact
lagrangeRelativeEquilibrium =
  threeBodySourceFact
    chencinerMontgomery2000
    "Lagrange relative equilibrium"
    "three bodies can form a rigid equilateral-triangle configuration rotating uniformly about the centre of mass"
    "exact source fact about a special Newtonian three-body solution; Local Group masses/configuration are not assumed to satisfy it"

------------------------------------------------------------------------
-- Prior DASHI three-body ideas, recovered from project notes.
------------------------------------------------------------------------

data PriorThreeBodyIdeaKind : Set where
  z3PhaseAnalogy : PriorThreeBodyIdeaKind
  equilateralStabilityAnalogy : PriorThreeBodyIdeaKind
  eclipseThreeBodyObservation : PriorThreeBodyIdeaKind
  kamResonanceAnalogy : PriorThreeBodyIdeaKind

record PriorThreeBodyIdea : Set where
  constructor priorThreeBodyIdea
  field
    ideaKind : PriorThreeBodyIdeaKind
    priorStatement : String
    scientificStatus : String
    reusablePart : String

open PriorThreeBodyIdea public

priorFigureEightZ3 : PriorThreeBodyIdea
priorFigureEightZ3 =
  priorThreeBodyIdea
    z3PhaseAnalogy
    "figure-eight choreography compared with a Z/3Z cyclic phase structure"
    "the choreography has a genuine cyclic permutation/phase symmetry; identifying this with unrelated DASHI generation carriers is an analogy unless an explicit isomorphism is proved"
    "reuse cyclic-indexing and phase-permutation structure, not physical gravitational conclusions"

priorLagrangeTriangle : PriorThreeBodyIdea
priorLagrangeTriangle =
  priorThreeBodyIdea
    equilateralStabilityAnalogy
    "L4/L5 or equilateral configurations compared with three-slot stability"
    "equilateral relative equilibria are exact celestial mechanics; stability depends on masses/linearized dynamics and is not inherited by an abstract three-slot representation"
    "reuse equilibrium/stability obligation shape only"

priorEclipseLane : PriorThreeBodyIdea
priorEclipseLane =
  priorThreeBodyIdea
    eclipseThreeBodyObservation
    "Sun-Earth-Moon eclipses treated as a three-body constraint problem with lunar inclination, nodes, and long-period recurrence"
    "the Moon's nodal regression is about 18.6 years; the Saros itself is about 18 years 11 days 8 hours and must not be identified with the 18.6-year nodal period"
    "reuse distinction between instantaneous geometric alignment and long-time dynamical stability"

priorKAMLane : PriorThreeBodyIdea
priorKAMLane =
  priorThreeBodyIdea
    kamResonanceAnalogy
    "KAM survival of non-resonant invariant tori compared with refinement/resonance avoidance"
    "KAM uses Diophantine non-resonance conditions on real frequency vectors; calling the condition itself 'precisely p-adic' is too strong without a separate theorem"
    "reuse typed split: near-integrable dynamics / resonance condition / perturbation size / surviving invariant structure"

------------------------------------------------------------------------
-- Local Group: which concrete three-body reductions are scientifically useful?
------------------------------------------------------------------------

data LocalGroupThreeBodySystem : Set where
  mwM31M33 : LocalGroupThreeBodySystem
  mwLmcSagittarius : LocalGroupThreeBodySystem
  mwM31Lmc : LocalGroupThreeBodySystem
  fullNBodyLocalGroup : LocalGroupThreeBodySystem

record LocalGroupThreeBodyDemand : Set where
  constructor localGroupThreeBodyDemand
  field
    system : LocalGroupThreeBodySystem
    bodies : String
    physicalQuestion : String
    exactInputsNeeded : String
    reductionStatus : String

open LocalGroupThreeBodyDemand public

mwM31M33Demand : LocalGroupThreeBodyDemand
mwM31M33Demand =
  localGroupThreeBodyDemand
    mwM31M33
    "Milky Way / M31 / M33"
    "mutual orbital history, barycentre motion, close-approach/merger forecasts, and M33 backreaction"
    "source-bound 6D states; mass profiles and uncertainties; dynamical-friction prescription; extended-halo potentials; integration convention"
    "high-value reduced subsystem, but not an isolated point-mass three-body problem"

mwLmcSgrDemand : LocalGroupThreeBodyDemand
mwLmcSgrDemand =
  localGroupThreeBodyDemand
    mwLmcSagittarius
    "Milky Way / LMC / Sagittarius"
    "time-dependent perturbation of the Sagittarius stream by the LMC plus Milky-Way reflex motion"
    "Vasiliev-model artifact identity; MW and LMC potentials; Sgr progenitor/state; non-inertial acceleration; integration history"
    "directly motivated by Vasiliev-Belokurov-Erkal; best immediate bridge from first-light state reconstruction to dynamics"

mwM31LmcDemand : LocalGroupThreeBodyDemand
mwM31LmcDemand =
  localGroupThreeBodyDemand
    mwM31Lmc
    "Milky Way / M31 / LMC"
    "motion of the adopted Local Group frame/barycentre when a massive LMC perturbs the Milky Way"
    "mass hierarchy; present 6D states; chosen barycentric convention; extended potentials"
    "useful frame-systematics reduction, not automatically the dominant physical three-body subsystem"

fullLocalGroupDemand : LocalGroupThreeBodyDemand
fullLocalGroupDemand =
  localGroupThreeBodyDemand
    fullNBodyLocalGroup
    "Milky Way / M31 / M33 / LMC / SMC / Sagittarius / dwarf population"
    "source-bound time evolution of the Virtual Observatory"
    "all retained massive-body states, mass/potential uncertainties, encounter/interaction model, numerical integrator and update/assimilation receipts"
    "actual digital-twin target; reduced three-body systems are diagnostics and validation slices"

------------------------------------------------------------------------
-- Firewalls carried from the earlier content into astronomy.
------------------------------------------------------------------------

threeBodyAnalogyImpliesLocalGroupDynamics : Bool
threeBodyAnalogyImpliesLocalGroupDynamics = false

threeBodyAnalogyImpliesLocalGroupDynamicsIsFalse :
  threeBodyAnalogyImpliesLocalGroupDynamics ≡ false
threeBodyAnalogyImpliesLocalGroupDynamicsIsFalse = refl

lagrangeGeometryImpliesStability : Bool
lagrangeGeometryImpliesStability = false

lagrangeGeometryImpliesStabilityIsFalse :
  lagrangeGeometryImpliesStability ≡ false
lagrangeGeometryImpliesStabilityIsFalse = refl

threeBodyReductionImpliesNBodyAdequacy : Bool
threeBodyReductionImpliesNBodyAdequacy = false

threeBodyReductionImpliesNBodyAdequacyIsFalse :
  threeBodyReductionImpliesNBodyAdequacy ≡ false
threeBodyReductionImpliesNBodyAdequacyIsFalse = refl

pointMassModelImpliesExtendedGalaxyAdequacy : Bool
pointMassModelImpliesExtendedGalaxyAdequacy = false

pointMassModelImpliesExtendedGalaxyAdequacyIsFalse :
  pointMassModelImpliesExtendedGalaxyAdequacy ≡ false
pointMassModelImpliesExtendedGalaxyAdequacyIsFalse = refl

kamAnalogyImportsPadicTheorem : Bool
kamAnalogyImportsPadicTheorem = false

kamAnalogyImportsPadicTheoremIsFalse :
  kamAnalogyImportsPadicTheorem ≡ false
kamAnalogyImportsPadicTheoremIsFalse = refl

------------------------------------------------------------------------
-- Preferred first dynamical weld.
------------------------------------------------------------------------

preferredFirstThreeBodyWeld : LocalGroupThreeBodyDemand
preferredFirstThreeBodyWeld = mwLmcSgrDemand

preferredFirstThreeBodyWeldPaysValidatedTwin : Bool
preferredFirstThreeBodyWeldPaysValidatedTwin = false

preferredFirstThreeBodyWeldPaysValidatedTwinIsFalse :
  preferredFirstThreeBodyWeldPaysValidatedTwin ≡ false
preferredFirstThreeBodyWeldPaysValidatedTwinIsFalse = refl
