module DASHI.Moonshine.OggSSPP2Gamma0FourUniqueSupersingularSubgroupSeparationExact where

------------------------------------------------------------------------
-- p=2 GAMMA_0(4): UNIQUE RAW SUPERSINGULAR CYCLIC SUBGROUP
-- VERSUS TEN-STATE RESIDUAL TARGET
--
-- EXTERNAL SOURCE CONTEXT
--
-- Massimo Bertolini, Henri Darmon, Kartik Prasanna,
-- with an appendix by Brian Conrad,
-- "p-adic L-functions and the coniveau filtration on Chow groups",
-- J. Reine Angew. Math. 731 (2017), 21--86.
-- DOI: 10.1515/crelle-2014-0150.
--
-- Source statement used:
-- every supersingular elliptic curve over an algebraic closure of F_p admits
-- a unique Drinfeld cyclic subgroup scheme of order p^r, namely the kernel of
-- the r-fold relative Frobenius.
--
-- Specializing p=2, r=2:
--
--   unique cyclic rank-4 subgroup = ker(F^2).
--
-- DASHI CONSEQUENCE
--
-- The ten-state p=2 residual target CANNOT be interpreted as ten distinct raw
-- cyclic order-4 subgroup choices on one fixed supersingular elliptic curve.
-- Any ten-state arithmetic recognition must therefore use finer data:
-- deformation/marking/inertia/stacky provenance over the unique raw subgroup.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Moonshine.OggSSPP2BalancedTernaryPuncturedPlaneExact as Target
import DASHI.Moonshine.OggSSPP2Gamma0FourMarkedSubgroupSchemeSourceExact as Gamma0
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Source-calibrated raw subgroup count.
------------------------------------------------------------------------

supersingularGamma0FourRawCyclicSubgroupCount : Nat
supersingularGamma0FourRawCyclicSubgroupCount = 1

supersingularGamma0FourRawCyclicSubgroupCountIsOne :
  supersingularGamma0FourRawCyclicSubgroupCount ≡ 1
supersingularGamma0FourRawCyclicSubgroupCountIsOne = refl

selectedResidualTargetCount : Nat
selectedResidualTargetCount =
  Target.duplicatedCentreStateCount

selectedResidualTargetCountIsTen :
  selectedResidualTargetCount ≡ 10
selectedResidualTargetCountIsTen = refl

oneDoesNotEqualTen :
  supersingularGamma0FourRawCyclicSubgroupCount
  ≡ selectedResidualTargetCount ->
  ⊥
oneDoesNotEqualTen ()

------------------------------------------------------------------------
-- 2. Typed unique-subgroup source fact.
------------------------------------------------------------------------

data SupersingularRawGamma0FourSubgroup : Set where
  kerFrobeniusSquared :
    SupersingularRawGamma0FourSubgroup

rawSubgroupCount : Nat
rawSubgroupCount = 1

rawSubgroupIsFrobeniusSquaredKernel :
  (subgroup : SupersingularRawGamma0FourSubgroup) ->
  subgroup ≡ kerFrobeniusSquared
rawSubgroupIsFrobeniusSquaredKernel kerFrobeniusSquared = refl

------------------------------------------------------------------------
-- 3. Recognition consequences.
------------------------------------------------------------------------

data TenResidualStatesAreTenRawCyclicSubgroups : Set where
data OneRawSubgroupCountCreatesTenComponentRecognition : Set where

tenResidualStatesAreNotTenRawCyclicSubgroups :
  TenResidualStatesAreTenRawCyclicSubgroups -> ⊥
tenResidualStatesAreNotTenRawCyclicSubgroups ()

oneRawSubgroupCountDoesNotCreateTenComponentRecognition :
  OneRawSubgroupCountCreatesTenComponentRecognition -> ⊥
oneRawSubgroupCountDoesNotCreateTenComponentRecognition ()

data RequiredExtraArithmeticDatum : Set where
  deformationMarking :
    RequiredExtraArithmeticDatum
  inertiaOrAutomorphismMarking :
    RequiredExtraArithmeticDatum
  stackyOrLocalModelBranch :
    RequiredExtraArithmeticDatum
  otherArithmeticResidual :
    RequiredExtraArithmeticDatum

------------------------------------------------------------------------
-- 4. Acquisition refinement.
------------------------------------------------------------------------

record MarkingOverUniqueGamma0FourSubgroup : Set₁ where
  field
    MarkedState : Set

    rawSubgroup :
      MarkedState ->
      SupersingularRawGamma0FourSubgroup

    everyStateLiesOverKerFrobeniusSquared :
      (state : MarkedState) ->
      rawSubgroup state ≡ kerFrobeniusSquared

    residualDatum :
      MarkedState ->
      RequiredExtraArithmeticDatum

    provenanceFromArithmeticModuli : Bool
    provenanceFromArithmeticModuliIsTrue :
      provenanceFromArithmeticModuli ≡ true

open MarkingOverUniqueGamma0FourSubgroup public

------------------------------------------------------------------------
-- 5. Attribution boundary.
------------------------------------------------------------------------

sourceReference : String
sourceReference =
  "Bertolini-Darmon-Prasanna, appendix by Brian Conrad, J. Reine Angew. Math. 731 (2017), DOI 10.1515/crelle-2014-0150"

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryCrossModuleInference

record UniqueSupersingularGamma0FourSubgroupBoundary : Set where
  constructor unique-supersingular-gamma0-four-subgroup-boundary
  field
    sourceBackedUniqueDrinfeldCyclicSubgroupUsed : Bool
    p2r2SpecializationIsKerFrobeniusSquared : Bool
    rawSubgroupChoiceCountIsOne : Bool
    residualTargetCountIsTen : Bool
    tenResidualStatesIdentifiedWithRawSubgroupChoices : Bool
    extraArithmeticMarkingRequired : Bool
    actualExtraArithmeticMarkingConstructed : Bool

canonicalUniqueSupersingularGamma0FourSubgroupBoundary :
  UniqueSupersingularGamma0FourSubgroupBoundary
canonicalUniqueSupersingularGamma0FourSubgroupBoundary =
  unique-supersingular-gamma0-four-subgroup-boundary
    true true true true false true false
