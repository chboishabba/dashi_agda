{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayAgdaParityValidation where

-- RED/GREEN parity surface for the retained Lean RequestProject.YangMills.Clay
-- tranche.  The production owners imported below must expose the same two
-- consumer routes: bounded physical energy form and source/clustering, both
-- entering one common continuum/OS mass-gap conclusion.

import DASHI.Physics.YangMills.YMClayBoundedFormParityExact as Form
import DASHI.Physics.YangMills.YMClayMassGapAssemblyParityExact as Assembly

open Form
open Assembly

boundedFormPackageAvailable : Set₁
boundedFormPackageAvailable = BoundedFormGapPackage

massGapConclusionAvailable : Set₁
massGapConclusionAvailable = MassGapConclusion

energyFormRouteAvailable : Set₁
energyFormRouteAvailable = EnergyFormRoute

sourceRouteAvailable : Set₁
sourceRouteAvailable = SourceClusteringRoute

commonContinuumRouteAvailable : Set₁
commonContinuumRouteAvailable = CommonContinuumOSRoute

-- The validation surface intentionally names the two headline assemblers.
energyAssemblerIsPresent : Set
energyAssemblerIsPresent = EnergyAssemblerPresent

sourceAssemblerIsPresent : Set
sourceAssemblerIsPresent = SourceAssemblerPresent
