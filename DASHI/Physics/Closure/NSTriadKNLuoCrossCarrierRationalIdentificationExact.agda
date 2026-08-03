module DASHI.Physics.Closure.NSTriadKNLuoCrossCarrierRationalIdentificationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Loukas Grafakos; Rodolfo H. Torres.
-- Title: "A Multilinear Schur Test and Multiplier Operators".
-- Journal of Functional Analysis 187 (2001), 1--24.
-- DOI: 10.1006/jfan.2001.3804.
--
-- PURPOSE
-- Construct the rational physical weighted-Schur bridge from one mature
-- full-shell adapter and one scalar-to-rational transport.  The physical flux,
-- Schur constant, weighted energy and low-pass gradient are defined from the
-- transported full-shell quantities.  Their four cross-carrier equalities are
-- therefore definitional, not independent semantic assumptions.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSCompactGammaAnalyticClosureProgram as Closure
import DASHI.Physics.Closure.NSCompactGammaDifferentiatedTriadInstantiation as Triads
import DASHI.Physics.Closure.NSTriadKNLuoFullShellFluxAdapterExact as FullShell
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffFluxWeightedSchurExact as Flux

record RationalizedFullShellPhysicalBridgeInputs
    (program : Closure.CompactGammaAnalyticClosure)
    (K N : Nat) : Setω where
  field
    fullShellAdapter : FullShell.LuoFullShellFluxAdapter program K N

    scalarToRational : Scalar (Closure.arithmetic program) → ℚ

    orderTransport :
      ∀ {left right} →
      _≤_ (Closure.arithmetic program) left right →
      scalarToRational left ≤ scalarToRational right

    productMeaning :
      (left right : Scalar (Closure.arithmetic program)) →
      scalarToRational
        (FullShell.luoProduct fullShellAdapter left right)
      ≡ scalarToRational left * scalarToRational right

    atoms : List Flux.HermitianPairIncidenceAtom
    profilePartition : Flux.FourProfilePhysicalFluxPartition

    partitionUsesAtoms :
      Flux.allAtoms profilePartition ≡ atoms

    physicalFluxTriangleBound :
      scalarToRational
        (FullShell.absoluteCutoffFlux fullShellAdapter)
      ≤ Flux.sumAbsoluteFluxTerms atoms

    incidenceMajorantSumMeaning :
      Flux.sumIncidenceMajorants atoms
      ≡ scalarToRational
          (Triads.majorantActionOutput
            (Closure.differentiatedTriadsAt program K N))

    fluxNonnegative :
      0ℚ ≤ scalarToRational
        (FullShell.absoluteCutoffFlux fullShellAdapter)

    energyNonnegative :
      0ℚ ≤ scalarToRational
        (FullShell.cutoffEnergyMajorant fullShellAdapter)

    gradientNonnegative :
      0ℚ ≤ scalarToRational
        (FullShell.lowPassGradientInfinity fullShellAdapter)

    schurConstantNonnegative :
      0ℚ ≤ scalarToRational
        (FullShell.profileSchurConstant fullShellAdapter)

open RationalizedFullShellPhysicalBridgeInputs public

transportedMajorantSchurBound :
  (program : Closure.CompactGammaAnalyticClosure) →
  (K N : Nat) →
  (I : RationalizedFullShellPhysicalBridgeInputs program K N) →
  Flux.sumIncidenceMajorants (atoms I)
    ≤ scalarToRational I
        (FullShell.profileSchurConstant (fullShellAdapter I))
      * (scalarToRational I
          (FullShell.cutoffEnergyMajorant (fullShellAdapter I))
        * scalarToRational I
          (FullShell.lowPassGradientInfinity (fullShellAdapter I)))
transportedMajorantSchurBound program K N I
  rewrite incidenceMajorantSumMeaning I
        | productMeaning I
            (FullShell.profileSchurConstant (fullShellAdapter I))
            (FullShell.luoProduct (fullShellAdapter I)
              (FullShell.cutoffEnergyMajorant (fullShellAdapter I))
              (FullShell.lowPassGradientInfinity (fullShellAdapter I)))
        | productMeaning I
            (FullShell.cutoffEnergyMajorant (fullShellAdapter I))
            (FullShell.lowPassGradientInfinity (fullShellAdapter I)) =
  orderTransport I
    (FullShell.fullShellMajorantFactorsAsLuoProduct
      (fullShellAdapter I))

physicalBridgeFromFullShell :
  (program : Closure.CompactGammaAnalyticClosure) →
  (K N : Nat) →
  RationalizedFullShellPhysicalBridgeInputs program K N →
  Flux.PhysicalCutoffFluxWeightedSchurBridge
physicalBridgeFromFullShell program K N I = Flux.weighted-flux-bridge
  (atoms I)
  (profilePartition I)
  (scalarToRational I
    (FullShell.absoluteCutoffFlux (fullShellAdapter I)))
  (fluxNonnegative I)
  (scalarToRational I
    (FullShell.cutoffEnergyMajorant (fullShellAdapter I)))
  (scalarToRational I
    (FullShell.lowPassGradientInfinity (fullShellAdapter I)))
  (scalarToRational I
    (FullShell.profileSchurConstant (fullShellAdapter I)))
  (energyNonnegative I)
  (gradientNonnegative I)
  (schurConstantNonnegative I)
  (partitionUsesAtoms I)
  (physicalFluxTriangleBound I)
  (transportedMajorantSchurBound program K N I)

fullShellFluxMatchesPhysicalBridge :
  (program : Closure.CompactGammaAnalyticClosure) →
  (K N : Nat) →
  (I : RationalizedFullShellPhysicalBridgeInputs program K N) →
  scalarToRational I
    (FullShell.absoluteCutoffFlux (fullShellAdapter I))
  ≡ Flux.absoluteCutoffFlux
      (physicalBridgeFromFullShell program K N I)
fullShellFluxMatchesPhysicalBridge program K N I = refl

fullShellSchurConstantMatchesPhysicalBridge :
  (program : Closure.CompactGammaAnalyticClosure) →
  (K N : Nat) →
  (I : RationalizedFullShellPhysicalBridgeInputs program K N) →
  scalarToRational I
    (FullShell.profileSchurConstant (fullShellAdapter I))
  ≡ Flux.profileSchurConstant
      (physicalBridgeFromFullShell program K N I)
fullShellSchurConstantMatchesPhysicalBridge program K N I = refl

fullShellEnergyMatchesPhysicalBridge :
  (program : Closure.CompactGammaAnalyticClosure) →
  (K N : Nat) →
  (I : RationalizedFullShellPhysicalBridgeInputs program K N) →
  scalarToRational I
    (FullShell.cutoffEnergyMajorant (fullShellAdapter I))
  ≡ Flux.cutoffEnergyMajorant
      (physicalBridgeFromFullShell program K N I)
fullShellEnergyMatchesPhysicalBridge program K N I = refl

fullShellGradientMatchesPhysicalBridge :
  (program : Closure.CompactGammaAnalyticClosure) →
  (K N : Nat) →
  (I : RationalizedFullShellPhysicalBridgeInputs program K N) →
  scalarToRational I
    (FullShell.lowPassGradientInfinity (fullShellAdapter I))
  ≡ Flux.lowPassGradientInfinity
      (physicalBridgeFromFullShell program K N I)
fullShellGradientMatchesPhysicalBridge program K N I = refl

fourCrossCarrierEqualitiesClosed : Bool
fourCrossCarrierEqualitiesClosed = true

physicalWeightedSchurBridgeConstructorClosed : Bool
physicalWeightedSchurBridgeConstructorClosed = true

fourCrossCarrierEqualitiesClosedIsTrue :
  fourCrossCarrierEqualitiesClosed ≡ true
fourCrossCarrierEqualitiesClosedIsTrue = refl

physicalWeightedSchurBridgeConstructorClosedIsTrue :
  physicalWeightedSchurBridgeConstructorClosed ≡ true
physicalWeightedSchurBridgeConstructorClosedIsTrue = refl
