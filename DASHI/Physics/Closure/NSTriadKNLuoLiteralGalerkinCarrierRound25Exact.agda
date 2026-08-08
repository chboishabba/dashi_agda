module DASHI.Physics.Closure.NSTriadKNLuoLiteralGalerkinCarrierRound25Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Round 24 treated L3 as one undifferentiated open node.  The repository
-- already contained the literal cutoff cube, duplicate-free resonant triad
-- enumeration, output fibres, reality closure, exact Leray coefficient and
-- coefficientwise physical/Fourier equivalence.  This file turns those pieces
-- into one theorem-bearing finite-carrier certificate and adds the previously
-- missing proof that every output fibre is duplicate-free.
--
-- The remaining L3 leaf is analytic rather than combinatorial: construct the
-- time-dependent finite-dimensional ODE solution over the chosen continuum
-- real carrier and prove propagation of the reality/transversality constraints.
-- No ODE-existence claim is smuggled into this certificate.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Equation
import DASHI.Physics.Closure.NSTriadKNFiniteTrigonometricGalerkinEquivalence as Equivalence

open Cube using (_∈_; _∉_; NoDuplicates; unique[]; unique∷)

------------------------------------------------------------------------
-- Filtering a duplicate-free triad enumeration by one output mode preserves
-- duplicate-freeness.  This is the exact list theorem missing from the prior
-- output-fibre implementation.
------------------------------------------------------------------------

filterOutputMemberOriginal :
  ∀ {output items τ} →
  τ ∈ Output.filterOutput output items →
  τ ∈ items
filterOutputMemberOriginal {items = []} ()
filterOutputMemberOriginal {output} {items = head ∷ tail} {τ} member
  with Output.modeEqual (Physical.k head) output
... | true with member
...   | Cube.here equality = Cube.here equality
...   | Cube.there rest =
      Cube.there (filterOutputMemberOriginal rest)
... | false =
      Cube.there (filterOutputMemberOriginal member)

filterOutputNoDuplicates :
  (output : Z3.FourierMode) →
  ∀ {items} →
  NoDuplicates items →
  NoDuplicates (Output.filterOutput output items)
filterOutputNoDuplicates output unique[] = unique[]
filterOutputNoDuplicates output
  (unique∷ {x = head} {xs = tail} headFresh rest)
  with Output.modeEqual (Physical.k head) output
... | true =
  unique∷ filteredHeadFresh (filterOutputNoDuplicates output rest)
  where
  filteredHeadFresh :
    head ∉ Output.filterOutput output tail
  filteredHeadFresh member =
    headFresh (filterOutputMemberOriginal member)
... | false = filterOutputNoDuplicates output rest

physicalOutputFiberNoDuplicates :
  (cutoff : Nat) →
  (output : Z3.FourierMode) →
  NoDuplicates (Output.physicalOutputFiber cutoff output)
physicalOutputFiberNoDuplicates cutoff output =
  filterOutputNoDuplicates output
    (Physical.physicalTriadEnumerationNoDuplicates cutoff)

physicalOutputFiberCutoffSound :
  ∀ {cutoff output τ} →
  τ ∈ Output.physicalOutputFiber cutoff output →
  Physical.PhysicalTriadInCutoff cutoff τ
physicalOutputFiberCutoffSound member =
  Physical.physicalTriadEnumerationCutoffSound
    (filterOutputMemberOriginal member)

physicalOutputFiberResonanceSound :
  ∀ {cutoff output τ} →
  τ ∈ Output.physicalOutputFiber cutoff output →
  Z3.addMode (Physical.p τ) (Physical.q τ) ≡ Physical.k τ
physicalOutputFiberResonanceSound member =
  Physical.physicalTriadEnumerationResonanceSound
    (filterOutputMemberOriginal member)

------------------------------------------------------------------------
-- One exact certificate for every finite cutoff.
------------------------------------------------------------------------

record LiteralGalerkinCarrierCertificate (cutoff : Nat) : Set where
  constructor literal-galerkin-carrier-certificate
  field
    enumerationDuplicateFree :
      NoDuplicates (Physical.physicalTriadEnumeration cutoff)

    enumerationResonanceSound :
      ∀ {τ} →
      τ ∈ Physical.physicalTriadEnumeration cutoff →
      Z3.addMode (Physical.p τ) (Physical.q τ) ≡ Physical.k τ

    enumerationCutoffSound :
      ∀ {τ} →
      τ ∈ Physical.physicalTriadEnumeration cutoff →
      Physical.PhysicalTriadInCutoff cutoff τ

    enumerationComplete :
      ∀ {τ} →
      Physical.PhysicalTriadInCutoff cutoff τ →
      Physical.PhysicalTriadEnumerationHit cutoff τ

    literalRealityPolicy :
      Physical.PhysicalTriadRealityPolicy cutoff

    everyOutputFiberDuplicateFree :
      ∀ output →
      NoDuplicates (Output.physicalOutputFiber cutoff output)

    everyOutputFiberSound :
      ∀ {output τ} →
      τ ∈ Output.physicalOutputFiber cutoff output →
      Physical.k τ ≡ output

    everyOutputFiberComplete :
      ∀ {output τ} →
      τ ∈ Physical.physicalTriadEnumeration cutoff →
      Physical.k τ ≡ output →
      τ ∈ Output.physicalOutputFiber cutoff output

open LiteralGalerkinCarrierCertificate public

literalGalerkinCarrierCertificate :
  (cutoff : Nat) → LiteralGalerkinCarrierCertificate cutoff
literalGalerkinCarrierCertificate cutoff =
  literal-galerkin-carrier-certificate
    (Physical.physicalTriadEnumerationNoDuplicates cutoff)
    Physical.physicalTriadEnumerationResonanceSound
    Physical.physicalTriadEnumerationCutoffSound
    Physical.physicalTriadEnumerationComplete
    (Physical.literalCutoffRealityPolicy cutoff)
    (physicalOutputFiberNoDuplicates cutoff)
    Output.physicalOutputFiberSound
    Output.physicalOutputFiberComplete

------------------------------------------------------------------------
-- The already-proved coefficient identity is re-exported at the exact point
-- where L3 needs it: the projected physical Fourier coefficient and the
-- coefficient ODE use the same literal output-indexed resonant fibre.
------------------------------------------------------------------------

projectedPhysicalCoefficientEqualsGalerkinODE :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Equation.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode) →
  Equivalence.projectedPhysicalRightHandSide system output
  ≡ Equation.projectedNonlinearity system output
projectedPhysicalCoefficientEqualsGalerkinODE =
  Equivalence.physicalProjectionEqualsProjectedODECoefficient

------------------------------------------------------------------------
-- Fail-closed status: the exact finite carrier is complete, while the
-- continuum-valued finite ODE existence/constraint-propagation instance is a
-- separate analytic producer.
------------------------------------------------------------------------

record LiteralGalerkinL3Round25Status : Set where
  constructor literal-galerkin-l3-round25-status
  field
    cutoffCubeEnumerationExact : Bool
    resonantEnumerationSoundComplete : Bool
    outputFibresSoundCompleteDuplicateFree : Bool
    realityCarrierClosedUnderNegation : Bool
    projectedPhysicalCoefficientIdentified : Bool
    finiteDimensionalODEExistenceInstantiated : Bool
    realityAndTransversalityPropagationInstantiated : Bool

open LiteralGalerkinL3Round25Status public

canonicalLiteralGalerkinL3Round25Status : LiteralGalerkinL3Round25Status
canonicalLiteralGalerkinL3Round25Status =
  literal-galerkin-l3-round25-status
    true true true true true false false
