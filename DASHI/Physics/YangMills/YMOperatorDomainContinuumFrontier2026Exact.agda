module DASHI.Physics.YangMills.YMOperatorDomainContinuumFrontier2026Exact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.YangMills.YMAristotleOperatorReturn2026Exact as LeanReturn
import DASHI.Physics.YangMills.YMOperatorDomainContinuumSources2026Exact as Src

------------------------------------------------------------------------
-- BIDI return: Agda -> future Lean work.
--
-- The Lean tranche removes generic algebraic scaffolding, but its current
-- total-function and bounded-CLM carriers deliberately do not discharge the
-- physical unbounded Hamiltonian / continuum passage.  This module makes the
-- missing interfaces explicit so that future cross-prover work has a typed
-- target rather than an ambiguous prose phrase such as "gap stability".
------------------------------------------------------------------------

record AgdaToLeanInterface : Set where
  constructor agda-to-lean-interface
  field
    interfaceName : String
    motivatingSource : String
    requiredShape : String
    closedInCurrentLeanTranche : Bool
    boundedReading : String

open AgdaToLeanInterface public

domainAwareHamiltonianInterface : AgdaToLeanInterface
domainAwareHamiltonianInterface = agda-to-lean-interface
  "DomainAwareHamiltonian"
  "Tosio Kato, Perturbation Theory for Linear Operators, DOI 10.1007/978-3-642-66282-9"
  "carrier H; domain D(H); operator H : D(H) -> carrier; common invariant dense core; gauge-action invariance; symmetry/self-adjointness on the stated domain; quotient compatibility of domain and action"
  false
  "Current Lean uniqueness allows total H -> H generators with no boundedness hypothesis, but does not formalize a partial operator domain."

closedFormContinuumInterface : AgdaToLeanInterface
closedFormContinuumInterface = agda-to-lean-interface
  "ClosedFormOrResolventGapTransport"
  "Tosio Kato, Perturbation Theory for Linear Operators, DOI 10.1007/978-3-642-66282-9; Umberto Mosco, Convergence of Convex Sets and of Solutions of Variational Inequalities, DOI 10.1016/0001-8708(69)90009-7"
  "closed semibounded quadratic forms or closed operators; a specified convergence mode such as Mosco / strong resolvent / norm resolvent; identification of the limiting physical Hamiltonian; theorem transporting the positive lower bound above the vacuum"
  false
  "MassGapFormTransport closes only pointwise strong-limit preservation for bounded continuous linear maps E ->L[C] E."

osReconstructionIdentificationInterface : AgdaToLeanInterface
osReconstructionIdentificationInterface = agda-to-lean-interface
  "OSReconstructedEvolutionIdentification"
  "Konrad Osterwalder and Robert Schrader, Axioms for Euclidean Green's Functions I/II, DOI 10.1007/BF01645738 and 10.1007/BF01608978"
  "construct continuum Schwinger functions satisfying the required OS package; reconstruct the Hilbert-space dynamics; identify that evolution with the selected Yang--Mills Hamiltonian evolution on the physical carrier/common core"
  false
  "Generator uniqueness can consume equality of evolutions once supplied; it does not prove the equality of the Yang--Mills and OS-reconstructed evolutions."

agdaToLeanInterfaces : List AgdaToLeanInterface
agdaToLeanInterfaces =
  domainAwareHamiltonianInterface ∷
  closedFormContinuumInterface ∷
  osReconstructionIdentificationInterface ∷ []

------------------------------------------------------------------------
-- Exact frontier ledger.
------------------------------------------------------------------------

record YMOperatorContinuumFrontier : Set where
  constructor ym-operator-continuum-frontier
  field
    representationIdentificationClosed : Bool
    defectTelescopeClosed : Bool
    principalChartAdmissionClosed : Bool
    nullQuotientSeparationClosed : Bool
    symmetryImpliesNullPreservationClosedForTotalLinearMaps : Bool
    generatorUniquenessClosedWithoutBoundednessHypothesisOnTotalMaps : Bool
    gaugeInvariantL2CarrierClosed : Bool
    carrierNonVacuityClosed : Bool
    boundedStrongLimitFormGapTransportClosed : Bool

    balabanSelectedBackgroundAndStoredBondBudgetClosed : Bool
    literalYMActionVariationHamiltonianIdentificationClosed : Bool
    genuinePartialDomainHamiltonianFormalized : Bool
    commonInvariantDensePhysicalCoreConstructed : Bool
    ymEvolutionEqualsOSReconstructedEvolutionClosed : Bool
    unboundedClosedFormOrResolventGapTransportClosed : Bool
    finiteToContinuumYMConstructionClosed : Bool
    continuumOSWightmanPackageClosed : Bool
    clayPromotionClosed : Bool

open YMOperatorContinuumFrontier public

canonicalYMOperatorContinuumFrontier : YMOperatorContinuumFrontier
canonicalYMOperatorContinuumFrontier = ym-operator-continuum-frontier
  true true true true true true true true true
  false false false false false false false false false

------------------------------------------------------------------------
-- Regression theorems: the cross-pollination must not accidentally identify
-- the bounded theorem with the physical unbounded continuum theorem.
------------------------------------------------------------------------

boundedGapTransportClosedIsTrue :
  boundedStrongLimitFormGapTransportClosed canonicalYMOperatorContinuumFrontier ≡ true
boundedGapTransportClosedIsTrue = refl

unboundedGapTransportClosedIsFalse :
  unboundedClosedFormOrResolventGapTransportClosed canonicalYMOperatorContinuumFrontier ≡ false
unboundedGapTransportClosedIsFalse = refl

genuinePartialDomainHamiltonianFormalizedIsFalse :
  genuinePartialDomainHamiltonianFormalized canonicalYMOperatorContinuumFrontier ≡ false
genuinePartialDomainHamiltonianFormalizedIsFalse = refl

clayPromotionClosedIsFalse :
  clayPromotionClosed canonicalYMOperatorContinuumFrontier ≡ false
clayPromotionClosedIsFalse = refl

------------------------------------------------------------------------
-- Cross-prover ownership firewalls inherited from the Lean return.
------------------------------------------------------------------------

leanGeneratorReturnNotTransported :
  LeanReturn.transportedIntoAgda LeanReturn.generatorUniquenessStatus ≡ false
leanGeneratorReturnNotTransported = refl

leanMassGapReturnIsBoundedOperatorTheorem :
  LeanReturn.boundedContinuousOperatorTheorem LeanReturn.massGapStrongLimitStatus ≡ true
leanMassGapReturnIsBoundedOperatorTheorem = refl

leanMassGapReturnIsNotFullUnboundedDomainTheorem :
  LeanReturn.fullUnboundedDomainTheorem LeanReturn.massGapStrongLimitStatus ≡ false
leanMassGapReturnIsNotFullUnboundedDomainTheorem = refl

------------------------------------------------------------------------
-- Source-presence witnesses: these are metadata inhabitants, not mathematical
-- proofs of the open interfaces.
------------------------------------------------------------------------

katoSourcePresent : Src.LiteratureSource
katoSourcePresent = Src.katoPerturbationTheory

moscoSourcePresent : Src.LiteratureSource
moscoSourcePresent = Src.moscoVariationalConvergence
