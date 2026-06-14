module DASHI.Physics.Closure.StoneHbarDimensionlessActionBridge where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.StoneSISecondTimeParameterBridge as StoneTime
import DASHI.Physics.Closure.StoneTheoremCarrierReceipt as StoneReceipt

------------------------------------------------------------------------
-- Stone/Schrodinger dimensionless action bridge.
--
-- This module is a local, fail-closed bridge for the exponent in
--
--   U(t) = exp(-i H t / hbar).
--
-- The only internal construction here is SI-dimension arithmetic:
-- energy times time has the same dimension as hbar, and multiplication by
-- the inverse hbar dimension gives a dimensionless exponent.  No Real
-- carrier, hbar authority payload, Stone theorem authority, dense physical
-- domain, spectral calculus, or physical promotion token is constructed.

data SIExponent : Set where
  minus2 : SIExponent
  minus1 : SIExponent
  zeroE : SIExponent
  plus1 : SIExponent
  plus2 : SIExponent

addExponent : SIExponent -> SIExponent -> SIExponent
addExponent minus2 minus2 = minus2
addExponent minus2 minus1 = minus2
addExponent minus2 zeroE = minus2
addExponent minus2 plus1 = minus1
addExponent minus2 plus2 = zeroE
addExponent minus1 minus2 = minus2
addExponent minus1 minus1 = minus2
addExponent minus1 zeroE = minus1
addExponent minus1 plus1 = zeroE
addExponent minus1 plus2 = plus1
addExponent zeroE e = e
addExponent plus1 minus2 = minus1
addExponent plus1 minus1 = zeroE
addExponent plus1 zeroE = plus1
addExponent plus1 plus1 = plus2
addExponent plus1 plus2 = plus2
addExponent plus2 minus2 = zeroE
addExponent plus2 minus1 = plus1
addExponent plus2 zeroE = plus2
addExponent plus2 plus1 = plus2
addExponent plus2 plus2 = plus2

record SIBaseDimensionVector : Set where
  field
    length : SIExponent
    mass : SIExponent
    time : SIExponent
    current : SIExponent
    temperature : SIExponent
    amount : SIExponent
    luminousIntensity : SIExponent

open SIBaseDimensionVector public

dimensionlessVector : SIBaseDimensionVector
dimensionlessVector =
  record
    { length = zeroE
    ; mass = zeroE
    ; time = zeroE
    ; current = zeroE
    ; temperature = zeroE
    ; amount = zeroE
    ; luminousIntensity = zeroE
    }

energyDimension : SIBaseDimensionVector
energyDimension =
  record
    { length = plus2
    ; mass = plus1
    ; time = minus2
    ; current = zeroE
    ; temperature = zeroE
    ; amount = zeroE
    ; luminousIntensity = zeroE
    }

timeDimension : SIBaseDimensionVector
timeDimension =
  record
    { length = zeroE
    ; mass = zeroE
    ; time = plus1
    ; current = zeroE
    ; temperature = zeroE
    ; amount = zeroE
    ; luminousIntensity = zeroE
    }

hbarActionDimension : SIBaseDimensionVector
hbarActionDimension =
  record
    { length = plus2
    ; mass = plus1
    ; time = minus1
    ; current = zeroE
    ; temperature = zeroE
    ; amount = zeroE
    ; luminousIntensity = zeroE
    }

inverseHbarActionDimension : SIBaseDimensionVector
inverseHbarActionDimension =
  record
    { length = minus2
    ; mass = minus1
    ; time = plus1
    ; current = zeroE
    ; temperature = zeroE
    ; amount = zeroE
    ; luminousIntensity = zeroE
    }

addDimension :
  SIBaseDimensionVector ->
  SIBaseDimensionVector ->
  SIBaseDimensionVector
addDimension x y =
  record
    { length = addExponent (length x) (length y)
    ; mass = addExponent (mass x) (mass y)
    ; time = addExponent (time x) (time y)
    ; current = addExponent (current x) (current y)
    ; temperature = addExponent (temperature x) (temperature y)
    ; amount = addExponent (amount x) (amount y)
    ; luminousIntensity =
        addExponent (luminousIntensity x) (luminousIntensity y)
    }

hamiltonianTimesTimeDimension : SIBaseDimensionVector
hamiltonianTimesTimeDimension =
  addDimension energyDimension timeDimension

stoneExponentDimension : SIBaseDimensionVector
stoneExponentDimension =
  addDimension hamiltonianTimesTimeDimension inverseHbarActionDimension

hamiltonianTimesTimeHasHbarDimension :
  hamiltonianTimesTimeDimension ≡ hbarActionDimension
hamiltonianTimesTimeHasHbarDimension =
  refl

stoneExponentDimensionless :
  stoneExponentDimension ≡ dimensionlessVector
stoneExponentDimensionless =
  refl

record DimensionedStoneQuantity : Set where
  field
    symbol : String
    meaning : String
    dimension : SIBaseDimensionVector
    dimensionNarrative : String

open DimensionedStoneQuantity public

hamiltonianEnergyQuantity : DimensionedStoneQuantity
hamiltonianEnergyQuantity =
  record
    { symbol = "H"
    ; meaning = "self-adjoint Hamiltonian energy operator"
    ; dimension = energyDimension
    ; dimensionNarrative = "energy has SI dimension kg m^2 s^-2"
    }

stoneTimeQuantity : DimensionedStoneQuantity
stoneTimeQuantity =
  record
    { symbol = "t"
    ; meaning = "physical time parameter measured in SI seconds"
    ; dimension = timeDimension
    ; dimensionNarrative = "time has SI dimension s"
    }

hbarQuantity : DimensionedStoneQuantity
hbarQuantity =
  record
    { symbol = "hbar"
    ; meaning = "reduced Planck action constant h / (2 pi)"
    ; dimension = hbarActionDimension
    ; dimensionNarrative = "action has SI dimension kg m^2 s^-1"
    }

stoneExponentQuantity : DimensionedStoneQuantity
stoneExponentQuantity =
  record
    { symbol = "H t / hbar"
    ; meaning = "dimensionless Stone/Schrodinger exponential argument"
    ; dimension = stoneExponentDimension
    ; dimensionNarrative =
        "energy times time divided by action is dimensionless"
    }

record StoneHbarActionDimensionCancellationReceipt : Set where
  field
    hamiltonianQuantity : DimensionedStoneQuantity
    timeQuantity : DimensionedStoneQuantity
    hbarActionQuantity : DimensionedStoneQuantity
    exponentQuantity : DimensionedStoneQuantity
    actionDimension : SIBaseDimensionVector
    exponentDimension : SIBaseDimensionVector
    actionDimensionIsHbar :
      actionDimension ≡ hbarActionDimension
    exponentDimensionIsDimensionless :
      exponentDimension ≡ dimensionlessVector
    cancellationLawLabel : String
    cancellationNarrative : List String

open StoneHbarActionDimensionCancellationReceipt public

canonicalStoneHbarActionDimensionCancellationReceipt :
  StoneHbarActionDimensionCancellationReceipt
canonicalStoneHbarActionDimensionCancellationReceipt =
  record
    { hamiltonianQuantity = hamiltonianEnergyQuantity
    ; timeQuantity = stoneTimeQuantity
    ; hbarActionQuantity = hbarQuantity
    ; exponentQuantity = stoneExponentQuantity
    ; actionDimension = hamiltonianTimesTimeDimension
    ; exponentDimension = stoneExponentDimension
    ; actionDimensionIsHbar = refl
    ; exponentDimensionIsDimensionless = refl
    ; cancellationLawLabel = "dim(H * t / hbar) = 1"
    ; cancellationNarrative =
        "H carries energy dimension kg m^2 s^-2"
        ∷ "t carries SI-second dimension s"
        ∷ "H * t therefore carries action dimension kg m^2 s^-1"
        ∷ "hbar carries the same action dimension"
        ∷ "H * t / hbar is therefore dimensionless"
        ∷ "This is a dimension law only, not an hbar authority payload"
        ∷ []
    }

data StoneSchrodingerObligation : Set where
  requireRealTimeCarrier :
    StoneSchrodingerObligation

  requireSISecondEmbedding :
    StoneSchrodingerObligation

  requireHbarAuthorityPayload :
    StoneSchrodingerObligation

  requireDenseSelfAdjointHamiltonianDomain :
    StoneSchrodingerObligation

  requireFunctionalCalculusExponential :
    StoneSchrodingerObligation

  requireOneParameterUnitaryGroupLaws :
    StoneSchrodingerObligation

  requireStrongContinuityTopology :
    StoneSchrodingerObligation

  requireStoneTheoremAuthority :
    StoneSchrodingerObligation

canonicalStoneSchrodingerObligations :
  List StoneSchrodingerObligation
canonicalStoneSchrodingerObligations =
  requireRealTimeCarrier
  ∷ requireSISecondEmbedding
  ∷ requireHbarAuthorityPayload
  ∷ requireDenseSelfAdjointHamiltonianDomain
  ∷ requireFunctionalCalculusExponential
  ∷ requireOneParameterUnitaryGroupLaws
  ∷ requireStrongContinuityTopology
  ∷ requireStoneTheoremAuthority
  ∷ []

record OneParameterUnitaryGroupObligationReceipt : Set where
  field
    identityLawRequested : Bool
    identityLawRequestedIsTrue :
      identityLawRequested ≡ true
    compositionLawRequested : Bool
    compositionLawRequestedIsTrue :
      compositionLawRequested ≡ true
    adjointInverseLawRequested : Bool
    adjointInverseLawRequestedIsTrue :
      adjointInverseLawRequested ≡ true
    physicalRealGroupLawSupplied : Bool
    physicalRealGroupLawSuppliedIsFalse :
      physicalRealGroupLawSupplied ≡ false
    physicalUnitaryGroupConstructed : Bool
    physicalUnitaryGroupConstructedIsFalse :
      physicalUnitaryGroupConstructed ≡ false
    groupLawFormulae : List String

open OneParameterUnitaryGroupObligationReceipt public

canonicalOneParameterUnitaryGroupObligationReceipt :
  OneParameterUnitaryGroupObligationReceipt
canonicalOneParameterUnitaryGroupObligationReceipt =
  record
    { identityLawRequested = true
    ; identityLawRequestedIsTrue = refl
    ; compositionLawRequested = true
    ; compositionLawRequestedIsTrue = refl
    ; adjointInverseLawRequested = true
    ; adjointInverseLawRequestedIsTrue = refl
    ; physicalRealGroupLawSupplied = false
    ; physicalRealGroupLawSuppliedIsFalse = refl
    ; physicalUnitaryGroupConstructed = false
    ; physicalUnitaryGroupConstructedIsFalse = refl
    ; groupLawFormulae =
        "U(0) = I"
        ∷ "U(s + t) = U(s) U(t)"
        ∷ "U(- t) = U(t)^*"
        ∷ "These are requested for physical Real time, not supplied here"
        ∷ []
    }

record StrongContinuityTopologyObligationReceipt : Set where
  field
    realCarrierSupplied : Bool
    realCarrierSuppliedIsFalse :
      realCarrierSupplied ≡ false
    realMetricTopologySupplied : Bool
    realMetricTopologySuppliedIsFalse :
      realMetricTopologySupplied ≡ false
    hilbertNormTopologySupplied : Bool
    hilbertNormTopologySuppliedIsFalse :
      hilbertNormTopologySupplied ≡ false
    strongOperatorTopologySupplied : Bool
    strongOperatorTopologySuppliedIsFalse :
      strongOperatorTopologySupplied ≡ false
    epsilonDeltaLimitLawSupplied : Bool
    epsilonDeltaLimitLawSuppliedIsFalse :
      epsilonDeltaLimitLawSupplied ≡ false
    strongContinuityFormula : String
    missingTopologyEvidence : List String

open StrongContinuityTopologyObligationReceipt public

canonicalStrongContinuityTopologyObligationReceipt :
  StrongContinuityTopologyObligationReceipt
canonicalStrongContinuityTopologyObligationReceipt =
  record
    { realCarrierSupplied = false
    ; realCarrierSuppliedIsFalse = refl
    ; realMetricTopologySupplied = false
    ; realMetricTopologySuppliedIsFalse = refl
    ; hilbertNormTopologySupplied = false
    ; hilbertNormTopologySuppliedIsFalse = refl
    ; strongOperatorTopologySupplied = false
    ; strongOperatorTopologySuppliedIsFalse = refl
    ; epsilonDeltaLimitLawSupplied = false
    ; epsilonDeltaLimitLawSuppliedIsFalse = refl
    ; strongContinuityFormula =
        "for every psi and epsilon > 0, exists delta > 0 so that |t - t0| < delta implies ||U(t) psi - U(t0) psi|| < epsilon"
    ; missingTopologyEvidence =
        "constructive Real carrier or accepted Real-analysis authority"
        ∷ "metric/topology in which SI-second time converges"
        ∷ "Hilbert norm topology and strong-operator topology"
        ∷ "epsilon-delta or equivalent net/filter strong-continuity proof"
        ∷ []
    }

record DenseSelfAdjointDomainObligationReceipt : Set where
  field
    finiteGeneratorWitnessAvailable : Bool
    finiteGeneratorWitnessAvailableIsTrue :
      finiteGeneratorWitnessAvailable ≡ true
    physicalHilbertCarrierSupplied : Bool
    physicalHilbertCarrierSuppliedIsFalse :
      physicalHilbertCarrierSupplied ≡ false
    denseDomainSupplied : Bool
    denseDomainSuppliedIsFalse :
      denseDomainSupplied ≡ false
    domainInvariantUnderEvolutionSupplied : Bool
    domainInvariantUnderEvolutionSuppliedIsFalse :
      domainInvariantUnderEvolutionSupplied ≡ false
    selfAdjointnessTheoremSupplied : Bool
    selfAdjointnessTheoremSuppliedIsFalse :
      selfAdjointnessTheoremSupplied ≡ false
    spectralCalculusExponentialSupplied : Bool
    spectralCalculusExponentialSuppliedIsFalse :
      spectralCalculusExponentialSupplied ≡ false
    domainFormula : String
    domainGapNarrative : List String

open DenseSelfAdjointDomainObligationReceipt public

canonicalDenseSelfAdjointDomainObligationReceipt :
  DenseSelfAdjointDomainObligationReceipt
canonicalDenseSelfAdjointDomainObligationReceipt =
  record
    { finiteGeneratorWitnessAvailable = true
    ; finiteGeneratorWitnessAvailableIsTrue = refl
    ; physicalHilbertCarrierSupplied = false
    ; physicalHilbertCarrierSuppliedIsFalse = refl
    ; denseDomainSupplied = false
    ; denseDomainSuppliedIsFalse = refl
    ; domainInvariantUnderEvolutionSupplied = false
    ; domainInvariantUnderEvolutionSuppliedIsFalse = refl
    ; selfAdjointnessTheoremSupplied = false
    ; selfAdjointnessTheoremSuppliedIsFalse = refl
    ; spectralCalculusExponentialSupplied = false
    ; spectralCalculusExponentialSuppliedIsFalse = refl
    ; domainFormula =
        "D(H) dense in physical Hilbert space and H = H^* on D(H)"
    ; domainGapNarrative =
        "Finite-depth self-adjoint generator evidence is already threaded upstream"
        ∷ "The physical Hilbert carrier and dense domain are not constructed here"
        ∷ "Self-adjointness and spectral-calculus exponential remain authority-bound"
        ∷ []
    }

record StoneHbarDimensionlessActionBridge : Setω where
  field
    upstreamStoneTimeBridge :
      StoneTime.StoneSISecondTimeParameterBridge

    upstreamFormulaIsStoneSchrodinger :
      StoneTime.unitaryEvolutionFormula upstreamStoneTimeBridge
      ≡
      "U(t) = exp(-i H t / hbar)"

    upstreamRequestsHbarPayload :
      StoneTime.hbarDerivedSIPayloadRequested upstreamStoneTimeBridge
      ≡
      true

    upstreamKeepsHbarAuthorityFalse :
      StoneTime.hbarAuthorityPayloadSupplied upstreamStoneTimeBridge
      ≡
      false

    upstreamKeepsPhysicalStoneFalse :
      StoneReceipt.physicalStoneCarrierPromoted
        (StoneTime.stoneCarrierReceipt upstreamStoneTimeBridge)
      ≡
      false

    dimensionCancellation :
      StoneHbarActionDimensionCancellationReceipt

    dimensionCancellationActionIsHbar :
      actionDimension dimensionCancellation ≡ hbarActionDimension

    dimensionCancellationExponentIsDimensionless :
      exponentDimension dimensionCancellation ≡ dimensionlessVector

    groupObligations :
      OneParameterUnitaryGroupObligationReceipt

    topologyObligations :
      StrongContinuityTopologyObligationReceipt

    domainObligations :
      DenseSelfAdjointDomainObligationReceipt

    obligations :
      List StoneSchrodingerObligation

    obligationsAreCanonical :
      obligations ≡ canonicalStoneSchrodingerObligations

    realCarrierAuthoritySupplied :
      Bool

    realCarrierAuthoritySuppliedIsFalse :
      realCarrierAuthoritySupplied ≡ false

    hbarAuthoritySupplied :
      Bool

    hbarAuthoritySuppliedIsFalse :
      hbarAuthoritySupplied ≡ false

    stoneTheoremAuthoritySupplied :
      Bool

    stoneTheoremAuthoritySuppliedIsFalse :
      stoneTheoremAuthoritySupplied ≡ false

    physicalSchrodingerEvolutionPromoted :
      Bool

    physicalSchrodingerEvolutionPromotedIsFalse :
      physicalSchrodingerEvolutionPromoted ≡ false

    bridgeBoundary :
      List String

open StoneHbarDimensionlessActionBridge public

canonicalStoneHbarDimensionlessActionBridge :
  StoneHbarDimensionlessActionBridge
canonicalStoneHbarDimensionlessActionBridge =
  record
    { upstreamStoneTimeBridge =
        StoneTime.canonicalStoneSISecondTimeParameterBridge
    ; upstreamFormulaIsStoneSchrodinger =
        refl
    ; upstreamRequestsHbarPayload =
        refl
    ; upstreamKeepsHbarAuthorityFalse =
        refl
    ; upstreamKeepsPhysicalStoneFalse =
        refl
    ; dimensionCancellation =
        canonicalStoneHbarActionDimensionCancellationReceipt
    ; dimensionCancellationActionIsHbar =
        refl
    ; dimensionCancellationExponentIsDimensionless =
        refl
    ; groupObligations =
        canonicalOneParameterUnitaryGroupObligationReceipt
    ; topologyObligations =
        canonicalStrongContinuityTopologyObligationReceipt
    ; domainObligations =
        canonicalDenseSelfAdjointDomainObligationReceipt
    ; obligations =
        canonicalStoneSchrodingerObligations
    ; obligationsAreCanonical =
        refl
    ; realCarrierAuthoritySupplied =
        false
    ; realCarrierAuthoritySuppliedIsFalse =
        refl
    ; hbarAuthoritySupplied =
        false
    ; hbarAuthoritySuppliedIsFalse =
        refl
    ; stoneTheoremAuthoritySupplied =
        false
    ; stoneTheoremAuthoritySuppliedIsFalse =
        refl
    ; physicalSchrodingerEvolutionPromoted =
        false
    ; physicalSchrodingerEvolutionPromotedIsFalse =
        refl
    ; bridgeBoundary =
        "The upstream Stone SI-second bridge is consumed without changing its false promotion guards"
        ∷ "The local dimension law proves only dim(H * t / hbar) = 1 by constructor arithmetic"
        ∷ "The Real carrier, hbar authority payload, dense physical Hamiltonian domain, Stone theorem authority, and physical promotion token remain absent"
        ∷ "One-parameter group laws and strong continuity are recorded as requested obligations"
        ∷ "No physical Schrodinger evolution theorem is promoted from this module"
        ∷ []
    }

canonicalHbarActionCancellation :
  actionDimension canonicalStoneHbarActionDimensionCancellationReceipt
  ≡
  hbarActionDimension
canonicalHbarActionCancellation =
  refl

canonicalStoneExponentIsDimensionless :
  exponentDimension canonicalStoneHbarActionDimensionCancellationReceipt
  ≡
  dimensionlessVector
canonicalStoneExponentIsDimensionless =
  refl

canonicalBridgeKeepsRealCarrierAuthorityFalse :
  realCarrierAuthoritySupplied canonicalStoneHbarDimensionlessActionBridge
  ≡
  false
canonicalBridgeKeepsRealCarrierAuthorityFalse =
  refl

canonicalBridgeKeepsHbarAuthorityFalse :
  hbarAuthoritySupplied canonicalStoneHbarDimensionlessActionBridge
  ≡
  false
canonicalBridgeKeepsHbarAuthorityFalse =
  refl

canonicalBridgeKeepsStoneTheoremAuthorityFalse :
  stoneTheoremAuthoritySupplied canonicalStoneHbarDimensionlessActionBridge
  ≡
  false
canonicalBridgeKeepsStoneTheoremAuthorityFalse =
  refl

canonicalBridgeKeepsPhysicalSchrodingerPromotionFalse :
  physicalSchrodingerEvolutionPromoted
    canonicalStoneHbarDimensionlessActionBridge
  ≡
  false
canonicalBridgeKeepsPhysicalSchrodingerPromotionFalse =
  refl

canonicalStoneHbarDimensionlessActionBridgeORCSLPGF :
  List String
canonicalStoneHbarDimensionlessActionBridgeORCSLPGF =
  "O: Lane 3 Closure worker owns the Stone/Hbar dimensionless action bridge only"
  ∷ "R: make dim(H * t / hbar) explicit while recording group, topology, domain, and authority blockers"
  ∷ "C: DASHI.Physics.Closure.StoneHbarDimensionlessActionBridge imports only the existing Stone SI-second bridge and Stone carrier receipt"
  ∷ "S: internal SI dimension arithmetic closes by refl; Real carrier, hbar authority, Stone authority, and physical Schrodinger promotion remain false"
  ∷ "L: dimension receipt -> group/topology/domain obligation receipts -> fail-closed bridge"
  ∷ "P: canonical bridge packages U(t)=exp(-i H t / hbar) without constructing physical evolution"
  ∷ "G: no external authority is fabricated; every promotion-affecting boolean is false with refl proof"
  ∷ "F: remaining gap is external Real/topology/domain/hbar/Stone-theorem evidence"
  ∷ []
