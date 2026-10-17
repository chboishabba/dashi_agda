module DASHI.Biology.BH4OpenMetabolicNetworkAdapterExact where

open import DASHI.Core.Prelude

import DASHI.Biology.Cell.OpenMetabolicNetwork as OpenMetabolicNetwork
import DASHI.Biology.Cell.MetabolicStoichiometricConservation as MetabolicStoichiometricConservation
import DASHI.Biology.Cell.MetabolicOpenSystemBalance as MetabolicOpenSystemBalance
import DASHI.Biology.Molecular.BH4PanelStoichiometricMatrixExact as Matrix
import DASHI.Biology.BH4CompartmentKineticStateExact as Parameters
import DASHI.Biology.BH4JointFluxFeasibilityExact as Flux
import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- BH4 adapter into the existing open-metabolic network machinery.
--
-- Internal biochemical reactions live in the stoichiometric reaction carrier.
-- Compartment transport, uptake, secretion and oxidative loss live in the
-- external-exchange carrier.  This is the same separation already formalized by
-- MetabolicOpenSystemBalance; the BH4 lane does not introduce a parallel law.
------------------------------------------------------------------------

data BH4MetabolicEventKind : Set where
  internalReactionEvent : BH4MetabolicEventKind
  externalExchangeEvent : BH4MetabolicEventKind

data BH4ExchangeKind : Set where
  compartmentTransport : BH4ExchangeKind
  substrateUptake : BH4ExchangeKind
  productExport : BH4ExchangeKind
  oxidativeLoss : BH4ExchangeKind
  namedExchange : String → BH4ExchangeKind

openMetabolicNetworkType : Set₁
openMetabolicNetworkType = OpenMetabolicNetwork.OpenMetabolicNetwork

record BH4OpenMetabolicNetworkAdapter : Set where
  constructor bh4-open-metabolic-network-adapter
  field
    matrix : Matrix.BH4PanelStoichiometricMatrix
    quantitativeStateReference : String
    fluxFeasibility : Flux.BH4JointFluxFeasibility
    internalReactionReference : String
    externalExchangeReference : String
    openMetabolicNetworkInterfacePresent : Bool
    metabolicStoichiometricInterfacePresent : Bool
    metabolicOpenBalanceInterfacePresent : Bool
    concreteOpenNetworkInstantiationPaid : Bool

open BH4OpenMetabolicNetworkAdapter public

canonicalBH4OpenMetabolicNetworkAdapter : BH4OpenMetabolicNetworkAdapter
canonicalBH4OpenMetabolicNetworkAdapter =
  bh4-open-metabolic-network-adapter
    Matrix.qdprFiniteColumn
    "DASHI.Biology.BH4CompartmentKineticStateExact; parameter coordinates currently unresolved"
    Flux.canonicalUnderdeterminedFluxFeasibility
    "finite Rhea/ChEBI reaction columns only"
    "transport / uptake / export / oxidation exchange coordinates; quantitatively unpaid"
    true
    true
    true
    false

parameterEvidenceType : Set
parameterEvidenceType = Parameters.BH4ParameterEvidence

record BH4OpenMetabolicBoundary : Set where
  constructor bh4-open-metabolic-boundary
  field
    externalExchangeMayBeCollapsedIntoInternalStoichiometry : Bool
    externalExchangeMayBeCollapsedIntoInternalStoichiometryIsFalse :
      externalExchangeMayBeCollapsedIntoInternalStoichiometry ≡ false
    openMetabolicInterfaceCreatesConcreteNetworkInstance : Bool
    openMetabolicInterfaceCreatesConcreteNetworkInstanceIsFalse :
      openMetabolicInterfaceCreatesConcreteNetworkInstance ≡ false
    internalStoichiometricConservationPaysEnvironmentalBalance : Bool
    internalStoichiometricConservationPaysEnvironmentalBalanceIsFalse :
      internalStoichiometricConservationPaysEnvironmentalBalance ≡ false
    underdeterminedFluxReceiptCreatesMeasuredCellState : Bool
    underdeterminedFluxReceiptCreatesMeasuredCellStateIsFalse :
      underdeterminedFluxReceiptCreatesMeasuredCellState ≡ false
    openSystemBalanceProvesDiseaseMechanism : Bool
    openSystemBalanceProvesDiseaseMechanismIsFalse :
      openSystemBalanceProvesDiseaseMechanism ≡ false

open BH4OpenMetabolicBoundary public

canonicalBH4OpenMetabolicBoundary : BH4OpenMetabolicBoundary
canonicalBH4OpenMetabolicBoundary =
  bh4-open-metabolic-boundary false refl false refl false refl false refl false refl

canonicalBH4OpenMetabolicNetworkReceipt : Receipt.GenericReceipt
canonicalBH4OpenMetabolicNetworkReceipt =
  Receipt.mkNonPromotingReceipt
    "BH4 open metabolic network adapter"
    "DASHI.Biology.BH4OpenMetabolicNetworkAdapterExact"
    "BH4 internal reaction matrix + quantitative-state coordinates + explicit external exchange -> existing OpenMetabolicNetwork / MetabolicStoichiometricConservation / MetabolicOpenSystemBalance interfaces"
    "reuses DASHI's established open-system law instead of folding transport, uptake, export or oxidation into internal stoichiometric columns"
    "interface availability is not a concrete quantitative network instance; internal conservation is not environmental balance; open balance is not disease mechanism"
    "agda -i . DASHI/Biology/BH4OpenMetabolicNetworkAdapterExact.agda"
