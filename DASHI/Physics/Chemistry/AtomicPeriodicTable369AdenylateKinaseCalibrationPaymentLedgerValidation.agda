module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationPaymentLedgerValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationPaymentLedgerExact as P

paymentRegression :
  P.AdKCalibrationPaymentLedgerBoundary.endpointThreeCVCellsPaid
    P.canonicalAdKCalibrationPaymentLedgerBoundary
  ≡ true
  × P.AdKCalibrationPaymentLedgerBoundary.gammaZeroReferencePaid
    P.canonicalAdKCalibrationPaymentLedgerBoundary
  ≡ true
  × P.AdKCalibrationPaymentLedgerBoundary.figureFiveVisibleEnergyCellsPaid
    P.canonicalAdKCalibrationPaymentLedgerBoundary
  ≡ true
  × P.AdKCalibrationPaymentLedgerBoundary.intermediateDLnCellsPaid
    P.canonicalAdKCalibrationPaymentLedgerBoundary
  ≡ false
  × P.AdKCalibrationPaymentLedgerBoundary.intermediateFreeEnergyCellsPaid
    P.canonicalAdKCalibrationPaymentLedgerBoundary
  ≡ false
  × P.AdKCalibrationPaymentLedgerBoundary.perEdgeKramersNumericsPaid
    P.canonicalAdKCalibrationPaymentLedgerBoundary
  ≡ false
paymentRegression = refl , refl , refl , refl , refl , refl

provenanceRegression :
  P.AdKCalibrationPaymentLedgerBoundary.everyCellCarriesSourceRole
    P.canonicalAdKCalibrationPaymentLedgerBoundary
  ≡ true
  × P.AdKCalibrationPaymentLedgerBoundary.everyUnpaidCellCarriesNextPayment
    P.canonicalAdKCalibrationPaymentLedgerBoundary
  ≡ true
  × P.AdKCalibrationPaymentLedgerBoundary.ledgerReusesGuardedAcquisition
    P.canonicalAdKCalibrationPaymentLedgerBoundary
  ≡ true
  × P.AdKCalibrationPaymentLedgerBoundary.ledgerReusesProvenanceGraph
    P.canonicalAdKCalibrationPaymentLedgerBoundary
  ≡ true
provenanceRegression = refl , refl , refl , refl

firewallRegression :
  P.AdKCalibrationPaymentLedgerBoundary.paidEndpointCreatesIntermediateTable
    P.canonicalAdKCalibrationPaymentLedgerBoundary
  ≡ false
  × P.AdKCalibrationPaymentLedgerBoundary.uncertaintyCreatesMissingEnergy
    P.canonicalAdKCalibrationPaymentLedgerBoundary
  ≡ false
  × P.AdKCalibrationPaymentLedgerBoundary.identityCreatesNumericPayment
    P.canonicalAdKCalibrationPaymentLedgerBoundary
  ≡ false
firewallRegression = refl , refl , refl
