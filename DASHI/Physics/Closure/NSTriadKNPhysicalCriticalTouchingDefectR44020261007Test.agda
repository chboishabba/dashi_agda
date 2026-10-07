module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingDefectR44020261007Test where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingDefectR44020261007Exact as X

r440SubsetWeldClosed : X.b4DefectR440SubsetWeldClosed ≡ true
r440SubsetWeldClosed = X.b4DefectR440SubsetWeldClosedIsTrue

physicalResidualNormalFormClosed : X.b4DefectPhysicalResidualNormalFormClosed ≡ true
physicalResidualNormalFormClosed = X.b4DefectPhysicalResidualNormalFormClosedIsTrue

signedPhysicalWorkClosed : X.b4DefectSignedPhysicalWorkClosed ≡ true
signedPhysicalWorkClosed = X.b4DefectSignedPhysicalWorkClosedIsTrue

physicalPaymentStillOpen : X.b4DefectR440PhysicalPaymentClosed ≡ false
physicalPaymentStillOpen = X.b4DefectR440PhysicalPaymentClosedIsFalse
