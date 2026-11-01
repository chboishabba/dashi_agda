module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFRETDistributionTextAcquisitionValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFRETDistributionTextAcquisitionExact as Target

------------------------------------------------------------------------
-- RED-first validation surface for the machine-readable Figure-7 discussion.
-- The source pays qualitative distribution/population and labeling-axis facts,
-- not exact numeric population fractions or complete conformational recovery.
------------------------------------------------------------------------

ligandFreeDLn = Target.ligandFreeDLnDistributionObservation
ligandBoundDLn = Target.ligandBoundDLnDistributionObservation
ligandFreeDLc = Target.ligandFreeDLcDistributionObservation
intermediateContact = Target.intermediateContactObservation

boundary = Target.canonicalAdKFRETDistributionTextAcquisitionBoundary

dLnTwoMajorStatesPaid : Bool
dLnTwoMajorStatesPaid = Target.AdKFRETDistributionTextAcquisitionBoundary.ligandFreeDLnTwoMajorStatesPaid boundary

closedLikeFractionSmallerPaid : Bool
closedLikeFractionSmallerPaid = Target.AdKFRETDistributionTextAcquisitionBoundary.closedLikeFractionSmallerThanOpenLikePaid boundary

labelAxisDistinctionPaid : Bool
labelAxisDistinctionPaid = Target.AdKFRETDistributionTextAcquisitionBoundary.labelAxisDependentInterpretationPaid boundary

intermediateContactDecreasePaid : Bool
intermediateContactDecreasePaid = Target.AdKFRETDistributionTextAcquisitionBoundary.intermediateContactDecreasesDistancesPaid boundary

numericFractionsStillUnpaid : Bool
numericFractionsStillUnpaid = Target.AdKFRETDistributionTextAcquisitionBoundary.exactPopulationFractionsPaid boundary

fretClosedNotPromotedToFullyClosed : Bool
fretClosedNotPromotedToFullyClosed = Target.AdKFRETDistributionTextAcquisitionBoundary.fretClosedEqualsFullyClosedAdK boundary
