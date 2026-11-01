module DASHI.Physics.Closure.NSTriadKNCheskidovEguchiCountingTransferAudit where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Alexey Cheskidov; Taichi Eguchi.
-- Title: "Global well-posedness of the Navier-Stokes equations for small
-- initial data in frequency localized Koch-Tataru's space"; journal version
-- "Global-in-time smooth solution to the Navier-Stokes equations for small
-- initial data in frequency localized Koch-Tataru's space".
-- arXiv/year: arXiv:2503.11642v1, submitted 14 March 2025.
-- arXiv/DataCite DOI: 10.48550/arXiv.2503.11642.
-- Journal title: "Global-in-time smooth solution to the Navier-Stokes
-- equations for small initial data in frequency localized Koch-Tataru's
-- space".
-- Venue/year: Journal of Differential Equations 477 (2026), article 114534;
-- issue date 5 October 2026.
-- Journal DOI: 10.1016/j.jde.2026.114534.
-- Uses: Lemma 3.2's physical-space heat-kernel decomposition.  Its distant
-- term covers annular cube layers by lattice-indexed cubes, uses layer count
-- comparable to n^2, kernel decay n^-4, and sums n^-2.
-- Relationship: the local/distant and count-versus-decay pattern is useful
-- reconnaissance for DASHI.  It is not itself a Fourier resonance-fibre
-- theorem: the source works in physical space, with a heat kernel and
-- space-time BMO quantities.  DASHI therefore does not cite it as proving the
-- low-output shell convolution estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

sourceExists : Bool
sourceExists = true

arxivDOIVerified : Bool
arxivDOIVerified = true

journalDOIVerified : Bool
journalDOIVerified = true

journalVersionMetadataAvailable : Bool
journalVersionMetadataAvailable = true

lemmaThreeTwoLocated : Bool
lemmaThreeTwoLocated = true

physicalSpaceHeatKernelArgument : Bool
physicalSpaceHeatKernelArgument = true

localDistantSplitPresent : Bool
localDistantSplitPresent = true

annularLayerCountComparableToNSquared : Bool
annularLayerCountComparableToNSquared = true

kernelDecayFourthPower : Bool
kernelDecayFourthPower = true

resultingLayerSeriesSecondPowerSummable : Bool
resultingLayerSeriesSecondPowerSummable = true

sourceDirectlyStatesFourierResonanceFibreBound : Bool
sourceDirectlyStatesFourierResonanceFibreBound = false

sourceDirectlySuppliesLowOutputThreeHalvesFactor : Bool
sourceDirectlySuppliesLowOutputThreeHalvesFactor = false

sourceConsumedAsFirstAdjointTheorem : Bool
sourceConsumedAsFirstAdjointTheorem = false

countingPatternRetainedAsReconnaissance : Bool
countingPatternRetainedAsReconnaissance = true

record CheskidovEguchiTransferReceipt : Set where
  constructor receipt
  field
    sourceReceipt : sourceExists ≡ true
    arxivDOIReceipt : arxivDOIVerified ≡ true
    journalDOIReceipt : journalDOIVerified ≡ true
    journalMetadataReceipt : journalVersionMetadataAvailable ≡ true
    lemmaReceipt : lemmaThreeTwoLocated ≡ true
    heatKernelReceipt : physicalSpaceHeatKernelArgument ≡ true
    localDistantReceipt : localDistantSplitPresent ≡ true
    layerCountReceipt : annularLayerCountComparableToNSquared ≡ true
    kernelDecayReceipt : kernelDecayFourthPower ≡ true
    summableSeriesReceipt : resultingLayerSeriesSecondPowerSummable ≡ true
    noFourierFibreTheoremReceipt :
      sourceDirectlyStatesFourierResonanceFibreBound ≡ false
    noLowOutputFactorReceipt :
      sourceDirectlySuppliesLowOutputThreeHalvesFactor ≡ false
    noTheoremConsumptionReceipt : sourceConsumedAsFirstAdjointTheorem ≡ false
    reconnaissanceReceipt : countingPatternRetainedAsReconnaissance ≡ true

open CheskidovEguchiTransferReceipt public

cheskidovEguchiTransferReceipt : CheskidovEguchiTransferReceipt
cheskidovEguchiTransferReceipt =
  receipt refl refl refl refl refl refl refl refl refl refl refl refl refl refl

cheskidovEguchiCountingTransferAuditRepresented : Bool
cheskidovEguchiCountingTransferAuditRepresented = true

cheskidovEguchiCountingTransferAuditRepresentedIsTrue :
  cheskidovEguchiCountingTransferAuditRepresented ≡ true
cheskidovEguchiCountingTransferAuditRepresentedIsTrue = refl
