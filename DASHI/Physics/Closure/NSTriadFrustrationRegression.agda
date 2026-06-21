module DASHI.Physics.Closure.NSTriadFrustrationRegression where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.Closure.NSAdversarialGibbsPhaseReferenceReceipt as Gibbs using
  ( NSAdversarialGibbsPhaseReferenceReceipt
  ; canonicalNSAdversarialGibbsPhaseReferenceReceipt
  )
open import DASHI.Physics.Closure.NSSacasaTriadFrustrationBridgeBoundary as Bridge using
  ( NSSacasaTriadFrustrationBridgeBoundary
  ; canonicalNSSacasaTriadFrustrationBridgeBoundary
  )
open import DASHI.Physics.Closure.NSTriadFrustrationDefectBoundary as Defect using
  ( NSTriadFrustrationDefectBoundary
  ; canonicalNSTriadFrustrationDefectBoundary
  )
open import DASHI.Physics.Closure.NSTriadIncidenceCocycleReceipt as Incidence using
  ( NSTriadIncidenceCocycleReceipt
  ; canonicalNSTriadIncidenceCocycleReceipt
  )
open import DASHI.Physics.Closure.NSTriadKernelPhaseCocycleReceipt as Kernel using
  ( NSTriadKernelPhaseCocycleReceipt
  ; canonicalNSTriadKernelPhaseCocycleReceipt
  )

record NSTriadFrustrationRegression : Setω where
  constructor mkNSTriadFrustrationRegression
  field
    incidenceReceipt :
      Incidence.NSTriadIncidenceCocycleReceipt

    kernelPhaseReceipt :
      Kernel.NSTriadKernelPhaseCocycleReceipt

    frustrationDefectBoundary :
      Defect.NSTriadFrustrationDefectBoundary
    frustrationDefectBoundaryIsCanonical :
      frustrationDefectBoundary ≡ Defect.canonicalNSTriadFrustrationDefectBoundary

    adversarialGibbsReceipt :
      Gibbs.NSAdversarialGibbsPhaseReferenceReceipt
    adversarialGibbsReceiptIsCanonical :
      adversarialGibbsReceipt ≡ Gibbs.canonicalNSAdversarialGibbsPhaseReferenceReceipt

    sacasaTriadFrustrationBridgeBoundary :
      Bridge.NSSacasaTriadFrustrationBridgeBoundary

open NSTriadFrustrationRegression public

canonicalNSTriadFrustrationRegression :
  NSTriadFrustrationRegression
canonicalNSTriadFrustrationRegression =
  mkNSTriadFrustrationRegression
    Incidence.canonicalNSTriadIncidenceCocycleReceipt
    Kernel.canonicalNSTriadKernelPhaseCocycleReceipt
    Defect.canonicalNSTriadFrustrationDefectBoundary
    refl
    Gibbs.canonicalNSAdversarialGibbsPhaseReferenceReceipt
    refl
    Bridge.canonicalNSSacasaTriadFrustrationBridgeBoundary
