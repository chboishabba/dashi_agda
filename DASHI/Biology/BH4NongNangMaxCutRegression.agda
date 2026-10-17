module DASHI.Biology.BH4NongNangMaxCutRegression where

open import DASHI.Core.Prelude

import DASHI.Biology.BH4SystemStateExact as System
import DASHI.Biology.NitrogenOxideSpeciesCouplingExact as Oxide
import DASHI.Biology.NitrousOxideMetabolismEvidenceExact as Nang
import DASHI.Biology.NonginNangNitrogenOxideRefinementExact as Nongin
import DASHI.Biology.KitzerowBH4SystemNongNangMaxCutExact as MaxCut

------------------------------------------------------------------------
-- Regression surface written before the production owners.
------------------------------------------------------------------------

nitricOxideIsNotNitrousOxide :
  Oxide.nitricOxide ≡ Oxide.nitrousOxide → ⊥
nitricOxideIsNotNitrousOxide = Oxide.nitricOxideNotNitrousOxide

coarseNitrogenOxideCannotServeFineChemicalConsumer :
  Nongin.CoarseChemicalDescent → ⊥
coarseNitrogenOxideCannotServeFineChemicalConsumer =
  Nongin.coarseNitrogenOxideCannotServeFineConsumer

proteinPresenceDoesNotEstablishNOSUncoupling :
  Oxide.NOSCouplingBoundary.proteinPresenceEstablishesUncoupling
    Oxide.canonicalNOSCouplingBoundary
  ≡ false
proteinPresenceDoesNotEstablishNOSUncoupling = refl

reactionAnnotationDoesNotPayWholeFluxBalance :
  System.BH4SystemBoundary.reactionAnnotationPaysWholeFluxBalance
    System.canonicalBH4SystemBoundary
  ≡ false
reactionAnnotationDoesNotPayWholeFluxBalance = refl

nangCobalaminLaneDoesNotBecomeNOSLane :
  Nang.NitrousOxideMetabolismBoundary.nitrousOxideEvidenceCreatesNOSUncouplingProof
    Nang.canonicalNitrousOxideMetabolismBoundary
  ≡ false
nangCobalaminLaneDoesNotBecomeNOSLane = refl

nongNangAliasDoesNotIdentifyNitricOxide :
  Nongin.NongNangGenealogyBoundary.nongNangAliasIdentifiesNitricOxide
    Nongin.canonicalNongNangGenealogyBoundary
  ≡ false
nongNangAliasDoesNotIdentifyNitricOxide = refl

isolatedNodesDoNotConfirmKitzerowWholeGraph :
  MaxCut.KitzerowBH4SystemMaxCutBoundary.isolatedNodeSupportConfirmsWholeGraph
    MaxCut.canonicalKitzerowBH4SystemMaxCutBoundary
  ≡ false
isolatedNodesDoNotConfirmKitzerowWholeGraph = refl

n2oLaneDoesNotCreateKitzerowMechanism :
  MaxCut.KitzerowBH4SystemMaxCutBoundary.nitrousOxideLaneCreatesKitzerowMechanism
    MaxCut.canonicalKitzerowBH4SystemMaxCutBoundary
  ≡ false
n2oLaneDoesNotCreateKitzerowMechanism = refl
