module DASHI.Reasoning.TypedDependencyUpgradeAtlas where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.TypedDependencyCore as Dependency

------------------------------------------------------------------------
-- Conservative upgrade surface for legacy Boolean fields.
--
-- A true flag may be retained for display/regression, but promotion requires a
-- witness inhabiting the indexed evidence type.  This lets existing records
-- migrate incrementally without pretending a Boolean contains its proof.
------------------------------------------------------------------------

record WitnessBearingFlag : Set₁ where
  field
    flag : Bool
    Witness : Set
    trueRequiresWitness : flag ≡ true → Witness
    flagLabel : String
    witnessProvenance : String

open WitnessBearingFlag public

forgetWitnessBearingFlag : WitnessBearingFlag → Bool
forgetWitnessBearingFlag wrapped = flag wrapped

data UpgradeDomain : Set where
  rsiDomain gluingDomain memoryDomain verificationDomain : UpgradeDomain
  capabilityDomain authorityDomain pathologicDomain stageDomain : UpgradeDomain

record DependencyUpgradeSite : Set where
  field
    domain : UpgradeDomain
    legacySurface : String
    typedReplacement : String
    sourceModule : String
    targetModule : String
    implementedInThisTranche : Bool
    promotionBlockedWithoutWitness : Bool
    upgradeReceipt : String

open DependencyUpgradeSite public

rsiUpgrade : DependencyUpgradeSite
rsiUpgrade = record
  { domain = rsiDomain
  ; legacySurface = "RSIPresence Bool conjunction"
  ; typedReplacement = "irreducible ternary dependency plus typed hyperedge section"
  ; sourceModule = "DASHI.Reasoning.LacanRegisterSinthomeHyperfabric"
  ; targetModule = "DASHI.Reasoning.RSITypedDependencyHyperfabric"
  ; implementedInThisTranche = true
  ; promotionBlockedWithoutWitness = true
  ; upgradeReceipt = "Boolean deletion tests retained; relational support now has indexed witnesses."
  }

gluingUpgrade : DependencyUpgradeSite
gluingUpgrade = record
  { domain = gluingDomain
  ; legacySurface = "actualGluingWitnessAvailable : Bool"
  ; typedReplacement = "TypedClosureGluing with GlobalSection and compatibility proof"
  ; sourceModule = "DASHI.Reasoning.PNFZizekOperator"
  ; targetModule = "DASHI.Reasoning.PNFTypedDependencyAdapters"
  ; implementedInThisTranche = true
  ; promotionBlockedWithoutWitness = true
  ; upgradeReceipt = "A closure narrative or true flag cannot stand in for an indexed compatible section."
  }

memoryUpgrade : DependencyUpgradeSite
memoryUpgrade = record
  { domain = memoryDomain
  ; legacySurface = "rememberedEventPreservedForThisMode : Bool"
  ; typedReplacement = "MemoryEventPreserved update memory equality and path-indexed MemoryPreserved family"
  ; sourceModule = "DASHI.Cognition.PNF.MemoryFibre and DASHI.Reasoning.PNFZizekOperator"
  ; targetModule = "DASHI.Reasoning.PNFTypedDependencyAdapters and DASHI.Reasoning.SinthomeTypedStabilisation"
  ; implementedInThisTranche = true
  ; promotionBlockedWithoutWitness = true
  ; upgradeReceipt = "Existing preservation theorems are reused for revaluation, habituation and inhibitory extinction; other modes remain separately obligated."
  }

verificationUpgrade : DependencyUpgradeSite
verificationUpgrade = record
  { domain = verificationDomain
  ; legacySurface = "verification/checker availability Boolean"
  ; typedReplacement = "receipt carrying checker, context, claim and source authority"
  ; sourceModule = "DASHI.Reasoning.SFMVerifiedClaimPresentation"
  ; targetModule = "existing SFM formal artefact and checker receipt types"
  ; implementedInThisTranche = false
  ; promotionBlockedWithoutWitness = true
  ; upgradeReceipt = "The repository already contains the richer target; remaining Boolean call sites can be adapted incrementally."
  }

stageUpgrade : DependencyUpgradeSite
stageUpgrade = record
  { domain = stageDomain
  ; legacySurface = "stage reached/available Boolean"
  ; typedReplacement = "guarded transition with source, target, memory, valuation and residual witnesses"
  ; sourceModule = "legacy stage receipt surfaces"
  ; targetModule = "DASHI.Foundations.StageZeroToTwelveTransitionCore"
  ; implementedInThisTranche = true
  ; promotionBlockedWithoutWitness = true
  ; upgradeReceipt = "Numeral inhabitation does not establish a transition."
  }

pathologicUpgrade : DependencyUpgradeSite
pathologicUpgrade = record
  { domain = pathologicDomain
  ; legacySurface = "action constructor or menu availability"
  ; typedReplacement = "ActionDependency indexed by state, role, time, health and reputation"
  ; sourceModule = "Pathologic mechanics described in the attached review transcript"
  ; targetModule = "DASHI.Reasoning.PathologicConstraintSystem"
  ; implementedInThisTranche = true
  ; promotionBlockedWithoutWitness = true
  ; upgradeReceipt = "Can attempt, prudent, morally permitted and narratively required remain different types."
  }

canonicalDependencyUpgradeSites : List DependencyUpgradeSite
canonicalDependencyUpgradeSites =
  rsiUpgrade
  ∷ gluingUpgrade
  ∷ memoryUpgrade
  ∷ verificationUpgrade
  ∷ stageUpgrade
  ∷ pathologicUpgrade
  ∷ []

record DependencyUpgradeAtlasBoundary : Set where
  field
    boolsDeletedWholesale : Bool
    conservativeAdaptersAvailable : Bool
    typedPromotionRequired : Bool
    allLegacySitesAlreadyMigrated : Bool
    auditIdentifiesRemainingWork : Bool
    boundaryNote : String

canonicalDependencyUpgradeAtlasBoundary : DependencyUpgradeAtlasBoundary
canonicalDependencyUpgradeAtlasBoundary = record
  { boolsDeletedWholesale = false
  ; conservativeAdaptersAvailable = true
  ; typedPromotionRequired = true
  ; allLegacySitesAlreadyMigrated = false
  ; auditIdentifiesRemainingWork = true
  ; boundaryNote =
      "Legacy flags may remain as projections, but proof-bearing operations should consume indexed witnesses. The atlas distinguishes implemented adapters from future refactors."
  }
