module DASHI.Analysis.RiemannUniversalEvenConeFinalTaperLocalizationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannG2BalanceFreeComplementContextExact as BalanceFree
import DASHI.Analysis.RiemannUniversalEvenConeTransportGateExact as Transport

------------------------------------------------------------------------
-- FINAL-TAPER LOCALIZATION
--
-- The final RH lane already owns the same-universal-taper equalities from the
-- literal Off target into the Gamma and cluster targets inside
-- BalanceFreeComplementContext.  Therefore the universal-even-cone source does
-- not need three independent same-object welds.  The only genuinely new taper
-- identity is source -> literal Off universal pole-quotient taper; the existing
-- context then propagates that same object to Gamma and cluster consumers.
--
-- This owner records the dependency contraction only.  It does not fabricate
-- the source-to-Off weld or transport the Lean proof into Agda.
------------------------------------------------------------------------

universalReturn : Universal.UniversalEvenConeReturn
universalReturn = Universal.canonicalUniversalEvenConeReturn

balanceFreeBoundary : BalanceFree.BalanceFreeContextBoundary
balanceFreeBoundary = BalanceFree.canonicalBalanceFreeContextBoundary

transportBoundary : Transport.UniversalEvenConeTransportBoundary
transportBoundary = Transport.canonicalUniversalEvenConeTransportBoundary

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data LeanSourceExistenceCreatesSourceToOffWeld : Set where
data OEISCreatesSourceToOffWeld : Set where
data OffGammaTaperEqualityCreatesSourceToOffWeld : Set where

leanSourceExistenceDoesNotCreateWeld :
  LeanSourceExistenceCreatesSourceToOffWeld -> ⊥
leanSourceExistenceDoesNotCreateWeld ()

oeisDoesNotCreateWeld : OEISCreatesSourceToOffWeld -> ⊥
oeisDoesNotCreateWeld ()

offGammaEqualityDoesNotCreateSourceWeld :
  OffGammaTaperEqualityCreatesSourceToOffWeld -> ⊥
offGammaEqualityDoesNotCreateSourceWeld ()

record UniversalEvenConeFinalTaperLocalizationBoundary : Set where
  constructor universal-even-cone-final-taper-localization-boundary
  field
    sourceUniversalEvenConeObjectOwned : Bool
    balanceFreeFinalTaperContextAvailable : Bool
    onlyNewTaperWeldIsSourceToOff : Bool
    offToGammaReuseAlreadyOwned : Bool
    offToClusterReuseAlreadyOwned : Bool
    transportedOffTaperFeedsExistingAttachmentCompilers : Bool

    sourceToOffSameObjectWeldPaid : Bool
    leanSourceExistenceCreatesWeld : Bool
    oeisCreatesWeld : Bool
    existingOffGammaEqualityCreatesSourceWeld : Bool
    nextResidual : String
open UniversalEvenConeFinalTaperLocalizationBoundary public

canonicalUniversalEvenConeFinalTaperLocalizationBoundary :
  UniversalEvenConeFinalTaperLocalizationBoundary
canonicalUniversalEvenConeFinalTaperLocalizationBoundary =
  universal-even-cone-final-taper-localization-boundary
    true true
    true true true true
    false false false false
    "Transport the exact Lean universal-even-cone taper to the literal Off.universalPoleQuotientTaper on the final target. Do not separately rebuild Gamma or cluster taper identity: BalanceFreeComplementContext already carries sameUniversalTaperOffGamma and sameUniversalTaperOffCluster. Source existence, OEIS patterns, and downstream Off/Gamma equality do not create the missing source-to-Off same-object receipt."
