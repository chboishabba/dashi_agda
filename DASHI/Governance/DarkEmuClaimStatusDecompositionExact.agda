module DASHI.Governance.DarkEmuClaimStatusDecompositionExact where

open import DASHI.Core.Prelude
import DASHI.Governance.BudjBimAquacultureAuthorityExact as BudjBim
import DASHI.Governance.MithakaArchaeologicalEvidenceExact as Mithaka

------------------------------------------------------------------------
-- DARK EMU: CLAIM-LEVEL STATUS, NOT BOOK-LEVEL PROMOTION/DEMOTION
--
-- Independently evidenced local practices are admitted through their own
-- Gunditjmara/Mithaka institutional and archaeological sources.  Pascoe's
-- terminology, source handling and broader generalisations remain separately
-- contestable.  Independent validation of a phenomenon does not validate every
-- inference or quotation used to narrate it.
------------------------------------------------------------------------

data ClaimKind : Set where
  localMaterialPractice
  historicalSourceUse
  classificatoryLabel
  geographicGeneralization
  : ClaimKind

data ClaimStatus : ClaimKind → Set where
  independentlySupportedLocalPractice : ClaimStatus localMaterialPractice
  contestedSourceUse : ClaimStatus historicalSourceUse
  contestedClassification : ClaimStatus classificatoryLabel
  contestedGeneralization : ClaimStatus geographicGeneralization

budjBimIndependentPractice : BudjBim.EvidenceAuthority BudjBim.systematicKooyangAquaculture
budjBimIndependentPractice = BudjBim.unescoAquaculture

mithakaIndependentPractice : Mithaka.ClaimStatus Mithaka.largeScaleQuarrying
mithakaIndependentPractice = Mithaka.evidencedQuarrying

record DarkEmuBoundary : Set where
  constructor darkEmuBoundary
  field
    independentlySupportedPracticeValidatesPascoeSourceUse : Bool
    independentlySupportedPracticeValidatesPascoeSourceUseIsFalse : independentlySupportedPracticeValidatesPascoeSourceUse ≡ false
    localPracticeValidatesContinentWideGeneralization : Bool
    localPracticeValidatesContinentWideGeneralizationIsFalse : localPracticeValidatesContinentWideGeneralization ≡ false
    contestedFramingErasesIndependentArchaeology : Bool
    contestedFramingErasesIndependentArchaeologyIsFalse : contestedFramingErasesIndependentArchaeology ≡ false
    agreementPercentageIsStableTheoremSurface : Bool
    agreementPercentageIsStableTheoremSurfaceIsFalse : agreementPercentageIsStableTheoremSurface ≡ false

canonicalDarkEmuBoundary : DarkEmuBoundary
canonicalDarkEmuBoundary = darkEmuBoundary false refl false refl false refl false refl
