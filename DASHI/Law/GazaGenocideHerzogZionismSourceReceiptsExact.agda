module DASHI.Law.GazaGenocideHerzogZionismSourceReceiptsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Source-attribution owner for highly contested Israel/Gaza/Zionism claims.
-- UN-mandated commission findings, ICJ procedural orders, General Assembly
-- resolutions, historical UN reports, party allegations, and DASHI bridges are
-- kept as distinct evidential relations.
------------------------------------------------------------------------

data SourceRole : Set where
  unIndependentCommissionFinding
  icjProvisionalMeasuresOrder
  generalAssemblyResolution
  unHistoricalStudy
  partyAllegation
  secondaryReport
  dashiInterpretiveBridge : SourceRole

data PropositionKind : Set where
  commissionFindsIsraelResponsibleForGenocideInGaza
  commissionFindsGenocideContinuing
  commissionFindsHerzogIncitementToGenocide
  icjMeritsGenocideJudgmentExists
  unga3379ZionismRacismDetermination
  unga4686Revoked3379
  historicalIrgunSternTerrorism
  zionismOfficiallyDeclaredTerroristIdeology
  fascismDiagnosis : PropositionKind

record SourceReceipt : Set where
  constructor sourceReceipt
  field
    proposition : PropositionKind
    role : SourceRole
    sourceReference : String
    boundedDescription : String

open SourceReceipt public

commissionGenocideFinding : SourceReceipt
commissionGenocideFinding = sourceReceipt
  commissionFindsIsraelResponsibleForGenocideInGaza
  unIndependentCommissionFinding
  "A/HRC/60/CRP.3, Independent International Commission of Inquiry, 16 September 2025"
  "Commission concluded on reasonable grounds that Israeli authorities and security forces committed genocide against Palestinians in Gaza and that the State of Israel bears responsibility"

commissionContinuingGenocideFinding : SourceReceipt
commissionContinuingGenocideFinding = sourceReceipt
  commissionFindsGenocideContinuing
  unIndependentCommissionFinding
  "UN Independent International Commission of Inquiry press release, 23 June 2026"
  "Commission reiterated that Israeli authorities and security forces continued to commit genocide and other atrocity crimes in Gaza"

commissionHerzogIncitementFinding : SourceReceipt
commissionHerzogIncitementFinding = sourceReceipt
  commissionFindsHerzogIncitementToGenocide
  unIndependentCommissionFinding
  "A/HRC/60/CRP.3, conclusion 253"
  "Commission concluded that President Isaac Herzog, Prime Minister Benjamin Netanyahu and former Defence Minister Yoav Gallant incited the commission of genocide"

icjNoMeritsReceipt : SourceReceipt
icjNoMeritsReceipt = sourceReceipt
  icjMeritsGenocideJudgmentExists
  icjProvisionalMeasuresOrder
  "South Africa v Israel, ICJ provisional-measures proceedings and subsequent interventions"
  "ICJ has issued provisional-measures orders; this receipt does not assert that a final merits judgment finding genocide exists"

unga3379Receipt : SourceReceipt
unga3379Receipt = sourceReceipt
  unga3379ZionismRacismDetermination
  generalAssemblyResolution
  "A/RES/3379 (XXX), 10 November 1975"
  "General Assembly determined that Zionism is a form of racism and racial discrimination"

unga4686Receipt : SourceReceipt
unga4686Receipt = sourceReceipt
  unga4686Revoked3379
  generalAssemblyResolution
  "A/RES/46/86, 16 December 1991"
  "General Assembly revoked the determination contained in resolution 3379"

irgunSternHistoricalReceipt : SourceReceipt
irgunSternHistoricalReceipt = sourceReceipt
  historicalIrgunSternTerrorism
  unHistoricalStudy
  "UN, Origins and Evolution of the Palestine Problem, Part I (1917-1947)"
  "UN historical material describes Irgun and the Stern Group as illegal armed organizations that engaged in terrorism"

------------------------------------------------------------------------
-- Explicit negative ownership: the stronger shorthand is not source-backed by
-- the above materials and must not be silently promoted.
------------------------------------------------------------------------

record AttributionBoundary : Set where
  constructor attributionBoundary
  field
    commissionFindingEqualsICJMeritsJudgment : Bool
    commissionFindingEqualsICJMeritsJudgmentIsFalse : commissionFindingEqualsICJMeritsJudgment ≡ false
    herzogCommissionFindingEqualsCriminalConviction : Bool
    herzogCommissionFindingEqualsCriminalConvictionIsFalse : herzogCommissionFindingEqualsCriminalConviction ≡ false
    zionismRacismResolutionEqualsTerroristIdeologyDesignation : Bool
    zionismRacismResolutionEqualsTerroristIdeologyDesignationIsFalse : zionismRacismResolutionEqualsTerroristIdeologyDesignation ≡ false
    armedGroupTerrorismEqualsWholeIdeologyTerroristDesignation : Bool
    armedGroupTerrorismEqualsWholeIdeologyTerroristDesignationIsFalse : armedGroupTerrorismEqualsWholeIdeologyTerroristDesignation ≡ false
    genocideFindingAutomaticallyEqualsFascismDiagnosis : Bool
    genocideFindingAutomaticallyEqualsFascismDiagnosisIsFalse : genocideFindingAutomaticallyEqualsFascismDiagnosis ≡ false

canonicalAttributionBoundary : AttributionBoundary
canonicalAttributionBoundary =
  attributionBoundary false refl false refl false refl false refl false refl
