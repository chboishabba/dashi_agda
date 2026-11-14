module DASHI.Cognition.OracleEllisonMotiveSourceBoundaryExact where

------------------------------------------------------------------------
-- DIRECT-MOTIVE SOURCE BOUNDARY
--
-- A quoted declaration can pay the motive actually stated, but cannot be
-- expanded into a different psychological theory. Ellison's 2017 FIDF
-- statement directly pays a bounded support/solidarity motive for that gift.
-- Safra Catz's 2021 public statement pays an Oracle-leadership commitment to
-- supporting Israel. Neither pays technological immortality, Oracle authorship
-- of Israeli security policy, or Netanyahu's alleged threat-maintenance motive.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.OracleEllisonCapabilityPromotionExact as Promotion

------------------------------------------------------------------------
-- Source coordinates.
------------------------------------------------------------------------

data MotiveSource : Set where
  ellisonFIDF2017QuotedStatement : MotiveSource
  safraCatz2021OracleIsraelStatement : MotiveSource
  transcriptImmortalityInterpretation : MotiveSource
  transcriptThreatMaintenanceInterpretation : MotiveSource

sourceLocator : MotiveSource → String
sourceLocator ellisonFIDF2017QuotedStatement =
  "2017 FIDF gala reporting quoting Larry Ellison: IDF defends 'our home'; supporting soldiers described as a great honor"
sourceLocator safraCatz2021OracleIsraelStatement =
  "CTech/Calcalist, 2021-07-08: Safra Catz states Oracle mission/commitment to support Israel and says she and Larry Ellison are publicly committed"
sourceLocator transcriptImmortalityInterpretation =
  "transcript-2026-10-02.srt: technological-immortality / ghost-in-the-machine interpretation"
sourceLocator transcriptThreatMaintenanceInterpretation =
  "transcript-2026-10-02.srt: permanent-threat-maintenance-for-survival interpretation"

------------------------------------------------------------------------
-- Motive granularity.
------------------------------------------------------------------------

data MotiveClaim : Set where
  ellisonSupportsFIDFSoldiers : MotiveClaim
  ellisonFramesIsraelAsOurHome : MotiveClaim
  oracleLeadershipSupportsIsrael : MotiveClaim
  ellisonTechnologicalImmortality : MotiveClaim
  oracleSeeksIsraeliSecurityControl : MotiveClaim
  netanyahuMaintainsThreatsForPoliticalSurvival : MotiveClaim

record MotiveReceipt : Set where
  constructor motive-receipt
  field
    source : MotiveSource
    claim : MotiveClaim
    directDeclaration : Bool
    paid : Bool
    boundedNote : String

ellisonFIDFSupportReceipt : MotiveReceipt
ellisonFIDFSupportReceipt = motive-receipt
  ellisonFIDF2017QuotedStatement
  ellisonSupportsFIDFSoldiers
  true
  true
  "The quote pays a declared reason for supporting FIDF/IDF soldiers; it does not generalise to every Ellison or Oracle action."

ellisonOurHomeReceipt : MotiveReceipt
ellisonOurHomeReceipt = motive-receipt
  ellisonFIDF2017QuotedStatement
  ellisonFramesIsraelAsOurHome
  true
  true
  "The quoted 'our home' framing is attributable to Ellison in the donation context only."

oracleLeadershipIsraelSupportReceipt : MotiveReceipt
oracleLeadershipIsraelSupportReceipt = motive-receipt
  safraCatz2021OracleIsraelStatement
  oracleLeadershipSupportsIsrael
  true
  true
  "Catz publicly characterises Oracle and its leadership as committed to supporting Israel; this is corporate posture, not sovereign-control authorship."

ellisonImmortalityNonReceipt : MotiveReceipt
ellisonImmortalityNonReceipt = motive-receipt
  transcriptImmortalityInterpretation
  ellisonTechnologicalImmortality
  false
  false
  "The acquired donation/corporate statements do not state the transcript's technological-immortality motive."

netanyahuThreatMaintenanceNonReceipt : MotiveReceipt
netanyahuThreatMaintenanceNonReceipt = motive-receipt
  transcriptThreatMaintenanceInterpretation
  netanyahuMaintainsThreatsForPoliticalSurvival
  false
  false
  "No acquired direct statement admits intentionally maintaining security threats for political survival."

------------------------------------------------------------------------
-- Paid and unpaid motive surfaces.
------------------------------------------------------------------------

ellisonFIDFSupportMotivePaid : Bool
ellisonFIDFSupportMotivePaid = true

ellisonOurHomeFramingPaid : Bool
ellisonOurHomeFramingPaid = true

oracleLeadershipIsraelSupportCommitmentPaid : Bool
oracleLeadershipIsraelSupportCommitmentPaid = true

ellisonImmortalityMotivePaid : Bool
ellisonImmortalityMotivePaid = false

oracleSecurityBlueprintMotivePaid : Bool
oracleSecurityBlueprintMotivePaid = false

netanyahuThreatMaintenanceMotivePaid : Bool
netanyahuThreatMaintenanceMotivePaid = false

supportForIsraelImpliesAllCorporateActsServeIsraeliPolicy : Bool
supportForIsraelImpliesAllCorporateActsServeIsraeliPolicy = false

------------------------------------------------------------------------
-- Claim-relative promotion lattice weld.
--
-- This is a genuine L4 payment only for the narrow declared reason attached to
-- the FIDF-support act. It does not upgrade the immortality or policy-control
-- motive claims.
------------------------------------------------------------------------

ellisonFIDFDeclaredSupportHighestPaidLevel : Promotion.PromotionLevel
ellisonFIDFDeclaredSupportHighestPaidLevel = Promotion.intentMotive

------------------------------------------------------------------------
-- Boundary receipt.
------------------------------------------------------------------------

record MotiveSourceBoundary : Set where
  constructor motive-source-boundary
  field
    directStatementCanPayItsOwnDeclaredMotive : Bool
    declaredSupportEqualsImmortalityMotive : Bool
    declaredSupportEqualsPolicyAuthorship : Bool
    corporateCommitmentEqualsSovereignControl : Bool
    politicalIncentiveEqualsAdmittedThreatMaintenanceMotive : Bool

canonicalMotiveSourceBoundary : MotiveSourceBoundary
canonicalMotiveSourceBoundary =
  motive-source-boundary true false false false false
