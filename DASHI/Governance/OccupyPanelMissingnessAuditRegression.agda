module DASHI.Governance.OccupyPanelMissingnessAuditRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.OccupyPanelMissingnessAuditExact as Audit

owsDevelopmentCountPinned : Audit.owsDevelopmentRecordCount Audit.canonicalMissingnessAudit ≡ 38
owsDevelopmentCountPinned = refl

durationObservedCountPinned : Audit.owsDurationObservedCount Audit.canonicalMissingnessAudit ≡ 6
durationObservedCountPinned = refl

lexicalCoveragePinned : Audit.owsLexicalObservedCount Audit.canonicalMissingnessAudit ≡ 38
lexicalCoveragePinned = refl

interfaceLexicalCoveragePinned : Audit.owsInterfaceLexicalObservedCount Audit.canonicalMissingnessAudit ≡ 38
interfaceLexicalCoveragePinned = refl

missingDurationNotZero : Audit.missingDurationImputedAsZero Audit.canonicalMissingnessBoundary ≡ false
missingDurationNotZero = refl

missingnessNotAssumedIgnorable : Audit.missingnessAssumedIgnorable Audit.canonicalMissingnessBoundary ≡ false
missingnessNotAssumedIgnorable = refl
