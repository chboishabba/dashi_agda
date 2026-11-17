module DASHI.Governance.BoloBoloOWSContemporaneousBurdenControlRegression where

import DASHI.Governance.BoloBoloOWSContemporaneousBurdenControlExact as Evidence

journalismIsNotMinutes :
  Evidence.contemporaneousJournalismEqualsPrimarySpokesMinutes
    Evidence.canonicalOWSContemporaneousBurdenControlBoundary ≡ false
journalismIsNotMinutes = refl

participantStatementIsNotMinutes :
  Evidence.participantStatementEqualsPrimarySpokesMinutes
    Evidence.canonicalOWSContemporaneousBurdenControlBoundary ≡ false
participantStatementIsNotMinutes = refl

selfReportedBurdenRetained :
  Evidence.participantStatementMaySupportSelfReportedBurden
    Evidence.canonicalOWSContemporaneousBurdenControlBoundary ≡ true
selfReportedBurdenRetained = refl

selfReportDoesNotGeneraliseSystem :
  Evidence.oneParticipantBurdenProvesGeneralSystemicBurden
    Evidence.canonicalOWSContemporaneousBurdenControlBoundary ≡ false
selfReportDoesNotGeneraliseSystem = refl
