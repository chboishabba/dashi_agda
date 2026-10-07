module DASHI.Governance.OccupyFilesCorpusReceiptRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.OccupyFilesCorpusReceiptExact as Corpus

packageHashPinned :
  Corpus.packageSha256 Corpus.canonicalOccupyFilesCorpusReceipt
  ≡ "b8a2e36ae46328dfec375ab3b3a859c45e5bf626d92d130db43855f19c8c75fb"
packageHashPinned = refl

memberCountPinned :
  Corpus.nonDirectoryMemberCount Corpus.canonicalOccupyFilesCorpusReceipt ≡ 49
memberCountPinned = refl

readmeOWSCountPinned :
  Corpus.readmeReportedOWSGAMinuteSets Corpus.canonicalOccupyFilesCorpusReceipt ≡ 45
readmeOWSCountPinned = refl

parserOWSCountPinned :
  Corpus.parserDetectedOWSRecords Corpus.canonicalOccupyFilesCorpusReceipt ≡ 45
parserOWSCountPinned = refl

readmeLondonCountPinned :
  Corpus.readmeReportedLondonGAMinuteSets Corpus.canonicalOccupyFilesCorpusReceipt ≡ 46
readmeLondonCountPinned = refl

parserLondonFileCountPinned :
  Corpus.parserDetectedLondonFiles Corpus.canonicalOccupyFilesCorpusReceipt ≡ 46
parserLondonFileCountPinned = refl

readmeOaklandCountIsCuratorMetadata :
  Corpus.readmeOaklandCountParserVerified Corpus.canonicalOccupyFilesCorpusBoundary ≡ false
readmeOaklandCountIsCuratorMetadata = refl

curationIsNotMinuteAuthorship :
  Corpus.curatorsAuthoredUnderlyingMinutes Corpus.canonicalOccupyFilesCorpusBoundary ≡ false
curationIsNotMinuteAuthorship = refl

ourParserDoesNotBecomeArchiveAuthor :
  Corpus.dashiParserAuthoredUnderlyingMinutes Corpus.canonicalOccupyFilesCorpusBoundary ≡ false
ourParserDoesNotBecomeArchiveAuthor = refl
