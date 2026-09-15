module DASHI.Environment.BiocontrolFirstImplementationExact where

import DASHI.Core.FirstImplementationTimestampExact as Chronology

------------------------------------------------------------------------
-- Repository chronology only. These receipts establish when source objects
-- first existed in the repository. They do not establish type-checking,
-- kernel acceptance, mathematical correctness, publication, or external
-- priority.
------------------------------------------------------------------------

biocontrolExternalityFirstImplementation : Chronology.FirstImplementationReceipt
biocontrolExternalityFirstImplementation = Chronology.first-implementation-receipt
  "DASHI.Environment.BiocontrolExternalityExperimentExact"
  "38aaea92eb21cccc41ec38d03c3a55e5e1ab178e"
  "2026-09-14T23:49:58Z"
  "2026-09-15T09:49:58+10:00"
  "Australia/Brisbane (AEST, UTC+10)"
  Chronology.exactRepresentationImplemented
  Chronology.sourceCommittedOnly

biocontrolCostedChoiceFirstImplementation : Chronology.FirstImplementationReceipt
biocontrolCostedChoiceFirstImplementation = Chronology.first-implementation-receipt
  "DASHI.Environment.BiocontrolCostedExperimentChoiceExact"
  "0cd907c423041bade3b5cfa4e5a7d5aeca4b6c45"
  "2026-09-15T00:40:03Z"
  "2026-09-15T10:40:03+10:00"
  "Australia/Brisbane (AEST, UTC+10)"
  Chronology.exactRepresentationImplemented
  Chronology.sourceCommittedOnly

biocontrolSIQuantityFirstImplementation : Chronology.FirstImplementationReceipt
biocontrolSIQuantityFirstImplementation = Chronology.first-implementation-receipt
  "DASHI.Environment.BiocontrolSIQuantityExact"
  "d3144c596df0c6696ad7f908f69f8669f3ebe52b"
  "2026-09-15T01:15:16Z"
  "2026-09-15T11:15:16+10:00"
  "Australia/Brisbane (AEST, UTC+10)"
  Chronology.exactRepresentationImplemented
  Chronology.sourceCommittedOnly
