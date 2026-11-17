module DASHI.Governance.OccupyOWSManifestExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- CHECKSUM-PINNED OWS RECORD MANIFEST.
--
-- The uploaded OWS DOCX contains 45 records identified by the repeated
-- "Posted <date> by Ows Minutes" boundary. Titles/dates and normalized-record
-- hashes are DASHI parser outputs over the materialised corpus. They are not
-- attributed to the Kinna-Prichard curators as original minute authorship.
--
-- Validation integrity correction:
-- the first seven records had substantive content exposed during the local
-- structural audit before this manifest freeze. They are therefore forced to
-- development. Every fifth record among the remaining still-uninspected
-- records is prospectively protected as holdout.
------------------------------------------------------------------------

data SplitClass : Set where
  preFreezeInspectedDevelopment : SplitClass
  development : SplitClass
  prospectiveHoldout : SplitClass

record OWSRecord : Set where
  constructor owsRecord
  field
    corpusIndex : Nat
    postedDate : String
    sourceTitle : String
    normalizedTextSha256 : String
    splitClass : SplitClass

open OWSRecord public

recordCount : List OWSRecord → Nat
recordCount [] = 0
recordCount (_ ∷ xs) = 1 + recordCount xs

record1 = owsRecord 1 "September 10th, 2011" "NYCGA Minutes 9/10/11" "cd6998fd3d0ad85db9b5ab85c113f9d4edbe1c65458dfbbf0e490d7b7115cc1f" preFreezeInspectedDevelopment
record2 = owsRecord 2 "September 17th, 2011" "General Assembly Minutes 9/17/11" "af4df5f8195255143dce2a9f2f45127aa9b2fa3721e66ed0c477757a694269f8" preFreezeInspectedDevelopment
record3 = owsRecord 3 "September 18th, 2011" "General Assembly Minutes 9/18/11" "d495b4e4f1d0311e96691883262e8bff0a7bb8866981c6ff32b0637813d083bb" preFreezeInspectedDevelopment
record4 = owsRecord 4 "September 19th, 2011" "General Assembly Minutes 9/19 10PM" "f1917e6a26d399224d1a8f8dd9f2794760f58220a85f8aba6f1806bb1442eb2d" preFreezeInspectedDevelopment
record5 = owsRecord 5 "September 21st, 2011" "NYCGA Minutes 9/21/2011" "3e13b67819955893d4297fb1b195c4886c9e30f55b05785d08532850fe50ba1c" preFreezeInspectedDevelopment
record6 = owsRecord 6 "September 23rd, 2011" "NYCGA Minutes 9/23/11" "57ef5bc9bf100e212a10f406404c3f6858a4ce93dee542fe58e719bc58a21562" preFreezeInspectedDevelopment
record7 = owsRecord 7 "September 26th, 2011" "NYCGA Minutes 9/26/2011" "11fb1000c6f87360de49dcf255b6874ccc45b518c3fe4eee4605a3aac3e59b10" preFreezeInspectedDevelopment
record8 = owsRecord 8 "September 27th, 2011" "NYGA Minutes 9/27/11" "dc27e539ca95749ac43ebcd36580c5ce00eb398268faa14ed07a6564a43132a6" development
record9 = owsRecord 9 "September 28th, 2011" "NYCGA Minutes 9/28/2011 2pm" "7fac485567cc66eec82f00455c624f6339dd4b00de1539d7f7d0a4970fc261aa" development
record10 = owsRecord 10 "September 28th, 2011" "NYCGA Minutes 9/28/11, 7:30pm" "141ef5f98ef6c5c461281fcde291ed2d10a713917d8688c57c0820ddca70b51b" development
record11 = owsRecord 11 "September 29th, 2011" "General Assembly Minutes 9/29 7PM" "a72ce562b107d97ca634e88f8bdf080c1a84b15cef781842c869355150507f89" development
record12 = owsRecord 12 "September 30th, 2011" "NYCGA Minutes 9/30/2011, 7PM" "30e33e73fd05d2ff7e045912606d8ba46b55f5541d6eadf505ed8d08ae7a62e8" prospectiveHoldout
record13 = owsRecord 13 "October 1st, 2011" "NYCGA Minutes 10/1/2011" "87c51c3185f7861fc1c801a619d99bbb9cf2807fb6f7f63a3278770c3ffc55c4" development
record14 = owsRecord 14 "October 2nd, 2011" "NYCGA Minutes 10/2/2011, 7:30PM" "f0651bd4d2113d70b6988ccc2fbd4849651689fb674d597a5eefa5cf563ccbe0" development
record15 = owsRecord 15 "October 3rd, 2011" "NYCGA Minutes 10/3/2011, 7:30pm" "8944f961614eb4cc88102c57e72c53c991ebbc1145894e292e46e0005aa415eb" development
record16 = owsRecord 16 "October 4th, 2011" "NYCGA Minutes 10/4/2011" "9bac9d8bbefe1b99ff0195dd9dc8f339f9fb54adafa9cfc75d113255d3694525" development
record17 = owsRecord 17 "October 9th, 2011" "NYCGA Minutes 10/09/11, 7PM" "528f40c5aed23d81c7d6d9608d11c7703b3484400ab5a9a78f1cd4ab884752f5" prospectiveHoldout
record18 = owsRecord 18 "October 10th, 2011" "NYCGA Minutes 10/10/11, 7PM" "cb4df2826d4a7fcc256068d5d6e3ed23dd60a570c91e98a14b4eb86919824545" development
record19 = owsRecord 19 "October 11th, 2011" "NYCGA Minutes 10/11/2011" "719eb1cde30c2bf51b9fab6f7a72be39ed84cbb3543c257f65f3ceb6d3a0c09c" development
record20 = owsRecord 20 "October 12th, 2011" "NYCGA Minutes 10/12/2011" "aa4c0a3ddd69f331fe8af97c4905385a85af5af767b949a5492b35fcbe4705fa" development
record21 = owsRecord 21 "October 13th, 2011" "NYCGA Minutes 10/13/2011" "651cb0a58838e9c173acebd95a4f5f15ee085d4207904b26ff59de62681b648e" development
record22 = owsRecord 22 "October 15th, 2011" "NYCGA Minutes 10/15/2011" "5d95f9eeee686c96335910a96328b3582410e32bb0329ca2982c31ec82262646" prospectiveHoldout
record23 = owsRecord 23 "October 16th, 2011" "NYCGA Minutes 10/16/2011" "9577deb29c24a1a726638cc2a5133e0182e3af030248689cd54d793865b4418c" development
record24 = owsRecord 24 "October 17th, 2011" "NYCGA Minutes 10/17/2011" "2727aa95160ca5261e85ab957b09a40835cc408ecffce2d8199cc06400a9dff2" development
record25 = owsRecord 25 "October 18th, 2011" "NYCGA Minutes 10/18/2011" "e48174ea39b358503c85fc63ac57f9f89d2a79f82fd45db4554786cb8a4d20a6" development
record26 = owsRecord 26 "October 19th, 2011" "NYCGA Minutes 10/19/2011" "a84f944ebc96bb5fa2da4f53d706b0439c70b782dcf8cfc029324f47d216729c" development
record27 = owsRecord 27 "October 20th, 2011" "NYCGA Minutes 10/20/2011" "6a933668b5a5d39e1313bd30d00cd7edfe37375efec6418d81e0a0cd1f10976f" prospectiveHoldout
record28 = owsRecord 28 "October 21st, 2011" "NYCGA Minutes 10/21/2011" "0a2e590b02859cb8d4e86f57dfcbd85893761537a566226f4a413aff7a0b20e5" development
record29 = owsRecord 29 "October 23rd, 2011" "NYCGA Minutes 10/23/2011" "80973583b8c48034f5f9197c586e09919a31e67a9bc174b92dd21ad0eb489772" development
record30 = owsRecord 30 "October 24th, 2011" "NYCGA Minutes 10/24/2011" "129fe2b6f3e7440592b849471d5b4d0ffa2fb97efdf3afaca4170622fd91771f" development
record31 = owsRecord 31 "October 25th, 2011" "NYCGA Minutes 10/25/2011" "b4fa197ba59e72029b3d9465155fbe0145b3620a1a442c2d43e7e63c106cd988" development
record32 = owsRecord 32 "October 26th, 2011" "NYCGA Minutes 10/26/2011" "47a18696dde23ca74f7a9f06fed8aea7e748e499bfdf21c1a1609a7d40132770" prospectiveHoldout
record33 = owsRecord 33 "October 28th, 2011" "NYCGA Minutes 10/28/2011" "ffca36f2159f71323bc7b05516c945625dc3207364dcde330f4a6025b2bcffcf" development
record34 = owsRecord 34 "October 29th, 2011" "NYCGA Minutes 10/29/2011" "74ce748a7d95a36e2e8e23f04966be3107cbc24347a2b66d1daae3bd2939bfab" development
record35 = owsRecord 35 "October 30th, 2011" "NYCGA Minutes 10/30/2011" "3501d36dc2b19076c8911149e8564c3af7a6a1838d8fac2c40cd2e4315d6e0bc" development
record36 = owsRecord 36 "October 31st, 2011" "NYCGA Minutes 10/31/2011" "a60a8271906f069ba1c3c572dfd607a2061b2bba464baf818ed4a2ed5eae6e74" development
record37 = owsRecord 37 "November 1st, 2011" "NYCGA Minutes 11/1/2011" "51cb6b4659f7d30cfd8138a55fa14064f57f6ba251c4238b840ce27b80953aec" prospectiveHoldout
record38 = owsRecord 38 "November 2nd, 2011" "NYCGA Minutes 11/2/2011" "84dcd079088b730af765178e389c1955b90a03c69881a45bff37e595379c16ba" development
record39 = owsRecord 39 "November 3rd, 2011" "NYCGA Minutes 11/3/2011" "957124797c05a1292285578e92eca0d77c9fe21b81ade429cd5ce6313dea49e5" development
record40 = owsRecord 40 "November 4th, 2011" "NYCGA Minutes 11/4/2011" "c79f47f7ed78b6dcdc8ce470eac4d6b139f93d63f0e04e40690568088cc199f1" development
record41 = owsRecord 41 "November 6th, 2011" "NYCGA Minutes 11/6/2011" "6b2cacad8bcc2177070cf742ffe6645ec08bb5dcd67590fef45c8dbea0d242bd" development
record42 = owsRecord 42 "November 8th, 2011" "NYCGA Minutes 11/8/2011" "6e93fbe07a5e8376d9e607c64782989b8002aa8d8176b7675812a39da1013c81" prospectiveHoldout
record43 = owsRecord 43 "November 10th, 2011" "NYCGA Minutes 11/10/2011" "7b3c427a7ea458f93b78d616216417cb3a54bd6e178d5df997b1a1400326c6f0" development
record44 = owsRecord 44 "November 12th, 2011" "NYCGA Minutes 11/12/2011" "31da65810c8b70b6259adcc618b485ea527d7a29485243fe218d5f0b21a5d1e3" development
record45 = owsRecord 45 "November 15th, 2011" "NYCGA Minutes 11/15/2011" "3c009c612fc50c1b3c5fc1cfc68c611b0a0acdb61ec1b10cfdbfd7c081171ae8" development

canonicalOWSRecords : List OWSRecord
canonicalOWSRecords =
  record1 ∷ record2 ∷ record3 ∷ record4 ∷ record5 ∷ record6 ∷ record7 ∷
  record8 ∷ record9 ∷ record10 ∷ record11 ∷ record12 ∷ record13 ∷ record14 ∷ record15 ∷ record16 ∷ record17 ∷
  record18 ∷ record19 ∷ record20 ∷ record21 ∷ record22 ∷ record23 ∷ record24 ∷ record25 ∷ record26 ∷ record27 ∷
  record28 ∷ record29 ∷ record30 ∷ record31 ∷ record32 ∷ record33 ∷ record34 ∷ record35 ∷ record36 ∷ record37 ∷
  record38 ∷ record39 ∷ record40 ∷ record41 ∷ record42 ∷ record43 ∷ record44 ∷ record45 ∷ []

preFreezeInspectedRecords : List OWSRecord
preFreezeInspectedRecords = record1 ∷ record2 ∷ record3 ∷ record4 ∷ record5 ∷ record6 ∷ record7 ∷ []

prospectiveHoldoutRecords : List OWSRecord
prospectiveHoldoutRecords =
  record12 ∷ record17 ∷ record22 ∷ record27 ∷ record32 ∷ record37 ∷ record42 ∷ []

splitManifestSha256 : String
splitManifestSha256 = "83982d16ef8bce87a3fc7d099203e0ed594e47359b48b9973b7bcb67af0d1bf1"

localJSONManifestSha256 : String
localJSONManifestSha256 = "cab08f089daee3eb2983cfb180e9ecc81b069d93d986a0f6ad1035a4161048e1"

record OWSManifestBoundary : Set where
  constructor owsManifestBoundary
  field
    preFreezeInspectedRecordsForcedDevelopment : Bool
    everyFifthRuleAppliedToAlreadyInspectedRecords : Bool
    titleDateMetadataTreatedAsOutcome : Bool
    normalizedRecordHashTreatedAsSemanticInspection : Bool
    holdoutSubstantiveContentsInspectedDuringManifestFreeze : Bool
    holdoutAssignmentMayChangeAfterOutcomeInspection : Bool

    materialisedManifestFrozen : Bool
    prospectiveHoldoutAssignmentFrozen : Bool

open OWSManifestBoundary public

canonicalManifestBoundary : OWSManifestBoundary
canonicalManifestBoundary =
  owsManifestBoundary
    true
    false
    false
    false
    false
    false
    true
    true

canonicalOWSManifestReceipt : GenericReceipt.GenericReceipt
canonicalOWSManifestReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "checksum-pinned Occupy Wall Street record manifest"
    "DASHI.Governance.OccupyOWSManifestExact"
    "canonicalManifestBoundary"
    "pins forty-five parser-detected OWS records from the materialised DOCX, per-record normalized-text hashes, the seven records exposed before freeze as forced development, and seven still-uninspected prospectively protected holdouts selected every fifth among the remaining records"
    "record titles/dates and hashes are DASHI parsing metadata rather than outcome claims; protected holdout substantive contents remain uninspected at manifest freeze and assignment cannot change after outcome inspection"
    "agda -i . DASHI/Governance/OccupyOWSManifestRegression.agda"
