module DASHI.Education.FollowThroughPriorArtConsumerExact where

-- One-way dependency: the independent Follow Through consumer may import
-- Alice Brown corpus LOOM and Digital ESD canonical definitions as prior art.
-- This neither edits these owners nor entails collaborative ESD adoption.
open import Agda.Builtin.String using (String)
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Biology.AliceBrownCorpusLoom as Alice
import DASHI.Core.LoomEncoding as Loom
import DASHI.Core.ProjectionCategory as PC
import DASHI.Core.ProjectionFibre as PF
import DASHI.Education.DigitalESDEvidenceBraidTensionExact as Braid
import DASHI.Education.DigitalESDTransferablePedagogicalPrinciplesExact as Principles
import DASHI.Education.FollowThroughStandaloneNonFactorabilityExact as FT

alicePriorArt : Alice.AliceBrownCorpusLoom
alicePriorArt = Alice.canonicalAliceBrownCorpusLoom

loomPriorArt : Loom.LoomEncoding
  PC.canonicalProjectionCategory PF.canonicalProjectionFibre
loomPriorArt = Loom.canonicalLoomEncoding

esdBraidPriorArt : Braid.EvidenceBraidBoundary
esdBraidPriorArt = Braid.canonicalEvidenceBraidBoundary

principlePriorArt : Principles.TransferablePedagogicalPrinciple
principlePriorArt = Principles.constitutiveLearnerAgency

followThroughWitness :
  INF.NonFactorabilityWitness FT.academicProjection FT.voiceProjection
followThroughWitness = FT.academicDoesNotDetermineVoiceWitness

interopBoundary : String
interopBoundary =
  "Read-only prior-art reuse: no ESD evidence admission, edited team formalism or team attribution. Reverse transfer requires explicit collaborator approval."
