module DASHI.Ontology.LeanWikidataSourceSnapshot where

open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Concrete provenance for the James Michael DuPont / Aristotle Wikidata Lean
-- snapshot supplied on 2026-08-16.
--
-- Aristotle request:
--   ae06ae06-2580-422a-8fc3-92aeaaca8762
--
-- The uploaded archive contains the actual RequestProject Lean sources.  These
-- constants pin the exact source-facing names used by the certificate bridge;
-- they are provenance data, not an assertion that DASHI kernel-checks Lean.
------------------------------------------------------------------------

aristotleRequestId : String
aristotleRequestId = "ae06ae06-2580-422a-8fc3-92aeaaca8762"

classAlgebraModule : String
classAlgebraModule = "RequestProject.ClassAlgebra"

classAlgebraSha256 : String
classAlgebraSha256 =
  "6ee3b2371498d67c159fe97389c9ca1e06144ad530e17554cb3f87968c9f899a"

rdfModule : String
rdfModule = "RequestProject.Rdf"

rdfSha256 : String
rdfSha256 =
  "11a4d3fc6b152a022016d7c8639b89805d45352c9e08c16ec2a8172a2610f3cf"

unionChecker : String
unionChecker = "Wikidata.KB.unionOk"

unionSoundnessTheorem : String
unionSoundnessTheorem = "Wikidata.KB.isUnion_of_unionOk"

intersectionChecker : String
intersectionChecker = "Wikidata.KB.interOk"

intersectionSoundnessTheorem : String
intersectionSoundnessTheorem = "Wikidata.KB.isIntersection_of_interOk"

rdfEntailmentSoundness : String
rdfEntailmentSoundness = "Wikidata.Rdf.entails_sound"

rdfSubclassExactness : String
rdfSubclassExactness = "Wikidata.Rdf.entails_iff_isSubclassOf"

------------------------------------------------------------------------
-- Exact worked-fragment identifiers from ClassAlgebraExample.artistKB.
------------------------------------------------------------------------

artistQid : String
artistQid = "wd:Q483501"

painterQid : String
painterQid = "wd:Q1028181"

sculptorQid : String
sculptorQid = "wd:Q1281618"

artistUnionParts : String
artistUnionParts = "wd:Q1028181|wd:Q1281618"
