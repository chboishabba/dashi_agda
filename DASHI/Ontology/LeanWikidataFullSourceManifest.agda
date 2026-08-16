module DASHI.Ontology.LeanWikidataFullSourceManifest where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

data LeanDevelopmentLayer : Set where
  foundations classHierarchy propertyConstraints dataModel overview : LeanDevelopmentLayer

data DASHIIntegrationAnchor : Set where
  epistemicAnchor contextualClaimAnchor wikidataStatementAnchor : DASHIIntegrationAnchor
  derivationFibreAnchor candidateRoleAnchor repairReviewAnchor authorityBoundaryAnchor : DASHIIntegrationAnchor

record LeanSourceModule : Set where
  constructor leanSourceModule
  field
    moduleName : String
    sha256 : String
    layer : LeanDevelopmentLayer
    dashiAnchors : List DASHIIntegrationAnchor
open LeanSourceModule public

alignmentSource : LeanSourceModule
alignmentSource = leanSourceModule "RequestProject.Alignment" "bf65094dec4322a52af28b3b0c069d372f6af983aa5a20589807d421094d6d5e" classHierarchy (contextualClaimAnchor ∷ candidateRoleAnchor ∷ [])

classAlgebraSource : LeanSourceModule
classAlgebraSource = leanSourceModule "RequestProject.ClassAlgebra" "6ee3b2371498d67c159fe97389c9ca1e06144ad530e17554cb3f87968c9f899a" classHierarchy (epistemicAnchor ∷ [])

conceptsSource : LeanSourceModule
conceptsSource = leanSourceModule "RequestProject.Concepts" "d0143dd5742798f528317a205f48bee3d7ffb042b8c8af161be2dd71e72d47bc" classHierarchy (epistemicAnchor ∷ [])

coreSource : LeanSourceModule
coreSource = leanSourceModule "RequestProject.Core" "45cd840ee934849749a1b753db07a23685ec1f61dfb21b1c6d6c9a2e82e137b1" foundations (epistemicAnchor ∷ [])

diagnosticsSource : LeanSourceModule
diagnosticsSource = leanSourceModule "RequestProject.Diagnostics" "aded8468ee98d58fff214b5ce86509e83643437e3768e8536b9ecc467374034d" propertyConstraints (repairReviewAnchor ∷ [])

disjointUnionSource : LeanSourceModule
disjointUnionSource = leanSourceModule "RequestProject.DisjointUnion" "fd22cab707d6d3e1e2822f7799e2526f4c0a8cce35cbf61ab9d7dccc7e0cf41a" classHierarchy (epistemicAnchor ∷ [])

engineSource : LeanSourceModule
engineSource = leanSourceModule "RequestProject.Engine" "bcf2dd5f64d05f27db81bda588f5e7e24d0bd1aa4c51dc9b4c311b12a1c2f5be" foundations (derivationFibreAnchor ∷ [])

examplesSource : LeanSourceModule
examplesSource = leanSourceModule "RequestProject.Examples" "47a85eebfe88508cf7c2656a39fa6eb6252c9900dc8e56dfbb3f056b05ad1ef0" classHierarchy (epistemicAnchor ∷ [])

externalIdsSource : LeanSourceModule
externalIdsSource = leanSourceModule "RequestProject.ExternalIds" "ea0053d4e7cf7c85f66390b90e8ec6cc00bb779bd7a3a999513d4dfc734563b9" dataModel (candidateRoleAnchor ∷ [])

itemMergeSource : LeanSourceModule
itemMergeSource = leanSourceModule "RequestProject.ItemMerge" "613fa1ae942d1f205fb1cc695e66962ef686066714ad70cc428f0c5feb5435cb" classHierarchy (repairReviewAnchor ∷ [])

lexemesSource : LeanSourceModule
lexemesSource = leanSourceModule "RequestProject.Lexemes" "c360600d18a681675a953cf76fec661c2f593f741269e35cf0bf9a1a77a91539" dataModel (candidateRoleAnchor ∷ [])

mainSource : LeanSourceModule
mainSource = leanSourceModule "RequestProject.Main" "13953102d7bb4e5075c6f8dca5d1d3db5dd49c713a7757e45227159ea7de48c5" overview (authorityBoundaryAnchor ∷ [])

matchingSource : LeanSourceModule
matchingSource = leanSourceModule "RequestProject.Matching" "cd48a47c11a8b3f056b74d26ab2d520873199d8821a7d13247a250bc5d68a9d9" foundations (contextualClaimAnchor ∷ [])

mereologySource : LeanSourceModule
mereologySource = leanSourceModule "RequestProject.Mereology" "b81a8632dce181845e4c9ca500fb4a9a74df77aeb86a99392361eda991347c35" propertyConstraints (repairReviewAnchor ∷ [])

mergeSource : LeanSourceModule
mergeSource = leanSourceModule "RequestProject.Merge" "0f5177f6276e5b7a979eaa7fc6a9b4e34a2de3ed28260d4973e352f24ff46319" classHierarchy (contextualClaimAnchor ∷ [])

pathsSource : LeanSourceModule
pathsSource = leanSourceModule "RequestProject.Paths" "ee28fddb1893ca5953da5259b2d7f25bebfecfba5877621f4abe8915c36cd284" propertyConstraints (derivationFibreAnchor ∷ [])

propertiesSource : LeanSourceModule
propertiesSource = leanSourceModule "RequestProject.Properties" "e5818524e5039d056564420d6ae7f3e865a7e34b83c777970abf17e770507c34" propertyConstraints (derivationFibreAnchor ∷ [])

propertyConstraintsSource : LeanSourceModule
propertyConstraintsSource = leanSourceModule "RequestProject.PropertyConstraints" "ccf2483d91a7fd2bb93efbdb2d995eb97c1a86ccf449859fbd88fa8149e8556e" propertyConstraints (repairReviewAnchor ∷ [])

propertyEngineSource : LeanSourceModule
propertyEngineSource = leanSourceModule "RequestProject.PropertyEngine" "c58b496c07a2154a8d1543e706e76b8bf362ff7ee37c14486555b7296b7484eb" propertyConstraints (derivationFibreAnchor ∷ [])

provenanceSource : LeanSourceModule
provenanceSource = leanSourceModule "RequestProject.Provenance" "9eb56b22b697e8ab2d8f6ef32258d99d4ab174599b48afa3c8baa06061845a09" dataModel (contextualClaimAnchor ∷ [])

quantitiesSource : LeanSourceModule
quantitiesSource = leanSourceModule "RequestProject.Quantities" "4d3ad104bcd620b4cff81cf81773af1aa183a4c32b468a6b1df9b0452946cd95" dataModel (wikidataStatementAnchor ∷ [])

ranksSource : LeanSourceModule
ranksSource = leanSourceModule "RequestProject.Ranks" "56331f7dd0c158498e2e0fb80b0556c138dc6d1a12142756b200c29fe5c83a63" dataModel (wikidataStatementAnchor ∷ [])

rdfSource : LeanSourceModule
rdfSource = leanSourceModule "RequestProject.Rdf" "11a4d3fc6b152a022016d7c8639b89805d45352c9e08c16ec2a8172a2610f3cf" dataModel (derivationFibreAnchor ∷ contextualClaimAnchor ∷ [])

reachabilitySource : LeanSourceModule
reachabilitySource = leanSourceModule "RequestProject.Reachability" "c1dfe2f2d88b6625295965f2c9cf080bcac4e775eee257048a8e6d7b933e8695" foundations (derivationFibreAnchor ∷ [])

redundancySource : LeanSourceModule
redundancySource = leanSourceModule "RequestProject.Redundancy" "5278b5ef622343e0e47fceb83930c920180a8a7aec6b19c345a4030843b2907b" propertyConstraints (repairReviewAnchor ∷ [])

schemasSource : LeanSourceModule
schemasSource = leanSourceModule "RequestProject.Schemas" "b2004eca08d1329580004b9f81b53b51efda0c0cdc7c4e7c44d0a1bb18a02901" propertyConstraints (repairReviewAnchor ∷ [])

selfDescriptionSource : LeanSourceModule
selfDescriptionSource = leanSourceModule "RequestProject.SelfDescription" "fde15b5f577df943c399cfdf47904ac33fabd620eb1d374ade7f722f525061de" classHierarchy (contextualClaimAnchor ∷ [])

semanticsSource : LeanSourceModule
semanticsSource = leanSourceModule "RequestProject.Semantics" "c7c907d6ae07a4eed1621ac28977c9b8719540bb4c856f971d5bc90f7826f73d" classHierarchy (epistemicAnchor ∷ [])

sitelinksSource : LeanSourceModule
sitelinksSource = leanSourceModule "RequestProject.Sitelinks" "5b00c7ce658194d0311de7d6ab4a7a734bf08b88440cf37f91aa37a9400ed807" dataModel (candidateRoleAnchor ∷ [])

snaksSource : LeanSourceModule
snaksSource = leanSourceModule "RequestProject.Snaks" "e9bdeb2a6451d905b8d431278f8ef3328b16c1999c39f33561c8648feed7a54c" dataModel (wikidataStatementAnchor ∷ [])

statementConstraintsSource : LeanSourceModule
statementConstraintsSource = leanSourceModule "RequestProject.StatementConstraints" "09e8b516cf746325e43ad4da70f2ab430b1383074378410623b4747a8d4f63af" propertyConstraints (repairReviewAnchor ∷ [])

stratificationSource : LeanSourceModule
stratificationSource = leanSourceModule "RequestProject.Stratification" "6460e6e86f9225b599a91efa1852f03a6b9f8d9e7d299ca9ce5e2330931ad5b9" classHierarchy (derivationFibreAnchor ∷ [])

subsumptionSource : LeanSourceModule
subsumptionSource = leanSourceModule "RequestProject.Subsumption" "8e4b7cc1bf2740cc12ac0a18114e06400ceb8c5d2ffba192b5c20febb9a7d1f2" classHierarchy (epistemicAnchor ∷ [])

taxonomySource : LeanSourceModule
taxonomySource = leanSourceModule "RequestProject.Taxonomy" "20c97e31c7e0583f8ecec77dc23acbb09afc9c465909122aeb8c50456c528b0c" classHierarchy (epistemicAnchor ∷ [])

temporalSource : LeanSourceModule
temporalSource = leanSourceModule "RequestProject.Temporal" "b18fdfd99e897aa2e451f7d2211a9b0aa30b86c9c54aa8df3c3b76e461140a3c" dataModel (contextualClaimAnchor ∷ [])

termsSource : LeanSourceModule
termsSource = leanSourceModule "RequestProject.Terms" "3a93be2ecc7e369b75fb6c2559c8245e88d07e0385f3b4be668d2f0b028fdf14" dataModel (candidateRoleAnchor ∷ [])

timeValuesSource : LeanSourceModule
timeValuesSource = leanSourceModule "RequestProject.TimeValues" "1cd52250e2fa7f3f3266198cbce691a4217b765227d37ea891a4133d4f844374" dataModel (contextualClaimAnchor ∷ [])

typePropertiesSource : LeanSourceModule
typePropertiesSource = leanSourceModule "RequestProject.TypeProperties" "dadadef0ff3586ca61a0bbcf29a7c65bd98d398a5725dea28f5079905c633a9a" propertyConstraints (repairReviewAnchor ∷ [])

upperOntologySource : LeanSourceModule
upperOntologySource = leanSourceModule "RequestProject.UpperOntology" "6c13993abbe1b5aabe3dbe0bbaf2036ce7eef917fda3d270ac1b45153bea2cf1" classHierarchy (epistemicAnchor ∷ [])

allLeanSourceModules : List LeanSourceModule
allLeanSourceModules =
  alignmentSource ∷
  classAlgebraSource ∷
  conceptsSource ∷
  coreSource ∷
  diagnosticsSource ∷
  disjointUnionSource ∷
  engineSource ∷
  examplesSource ∷
  externalIdsSource ∷
  itemMergeSource ∷
  lexemesSource ∷
  mainSource ∷
  matchingSource ∷
  mereologySource ∷
  mergeSource ∷
  pathsSource ∷
  propertiesSource ∷
  propertyConstraintsSource ∷
  propertyEngineSource ∷
  provenanceSource ∷
  quantitiesSource ∷
  ranksSource ∷
  rdfSource ∷
  reachabilitySource ∷
  redundancySource ∷
  schemasSource ∷
  selfDescriptionSource ∷
  semanticsSource ∷
  sitelinksSource ∷
  snaksSource ∷
  statementConstraintsSource ∷
  stratificationSource ∷
  subsumptionSource ∷
  taxonomySource ∷
  temporalSource ∷
  termsSource ∷
  timeValuesSource ∷
  typePropertiesSource ∷
  upperOntologySource ∷
  []
