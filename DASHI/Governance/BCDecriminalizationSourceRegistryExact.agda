module DASHI.Governance.BCDecriminalizationSourceRegistryExact where

------------------------------------------------------------------------
-- EXACT SOURCE REGISTRY FOR THE BC DECRIMINALIZATION BUNDLE
--
-- This registry exists so the intervention-bundle consumer can remain compact
-- while author/title/DOI provenance stays explicit and machine-addressable.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record SourceReference : Set where
  constructor sourceReference
  field
    authorsOrInstitution : String
    title : String
    venue : String
    year : Nat
    doiOrIdentifier : String
    boundedRole : String

open SourceReference public

russellEtAlServiceOperations : SourceReference
russellEtAlServiceOperations = sourceReference
  "Cayley Russell; Savannah Torres-Salbach; Laura MacKinnon; Rita Shahin; Dylan Griffith; Kate Hodgson; Charlene Burmeister; Courtney Amoraal; Frank Crichlow; Sameer Imtiaz; Jürgen Rehm; Farihah Ali"
  "Exploring the early impacts of drug decriminalization on harm reduction and opioid agonist treatment service operations and delivery in British Columbia: insights from key informant interviews"
  "BMC Public Health 26:157"
  2026
  "10.1186/s12889-025-25479-x"
  "service-operation implementation evidence; staffing/resource/funding/training constraints; not a universal causal estimate of decriminalization"

scherEtAlAccessBarriers : SourceReference
scherEtAlAccessBarriers = sourceReference
  "Benjamin D. Scher; Becca Wood; Naomi Zakimi; Mieke Fraser; Alexis Crabtree; Kaitlin Fajber; Brooke Kinniburgh; O. Kara Loewen; Alissa Greer"
  "Access to health and harm reduction services during drug decriminalization in British Columbia, Canada: a mixed-method study"
  "BMC Public Health 26:1700"
  2026
  "10.1186/s12889-026-26978-1"
  "mixed-method evidence that barriers to health/harm-reduction access persisted during the pilot; legal reform alone may be insufficient without additional supports"

record RegistryBoundary : Set where
  constructor registryBoundary
  field
    fullAuthorMetadataInstalled : Bool
    titleMetadataInstalled : Bool
    doiMetadataInstalled : Bool
    sourceRoleBounded : Bool

canonicalRegistryBoundary : RegistryBoundary
canonicalRegistryBoundary = registryBoundary true true true true
