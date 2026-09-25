module DASHI.Core.IrigarayContactRelationalRechartExact where

------------------------------------------------------------------------
-- IRIGARAY CONTACT RECHART
--
-- PRIMARY SOURCE BOUNDARY
--
-- Irigaray's "two lips" morphology motivates reciprocal contact and the
-- "neither one nor two" refusal of a forced unitary/binary reading.  Irigaray
-- does NOT number the lips or their contact as 0, 1, 2.
--
-- DASHI CONTRIBUTION
--
-- The ternary contact chart below deliberately chooses a local zero-address
-- for the constitutive between/contact relation.  This is a DASHI rechart,
-- not an Irigarayan numeral ontology.  It coexists with the repository's
-- existing classification chart in which code0 denotes neither-one-nor-two.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IrigarayLabialRelationalCarrierExact as Irigaray
import DASHI.Core.TernaryRoleCarrierExact as Ternary

data ContactRechartRole : Set where
  firstAspect : ContactRechartRole
  constitutiveContact : ContactRechartRole
  secondAspect : ContactRechartRole

dashiContactRechart :
  Ternary.TernaryRoleCode → ContactRechartRole
dashiContactRechart Ternary.code0 = constitutiveContact
dashiContactRechart Ternary.code1 = firstAspect
dashiContactRechart Ternary.code2 = secondAspect

zeroAddressIsContactInDashiRechart :
  dashiContactRechart Ternary.code0 ≡ constitutiveContact
zeroAddressIsContactInDashiRechart = refl

canonicalContact : Irigaray.Contact Irigaray.lipA Irigaray.lipB
canonicalContact = Irigaray.aTouchesB

contactReversesReciprocally :
  Irigaray.Contact Irigaray.lipB Irigaray.lipA
contactReversesReciprocally =
  Irigaray.contactSymmetric canonicalContact

data IrigarayNumbersContactAsZero : Set where
data ContactIsMereLack : Set where

irigarayDoesNotNumberContactAsZero :
  IrigarayNumbersContactAsZero → ⊥
irigarayDoesNotNumberContactAsZero ()

constitutiveContactIsNotDeclaredMereLack :
  ContactIsMereLack → ⊥
constitutiveContactIsNotDeclaredMereLack ()

contactNonseparability =
  Irigaray.labialContactIsNotEndpointAdditive

record IrigarayContactRechartBoundary : Set where
  constructor irigaray-contact-rechart-boundary
  field
    sourceNumbersLipsOrContact : Bool
    zeroAddressIsDashiLocalRechart : Bool
    contactRetainedAsConstitutiveRelation : Bool
    contactReducedToIndependentEndpoints : Bool
    contactRechartCreatesUniversalSexOntology : Bool

canonicalIrigarayContactRechartBoundary :
  IrigarayContactRechartBoundary
canonicalIrigarayContactRechartBoundary =
  irigaray-contact-rechart-boundary false true true false false
