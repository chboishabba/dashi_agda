module DASHI.Culture.MarxLabourUnionSourceBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- MARX / LABOUR / UNIONISM SOURCE BOUNDARY
--
-- Bounded source roles only.
--
-- Karl Marx, Capital, Volume I (1867), especially:
--   Ch. 6  Buying and Selling of Labour-Power
--   Ch. 10 The Working-Day
--   Ch. 13 Co-operation
-- Stable online edition: Marxists Internet Archive.
--
-- Bounded role: source context for wage-labour/capital relations, labour-power,
-- struggle over the working day, and co-operative/collective labour.  These
-- chapters do not thereby prove DASHI's finite control-topology or
-- non-factorability theorems, and this owner does not claim that one finite
-- carrier exhausts Marx's theory of capitalism.
--
-- International Labour Organization:
--   Convention No. 87, Freedom of Association and Protection of the Right to
--   Organise Convention, 1948.
--   Convention No. 98, Right to Organise and Collective Bargaining Convention,
--   1949.
--
-- Bounded role: C87 supplies freedom-of-association / organisation autonomy;
-- C98 supplies anti-union-discrimination, non-interference and collective-
-- bargaining source surfaces.  Neither convention is represented as a complete
-- theory of unionism or as proof authority for DASHI's governance mathematics.
------------------------------------------------------------------------

record LabourUnionSourceReference : Set where
  constructor labour-union-source-reference
  field
    authorOrInstitution : String
    work : String
    dateOrEdition : String
    exactScope : String
    identifier : String
    boundedRole : String

open LabourUnionSourceReference public

marxCapitalVolI : LabourUnionSourceReference
marxCapitalVolI = labour-union-source-reference
  "Karl Marx"
  "Capital, Volume I"
  "1867; bounded references to Chapters 6, 10 and 13"
  "labour-power exchange; working-day conflict; co-operation"
  "no DOI asserted; Marxists Internet Archive stable edition used for source recovery"
  "historical/theoretical source context only; does not prove DASHI exit, refusal, union or control-topology theorems"

iloConvention87 : LabourUnionSourceReference
iloConvention87 = labour-union-source-reference
  "International Labour Organization"
  "Freedom of Association and Protection of the Right to Organise Convention, 1948 (No. 87)"
  "adopted 9 July 1948"
  "workers/employers may establish and join organisations; organisations may determine rules, representatives, administration, activities and programmes without restrictive public interference"
  "ILO C087"
  "source context for freedom of association and organisational self-government; not a complete theory of labour power"

iloConvention98 : LabourUnionSourceReference
iloConvention98 = labour-union-source-reference
  "International Labour Organization"
  "Right to Organise and Collective Bargaining Convention, 1949 (No. 98)"
  "adopted 1 July 1949"
  "anti-union discrimination; protection from inter-organisational interference; collective bargaining"
  "ILO C098"
  "source context for organising and collective bargaining; does not by itself establish effective worker power in a concrete system"

------------------------------------------------------------------------
-- Source-role classification.
------------------------------------------------------------------------

data LabourUnionSourceRole : Set where
  marxianCapitalRelation
  marxianWorkingDayConflict
  marxianCooperation
  freedomOfAssociation
  organisationAutonomy
  antiUnionDiscrimination
  collectiveBargaining
  : LabourUnionSourceRole

------------------------------------------------------------------------
-- No-promotion types.
------------------------------------------------------------------------

data MarxSourceProvesDASHIControlTopology : Set where

data ILOConventionProvesEffectiveWorkerPower : Set where

data FreedomOfAssociationEqualsMaterialExit : Set where

data CollectiveBargainingEqualsMetaRuleAuthority : Set where

data UnionMembershipEqualsCapacityToWithdraw : Set where

data MarxianCapitalRelationExhaustsEveryCapitalism : Set where

data UnionismIsOneUniversalInstitutionalForm : Set where

marxSourceDoesNotProveDASHIControlTopology :
  MarxSourceProvesDASHIControlTopology → ⊥
marxSourceDoesNotProveDASHIControlTopology ()

iloConventionDoesNotProveEffectiveWorkerPower :
  ILOConventionProvesEffectiveWorkerPower → ⊥
iloConventionDoesNotProveEffectiveWorkerPower ()

freedomOfAssociationDoesNotEqualMaterialExit :
  FreedomOfAssociationEqualsMaterialExit → ⊥
freedomOfAssociationDoesNotEqualMaterialExit ()

collectiveBargainingDoesNotEqualMetaRuleAuthority :
  CollectiveBargainingEqualsMetaRuleAuthority → ⊥
collectiveBargainingDoesNotEqualMetaRuleAuthority ()

unionMembershipDoesNotEqualCapacityToWithdraw :
  UnionMembershipEqualsCapacityToWithdraw → ⊥
unionMembershipDoesNotEqualCapacityToWithdraw ()

marxianCapitalRelationDoesNotExhaustEveryCapitalism :
  MarxianCapitalRelationExhaustsEveryCapitalism → ⊥
marxianCapitalRelationDoesNotExhaustEveryCapitalism ()

unionismIsNotCollapsedToOneUniversalInstitutionalForm :
  UnionismIsOneUniversalInstitutionalForm → ⊥
unionismIsNotCollapsedToOneUniversalInstitutionalForm ()

record MarxLabourUnionSourceBoundary : Set where
  constructor marx-labour-union-source-boundary
  field
    marxSourceRecoveredForBoundedLabourRelation : Bool
    marxSourceRecoveredForBoundedLabourRelationIsTrue :
      marxSourceRecoveredForBoundedLabourRelation ≡ true

    iloC87SupportsFreedomOfAssociationSurface : Bool
    iloC87SupportsFreedomOfAssociationSurfaceIsTrue :
      iloC87SupportsFreedomOfAssociationSurface ≡ true

    iloC98SupportsCollectiveBargainingSurface : Bool
    iloC98SupportsCollectiveBargainingSurfaceIsTrue :
      iloC98SupportsCollectiveBargainingSurface ≡ true

    sourceProvesDASHINonFactorability : Bool
    sourceProvesDASHINonFactorabilityIsFalse :
      sourceProvesDASHINonFactorability ≡ false

    sourceExhaustsCapitalismOrUnionism : Bool
    sourceExhaustsCapitalismOrUnionismIsFalse :
      sourceExhaustsCapitalismOrUnionism ≡ false

canonicalMarxLabourUnionSourceBoundary : MarxLabourUnionSourceBoundary
canonicalMarxLabourUnionSourceBoundary =
  marx-labour-union-source-boundary
    true refl true refl true refl false refl false refl
