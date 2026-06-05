module DASHI.Physics.Closure.YMResidualMembershipRefinementAuthority where

import DASHI.Physics.Closure.YMResolvedMembershipSemantics as Membership
import DASHI.Physics.Closure.YMResidualTermMembershipResolver as Resolver

------------------------------------------------------------------------
-- Shared authority for the weak-to-strong PolymerIn refinement used in Gate B.
--
-- The underlying Balaban/Eriksson statement that weak polymer witnesses refine to
-- strong residual-term membership is the only non-derivable step that currently
-- remains outside the local residual-support architecture.

postulate
  erikssonProp31PolymerInStrongResidualMembershipAuthority :
    Membership.PolymerInRefinesToStrongResidualMembership

resolverFromStrongResidualRefinement :
  Membership.PolymerInRefinesToStrongResidualMembership →
  Resolver.PolymerInResidualTermResolver
resolverFromStrongResidualRefinement refinement =
  record
    { residualTermForMembership =
        λ S γ member →
          Membership.StrongResidualPolymerMembership.resolvedResidualTerm
            (Membership.PolymerInRefinesToStrongResidualMembership.refinePolymerIn
              refinement S γ member)
    ; residualTermForMembershipIsResidual =
        λ S γ member →
          Membership.StrongResidualPolymerMembership.resolvedResidualFlag
            (Membership.PolymerInRefinesToStrongResidualMembership.refinePolymerIn
              refinement S γ member)
    ; membershipSupportLinksUseResidualTerm =
        λ S γ member →
          Membership.StrongResidualPolymerMembership.resolvedSupportLinksUseResidualTerm
            (Membership.PolymerInRefinesToStrongResidualMembership.refinePolymerIn
              refinement S γ member)
    }

balabanResidualRefinementAuthority :
  Membership.PolymerInRefinesToStrongResidualMembership
balabanResidualRefinementAuthority =
  erikssonProp31PolymerInStrongResidualMembershipAuthority

balabanPolymerInResidualTermResolverAuthority :
  Resolver.PolymerInResidualTermResolver
balabanPolymerInResidualTermResolverAuthority =
  resolverFromStrongResidualRefinement balabanResidualRefinementAuthority
