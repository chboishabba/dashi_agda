# DASHI actual blocker-break requirements

This replaces the previous packaging-style bundle.

The previous bundle was correctly judged as not collapsing the board because it
only collected existing theorem surfaces and stamped status.  These modules do
not do that.  They state the missing witnesses needed to actually change the
current blocker board.

## Chemistry

`ChemistryRightLimitsNondegenerateQuotientCouplingRequirement.agda`

The existing quotient-visible observable and triple coupling are still only
stable compatibility.  To break the atomic blocker, an owner must provide a
non-degenerate relation: two supports with the defect/promoted pair held fixed,
while the quotient observable separates them, plus a chemistry-facing relation
witness.

## MDL / continuum

`CanonicalToNoncanonicalMdlGlobalObligationImpossible.agda`

Proves the old global source-schedule obligation is impossible against the
current CR obstruction.  This prevents the board from asking for a theorem that
cannot exist under the current target.

`CanonicalToNoncanonicalMdlAlignedChannelRequirement.agda`

States the honest positive target: source-to-schedule and schedule-to-noncanonical
must land on the same carrier/channel.

`CanonicalToNoncanonicalMdlCRRetargetRequirement.agda`

States the alternative CR route: keep the CR source bridge, but introduce an
explicit replacement CR noncanonical MDL target instead of pretending the current
obstructed target aligns.

## What this bundle does not do

It does not claim chemistry closure.
It does not claim global MDL closure.
It does not modify brain/DNA adjacent lanes.
It introduces no postulates, holes, or blockerBroken flags.
