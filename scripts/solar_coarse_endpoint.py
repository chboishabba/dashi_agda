"""Whole-proof coarse endpoint enclosure and selective refinement.
Bounds must be externally justified on the SAME admissible domain.
No empirical admission, no automatic promotion of synthetic witnesses.
"""
from fractions import Fraction as Q

def interval(v):
    a,b=map(Q,v)
    if a>b:raise ValueError('reversed interval')
    return a,b

def endpoint_bounds(source,efficiency,paid,passive,gain):
    """Fixed-source branch: independent nonnegative interval bounds."""
    s,e,c,p=map(interval,(source,efficiency,paid,passive));g=Q(gain)
    if min(s[0],e[0],c[0],p[0])<0 or e[1]>1 or g<=0:raise ValueError('admissibility')
    lo=s[0]*e[0]-c[1]-p[1]-g
    hi=s[1]*e[1]-c[0]-p[0]-g
    return lo,hi

def backaction_bounds(natural,loss,paid,passive,gain):
    """Restored signed work branch, with independent source response.
    paid is net cost not already included in loss or natural.
    """
    n,l,c,p=map(interval,(natural,loss,paid,passive));g=Q(gain)
    if min(l[0],c[0])<0 or g<=0:raise ValueError('admissibility')
    return n[0]-l[1]-c[1]-p[1]-g,n[1]-l[0]-c[0]-p[0]-g

def verdict(bounds,witness=False,domain_upper=False,return_verified=False,source_verified=False):
    lo,hi=interval(bounds)
    if domain_upper and hi<0:return 'EMPTY_ON_DECLARED_DOMAIN'
    if lo>=0 and witness and return_verified and source_verified:return 'INHABITED_ON_DECLARED_MODEL'
    return 'UNRESOLVED'

def refine(parent,child):
    """Reject an inconsistent purported refinement rather than clip it."""
    a,b=interval(parent);c,d=interval(child)
    if not a<=c<=d<=b:raise ValueError('not a nested enclosure')
    return c,d

def priority(terms):
    """Order certified endpoint-error budgets, not arbitrary mesh sizes.
    terms maps residual owner to nonnegative bound in endpoint work units.
    """
    t={k:Q(v) for k,v in terms.items()}
    if any(v<0 for v in t.values()):raise ValueError('negative error radius')
    return sorted(t,key=lambda k:(-t[k],k))

def classify(center,terms,**gates):
    """Triangle enclosure, valid only if supplied radii jointly cover defect."""
    c=Q(center);radius=sum(map(Q,terms.values()),Q(0))
    order=priority(terms);bounds=(c-radius,c+radius)
    status=verdict(bounds,**gates)
    return dict(bounds=bounds,status=status,
        next_residual=order[0] if status=='UNRESOLVED' and order and Q(terms[order[0]])>0 else None,
        physical_admission=False)
