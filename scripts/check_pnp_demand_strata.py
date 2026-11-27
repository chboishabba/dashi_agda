"""Demand-local separator folds and certified capacity exclusions.

All keys are in original absolute column coordinates, on a fixed source P.
A width/budget refusal is not an exclusion. Counts refer to original points.
"""
from check_pnp_affine_normal_components import bits, canon, chart, lift, satisfies
from check_pnp_normal_boundary_join import value, tree, span
from check_pnp_separator_row_strata import build


class ProbeLimit(Exception): pass


class Allowance:
    def __init__(self, B, cap):
        self.B=B; self.left=cap; self.stats=B.stats
    def pay(self, tag, n=1):
        if n>self.left:raise ProbeLimit
        self.B.pay(tag,n);self.left-=n


def bounded_fold(n,R,H,caps,B,leaf_cap=8,seam_cap=8):
    """Return (exact count, witness) or None on width refusal.
    Unlike incumbent observation, the demand need not contain the incumbent.
    Negative capacity is a genuine empty constraint, not a width refusal.
    """
    assert len(R)==len(caps) and H==canon(H)
    if any(c<1 for c in caps):return 0,None # retained odd row parity
    G=build(n,R,H,B,leaf_cap,seam_cap)
    if G is None:return None
    _,_,_,u,V,nodes,top,_=G;tables=[]
    for node in nodes:
        T={}
        def put(k,c,h):
            if k in T:T[k]=(T[k][0]+c,T[k][1])
            else:T[k]=(c,h)
        if len(node)==2:
            e,L=node
            for k,w,h in L:
                B.pay('demand_strata_leaf')
                if w<=caps[e]:put(k,1,h)
        else:
            l,r,L=node;A=tables[l];C=tables[r]
            for i,j,k in L:
                B.pay('demand_strata_pair')
                if i not in A or j not in C:continue
                a,h=A[i];b,g=C[j]
                B.pay('demand_strata_fold',1+len(V)+len(h)+len(g));put(k,a*b,h+g)
        tables.append(T)
    if 0 not in tables[top]:return 0,None
    c,h=tables[top][0];B.pay('demand_strata_reopen',1+n*(1+len(H))+len(V)*(1+len(h))+sum(r.bit_count() for r in R))
    Q=canon(h);assert Q is not None
    y=lift(u,V,chart(len(V),Q)[0]);assert satisfies(y,H,()) and all((r&y).bit_count()<=w for r,w in zip(R,caps))
    return c,y


def subtract(H,E,B):
    """Disjoint affine cells H\\E (canonical first-violated-equation fold)."""
    B.pay('demand_intersection',1+len(H)+len(E))
    if canon(H+E) is None:return (H,)
    out=[];Q=H
    for a,b in E:
        B.pay('demand_subtract',1+len(Q));C=canon(Q+((a,b^1),))
        if C is not None:out.append(C)
        Q=canon(Q+((a,b),));assert Q is not None
    return tuple(out)


def volume(n,cells):return sum(1<<(n-len(H)) for H in cells)


def projector(H,x):
    """Factorized character projector: product of (1+(-1)^(b+a.x))/2.
    No Fourier dictionary is expanded. This is a representation, not a proof.
    """
    v=1
    for a,b in H:v*=int((a&x).bit_count()%2==b)
    return v


class Ledger:
    def __init__(self,n,R,P):
        assert P==canon(P) and canon(P+tuple((r,1) for r in R))==P
        self.n=n;self.R=tuple(R);self.P=P;self.empty=[]
    def _demand(self,H,caps):
        assert len(caps)==len(self.R);return canon(self.P+tuple(H)),tuple(caps)
    def _applicable(self,caps,B):
        for H,C,why in self.empty:
            B.pay('demand_cache_scope',1+len(C))
            if all(a<=b for a,b in zip(caps,C)):yield H
    def remaining(self,H,caps,B,cell_cap=128):
        H,caps=self._demand(H,caps)
        cells=() if H is None else (H,)
        for E in self._applicable(caps,B):
            out=[]
            for Q in cells:
                out.extend(subtract(Q,E,B))
                if len(out)>cell_cap:raise ProbeLimit
            cells=tuple(out)
            if not cells:break
        return cells
    def _record(self,H,caps,why,B):
        # Only called after a sound exact consumer or replayed donor returns empty.
        B.pay('demand_cache_record',1+len(H)+len(caps));self.empty.append((H,caps,why))
    def record_character(self,H,caps,cert,B):
        from check_pnp_capacity_character import verify_certificate
        H,caps=self._demand(H,caps)
        if H is None or not verify_certificate(self.n,self.R,H,caps,cert,B):
            raise AssertionError('invalid capacity certificate')
        self._record(H,caps,cert,B)
    def join_character_siblings(self,H,caps,a,B):
        from check_pnp_capacity_character import Certificate
        H,caps=self._demand(H,caps)
        if H is None:return False
        Q=tuple(canon(H+((a,b),)) for b in (0,1))
        if any(q is None or len(q)!=len(H)+1 for q in Q):return False
        children={}
        for q,C,why in self.empty:
            B.pay('demand_sibling_scope',1+len(C)+len(q))
            if q in Q and C==caps and isinstance(why,Certificate):children[q]=why
        if len(children)!=2:return False
        self.record_character(H,caps,Certificate('siblings',normal=a,children=tuple(children[q] for q in Q)),B)
        return True
    def probe(self,H,caps,B,leaf_cap=8,seam_cap=8,cell_cap=128,character_degree=-1):
        H,caps=self._demand(H,caps)
        if H is None:return 'EMPTY',0,None
        cells=self.remaining(H,caps,B,cell_cap)
        if not cells:return 'EMPTY',0,None
        # Partial completion can learn exact empty cells, never promote UNKNOWN.
        total=0;y=None;unknown=False
        for Q in cells:
            if character_degree>=0:
                try:
                    ans=bounded_fold(self.n,self.R,Q,caps,Allowance(B,max(0,B.left//3)),leaf_cap,seam_cap)
                except ProbeLimit:ans=None
            else:ans=bounded_fold(self.n,self.R,Q,caps,B,leaf_cap,seam_cap)
            if ans is None:
                if character_degree>=0:
                    from check_pnp_capacity_character import discover_certificate
                    from check_pnp_capacity_signed import observe
                    # Use the same local allowance and original scope; never treat
                    # an incomplete positive mass observation as an exact count.
                    # A forest refusal must not starve the character consumer.
                    # Reserve disjoint portions of the current allowance.
                    try:
                        A=Allowance(B,max(0,B.left//2))
                        I,=observe(self.n,self.R,Q,caps,A)
                        if I.upper==0:
                            self._record(Q,caps,'signed_capacity_upper_zero',B);continue
                        if I.witness is not None:
                            total+=I.lower;y=I.witness if y is None else y
                            unknown|=I.lower!=I.upper
                            continue
                    except ProbeLimit:pass
                    try:
                        A=Allowance(B,max(0,B.left//2))
                        cert=discover_certificate(self.n,self.R,Q,caps,A,character_degree)
                        if cert is not None:
                            self.record_character(Q,caps,cert,A);continue
                    except ProbeLimit:pass
                    try:
                        from check_pnp_capacity_contraction import contract
                        w=contract(self.n,self.R,Q,caps,Allowance(B,max(0,B.left)))
                        if w is not None:
                            total+=1;y=w if y is None else y;unknown=True;continue
                    except ProbeLimit:pass
                unknown=True;continue
            c,w=ans
            if c==0:self._record(Q,caps,'exact_separator_fold',B)
            else:total+=c;y=w if y is None else y
        if unknown:return 'UNKNOWN',total,y # positive lower mass may still supply witness
        return ('SAT' if total else 'EMPTY'),total,y
    def coverage(self,H,caps,B,cell_cap=128):
        """Exact unresolved *affine candidate* volume, not feasible mass."""
        H,caps=self._demand(H,caps)
        return (0,0) if H is None else (1<<(self.n-len(H)),volume(self.n,self.remaining(H,caps,B,cell_cap)))


def conditioned_cut_rank(U,V,L):
    """Dimension of the new seam after quotienting by demand-normal span L."""
    return len(span(U+L))+len(span(V+L))-len(span(U+V+L))-len(span(L))


def conditioned_cut_defect(U,V,L):
    """Removed and introduced shared normal dimensions, separately."""
    L=span(L);U=span(U);V=span(V)
    shared=len(U)+len(V)-len(span(U+V))
    iu=len(U)+len(L)-len(span(U+L))
    iv=len(V)+len(L)-len(span(V+L))
    iuv=len(span(U+V))+len(L)-len(span(U+V+L))
    # dim(U intersect V intersect L) from explicit normal intersection.
    from check_pnp_normal_boundary_join import intersection
    n=max((a.bit_length() for a in U+V+L),default=0)
    removed=len(intersection(n,intersection(n,U,V),L))
    created=iuv-iu-iv+removed
    assert created>=0
    new=shared-removed+created
    assert new==conditioned_cut_rank(U,V,L)
    return new,removed,created


def choose_normal(n,R,H,B):
    """Score a basis of the widest seam on ALL fixed cuts, not just that seam.
    Both child fibres must be retained; no claim of inhabited orientation.
    A new tree may have a different profile after conditioning.
    """
    u,V=chart(n,H);d=len(V)
    if not d:return None
    F=tuple(tuple((value(V,1<<j),u>>j&1) for j in bits(r)) for r in R)
    B.pay('demand_split_tree',1+n*(1+d)+sum(map(len,F)))
    root,boundary,space=tree(d,F,B);best=();cuts=[];full=root[0]
    todo=[root]
    while todo:
        mask,A,C=todo.pop();D=boundary(mask)
        if len(D)>len(best):best=D
        if mask!=full:cuts.append((space(mask),space(full^mask)))
        if A is not None:todo.extend((A,C))
    def score(s):
        w=[];created=0
        for U,W in cuts:
            B.pay('demand_cut_score',1+d*(1+len(U)+len(W))**2)
            rank,removed,added=conditioned_cut_defect(U,W,(s,))
            w.append(rank);created+=added
        return max(w,default=0),sum(w),created,s
    s=min(best or (1,),key=score)
    piv={a.bit_length()-1 for a,b in H};free=[i for i in range(n) if i not in piv]
    return sum(1<<free[i] for i in bits(s))


def solve_cover(n,R,P,B,leaf_cap=8,seam_cap=8,nodes=32,probe_cap=1000000,
                donor_depth=1,character_degree=-1,cell_cap=128,ledger=None):
    """Bounded original-cover portfolio. No assumed inhabited branch.
    One shared parent clock; local refusals permit complementary observations.
    Returns (witness, decisive), with UNKNOWN on remaining unresolved cells.
    """
    L=ledger if ledger is not None else Ledger(n,R,P)
    assert (L.n,L.R,L.P)==(n,tuple(R),P)
    caps=(1,)*len(R);F=tuple(tuple((1<<j,0) for j in bits(r)) for r in R)
    pending=[P];unresolved=False
    for _ in range(nodes):
        if not pending:break
        H=pending.pop();B.pay('demand_node',1+len(H))
        try:
            cells=L.remaining(H,caps,Allowance(B,probe_cap),cell_cap)
        except ProbeLimit:unresolved=True;continue
        if not cells:continue
        # Process the remaining union by disjoint cells, never by overlapping labels.
        if cells!=(H,):pending.extend(reversed(cells));continue
        if donor_depth:
            from check_pnp_exact_cover_pair_hull import affine_disjunctive_close
            try:
                Q,y=affine_disjunctive_close(n,F,Allowance(B,probe_cap),H,depth=donor_depth,rounds=1)
                if Q is None:L._record(H,caps,'disjunctive_hull',B);continue
                if y is not None:
                    assert satisfies(y,H,()) and all((r&y).bit_count()==1 for r in R);return y,True
                assert canon(H+Q)==Q
                for E in subtract(H,Q,B):L._record(E,caps,'disjunctive_refinement',B)
                H=Q
            except ProbeLimit:pass
        if character_degree>=0:
            from check_pnp_character_ideal import demand_character_close
            try:
                Q,y=demand_character_close(n,F,H,Allowance(B,probe_cap),degree=character_degree,max_pivots=256,section_cap=8,path_steps=8,adaptive_nodes=8,adaptive_degree=0,adaptive_provenance=True)
                if Q is None:L._record(H,caps,'character_close',B);continue
                if y is not None:
                    assert satisfies(y,H,()) and all((r&y).bit_count()==1 for r in R);return y,True
                assert canon(H+Q)==Q
                for E in subtract(H,Q,B):L._record(E,caps,'character_refinement',B)
                H=Q
            except ProbeLimit:pass
        try:
            status,c,y=L.probe(H,caps,Allowance(B,probe_cap),leaf_cap,seam_cap,cell_cap,character_degree)
            if y is not None:return y,True
            if status=='EMPTY':continue
        except ProbeLimit:pass
        try:a=choose_normal(n,R,H,Allowance(B,probe_cap))
        except ProbeLimit:unresolved=True;continue
        if a is None:
            y=chart(n,H)[0];B.pay('demand_terminal_verify',1+sum(r.bit_count() for r in R))
            if all((r&y).bit_count()==1 for r in R):return y,True
            L._record(H,caps,'singleton_verify',B);continue
        order=(1,0)
        if character_degree>=0:
            from check_pnp_capacity_signed import observe_ledger,select
            try:
                A=Allowance(B,probe_cap)
                I=observe_ledger(L,H,caps,a,A,cell_cap,leaf_cap,seam_cap)
                for v in I:
                    if v.witness is not None:return v.witness,True
                # A positive lower bound is a real inhabited-child receipt.
                # Only such a receipt permits dropping other pending demands.
                b=select(I)
                if b is not None:
                    B.pay('demand_inhabited_rank_contraction')
                    pending.clear();unresolved=True;order=(b,)
                else:
                    order=tuple(b for b in (1,0) if I[b].upper>0)
            except ProbeLimit:pass
        for b in order:
            Q=canon(H+((a,b),));assert Q is not None and len(Q)==len(H)+1;pending.append(Q)
        B.pay('demand_split_children',2)
    return None,not pending and not unresolved


def rooted_probe(L,x,e,H,B,leaf_cap=8,seam_cap=8,cell_cap=128,character_degree=-1):
    """Strict root in absolute candidate coordinates; cache reusable cap implications."""
    assert 0<=e<len(L.R) and satisfies(x,L.P,())
    caps=[(r&x).bit_count() for r in L.R];caps[e]-=2
    status,c,y=L.probe(H,tuple(caps),B,leaf_cap,seam_cap,cell_cap,character_degree)
    if y is not None:
        q=tuple((r&x).bit_count()-(r&y).bit_count() for r in L.R)
        assert all(a>=0 and a%2==0 for a in q) and q[e]>=2
    return status,c,None if y is None else x^y
