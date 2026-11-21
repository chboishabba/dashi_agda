#!/usr/bin/env python3
"""S4c.7: finite enabled transfer histories; no drug or kinetic calibration."""
from collections import defaultdict
from itertools import combinations
from sympy import Matrix, eye, zeros, __version__

# Existing TransferStep order: packing, exocytosis, efflux, reuptake, C/E loss.
T = Matrix([[-1,0,-1,1,-1,0],[1,-1,0,0,0,0],[0,1,1,-1,0,-1]])
MOVES = ('p','r','f','u','lC','lE')
DELTA = {m: tuple(T[:,i]) for i,m in enumerate(MOVES)}
DELTA['idle'] = (0,0,0)
INITIAL = (1,1,0)


def enabled(stock, move, mask, remaining=None):
    return (move == 'idle' or move in mask) and (move != 'r' or remaining != 0) and all(
        a >= max(0,-b) for a,b in zip(stock, DELTA[move]))


def step(stock, move):
    return tuple(a+b for a,b in zip(stock,DELTA[move]))


def enumerate_histories(mask, slots=3, budget=None):
    # Clock slots permit at most one unit event; idle is explicit.
    def go(stock, path, counts, remaining):
        if len(path)==2*slots:
            yield stock, path, tuple(counts), remaining
            return
        for m in ('idle',)+MOVES:
            if not enabled(stock,m,mask,remaining):
                continue
            nxt=step(stock,m)
            c=counts.copy()
            if m!='idle': c[(len(path)//slots)*6+MOVES.index(m)]+=1
            assert min(nxt)>=0
            assert sum(nxt)+c[4]+c[5]+c[10]+c[11]==sum(INITIAL)
            yield from go(nxt,path+(m,),c, None if remaining is None else remaining-int(m=='r'))
    return list(go(INITIAL,(),[0]*12,budget))


def analyse(mask):
    histories=enumerate_histories(mask)
    fibres=defaultdict(set)
    for stock,path,c,remaining in histories:
        fibres[stock].add(c)
    # Span all same-stock admissible differences, not ambient nullspace by fiat.
    differences=[]
    for codes in fibres.values():
        codes=sorted(codes); base=Matrix(codes[0])
        differences.extend(Matrix(c)-base for c in codes[1:])
    N=Matrix.hstack(*differences) if differences else zeros(12,0)
    basis=N.columnspace(); N=Matrix.hstack(*basis) if basis else zeros(12,0)
    O=T.row_join(T)
    assert O*N==zeros(3,N.cols)
    e=eye(12); r=e[1,:]+e[7,:]; f=e[2,:]+e[8,:]; u=e[3,:]+e[9,:]
    goals={'release':r,'net_panel':Matrix.vstack(r,f-u),'gross_panel':Matrix.vstack(r,f,u),
           'early_release':e[1,:],'early_late_release':Matrix.vstack(e[1,:],e[7,:])}
    menu=list(range(12))
    results={}
    for name,F in goals.items():
        rank=(F*N).rank()
        # Linear decoder with coarse stock + selected raw count rows.
        found=[]
        for n in range(rank,13):
            for subset in combinations(menu,n):
                Q=N[list(subset),:] if subset else zeros(0,N.cols)
                if Q.col_join(F*N).rank()==Q.rank(): found.append(subset)
            if found: break
        assert found
        # Independently verify direct fibre constancy for selected panel.
        lookup={}
        for stock,_,c,_ in histories:
            key=(stock,tuple(c[i] for i in found[0])); answer=tuple(F*Matrix(c))
            assert key not in lookup or lookup[key]==answer
            lookup[key]=answer
        results[name]=(rank,n,len(found),found[0])
    return len(histories), len(fibres), N.cols,results


def check():
    masks={'all':MOVES,'no_reuptake':tuple(m for m in MOVES if m!='u'),
           'no_efflux_or_loss':('p','r','u'),'one_way':('p','r')}
    for name,mask in masks.items():
        print(name,analyse(mask))
    # Same initial and present stocks, same intervention relation, different
    # remaining release budget. A real enabled cycle consumes one entitlement.
    H=enumerate_histories(MOVES,budget=1)
    by_path={h[1]:h for h in H}
    left=by_path[('idle',)*6]; right=by_path[('p','r','u','idle','idle','idle')]
    assert left[0]==right[0]==INITIAL and left[3]==1 and right[3]==0
    cone=lambda h: tuple(m for m in MOVES if enabled(h[0],m,MOVES,h[3]))
    assert set(cone(left))-set(cone(right))=={'r'} and set(cone(right))<set(cone(left))
    # Stock + paid remaining budget determines the one-step accessible cone
    # and next (stock,budget) for each move under the fixed relation/mask.
    lookup={}
    for h in H:
        stock,_,_,remaining=h; key=(stock,remaining)
        target=tuple((m,step(stock,m),remaining-int(m=='r')) for m in cone(h))
        assert key not in lookup or lookup[key]==target
        lookup[key]=target
    # Budget alone without stock does not identify future cone.
    assert any(a[3]==b[3] and cone(a)!=cone(b) for a in H for b in H[:5])
    print('budgeted histories',len(H),'repair states',len(lookup),'left/right cones',cone(left),cone(right))
    print('SymPy',__version__,'PASS')


if __name__=='__main__':
    check()
