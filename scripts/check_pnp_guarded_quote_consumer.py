"""Guarded candidate/serialization receiver, not a self-diagonal producer.
Compact template lookup preserves absolute placement. Reading an encoded
query and executing its actual finite candidate are separate operations.
"""
from check_pnp_cook_quadratic_seek import QuadraticCookSeek
from check_pnp_stack_fractran import compile_candidate_bits, source_next
from check_pnp_stack_priority_transport import AuditedRunner
from check_pnp_candidate_literal_endpoint import candidate_bits

class GuardedSeek:
    def __init__(self,source,allowance):
        if allowance<0:raise ValueError("allowance")
        self.source=source;self.left=allowance;self.cache={};self.requests=0
    def bit(self,k):
        # A cache hit still consumes an actual requested operation.
        if self.left==0:raise RuntimeError("query refusal")
        self.left-=1;self.requests+=1
        if k not in self.cache:
            self.cache[k]=self.source.bit(k)
        return self.cache[k]
    def materialize(self):
        n=3*self.source.length()
        if n>self.left:return None
        return tuple(self.bit(i) for i in range(n))

def guarded_candidate_query(states,symbols,count,program,seek,steps,query_cap,
                            start_from_bits,exponent_bit_cap=8192):
    """Actual finite source run on the supplied original start mapping.
    Exact guardedStandardStart parity must still be furnished natively.
    Logical requests and raw FRACTRAN edges are reported separately.
    """
    if min(steps,query_cap,exponent_bit_cap)<0:raise ValueError("cap")
    M,initial,accept=compile_candidate_bits(states,symbols,count,program)
    reader=GuardedSeek(seek,query_cap)
    word=reader.materialize()
    if word is None:return dict(status="UNKNOWN",queries=reader.requests)
    q,L,R=start_from_bits(initial,word,steps)
    if q!=initial:raise ValueError("initial control")
    L,R=tuple(L),tuple(R) or (M.blank,)
    # Packing cost is guarded by original input length before packing.
    if (len(L)+len(R))*M.base.bit_length()>exponent_bit_cap:
        return dict(status="UNKNOWN",queries=reader.requests)
    s=M.encode(q,L,R);A=AuditedRunner(M);raw=0
    for i in range(steps):
        if max(s[:5]).bit_length()>exponent_bit_cap:
            return dict(status="UNKNOWN",queries=reader.requests,raw=raw)
        q,L,R,halt=M.decode(s)
        want=source_next(M,(q,L,R))
        if halt or want is None:
            # A missing source step is not a valid StandardExactRun edge.
            return dict(status="EARLY_HALT",queries=reader.requests,raw=raw,steps=i)
        s,h,receipt=A.exact(s,True);raw+=receipt["raw"]
        assert not h and M.decode(s)==(*want,False)
    q,L,R,h=M.decode(s);decision=(q==accept)
    return dict(status="ENDPOINT",decision=decision,flipped=not decision,
                queries=reader.requests,distinct_queries=len(reader.cache),
                raw=raw,steps=steps)
    # No claim that SAT(input)==flipped, or that query/raw counts
    # bound the original physical tape clock.

def main():
    seek=QuadraticCookSeek(0,1,1,(((0,True),),),(((0,True),),),(0,),(1,0,1))
    rules=((0,0,1,0,0),(0,1,1,1,0))
    program=candidate_bits(2,3,2,0,1,rules)
    # Scoped toy input map. Not the original Agda guarded start.
    start=lambda q,word,t:(q,(),word)
    cap=3*seek.length()
    q=guarded_candidate_query(2,3,len(rules),program,seek,1,cap,start)
    assert q["status"]=="ENDPOINT" and q["decision"] and not q["flipped"]
    assert q["queries"]==cap and q["raw"]>1
    assert guarded_candidate_query(2,3,len(rules),program,seek,1,cap-1,start)["status"]=="UNKNOWN"
    # Same template at different time offsets is NOT the same placed
    # clause. The absolute coordinates survive the compact chart.
    Q=QuadraticCookSeek(2,1,1,(((1,True),),),(((0,True),),),(0,),(1,0,1))
    assert Q.trans_coord(1,0,0)!=Q.trans_coord(1,1,0)
    assert Q.transition_prefix(1)>0
    print(dict(guarded_endpoint=1,query_refusal=1,placed_time_control=1))
if __name__=="__main__":main()
