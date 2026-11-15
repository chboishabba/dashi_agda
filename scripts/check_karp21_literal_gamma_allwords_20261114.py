#!/usr/bin/env python3
"""Exhaustive replay of ORIGINAL F1 3-state/one-work-tape gamma table.
Original readGammaBinary semantics: 0^k 1 payload[k] ++ suffix.
All 32767 bitwords of length 0..14, including malformed/truncated.
Not an Agda receipt or full N21/F2/F3/F4/NP proof.
"""
from itertools import product
import json
B0,B1,BLANK,MARK='0','1','_','M'
def tape(bits):return ([],bits[0] if bits else BLANK,list(bits[1:]))
def walk(t,d):
    ls,c,rs=t
    if d==0:return t
    if d==1:return ([c]+ls,rs[0],rs[1:]) if rs else ([c]+ls,BLANK,[])
    return (ls[1:],ls[0],[c]+rs) if ls else ([],BLANK,[c]+rs)
def physical(bits):
    I=tape(bits); W=tape([]); state=0; halted=False; count=0
    for _ in range(2*len(bits)+3):
        if halted:break
        inp=I[1]; work=W[1]
        if state in (0,1):
            if inp==B0:act=(1,B0,1,MARK,1,False)
            elif inp==B1 and state==0:act=(0,B1,1,BLANK,0,True)
            elif inp==B1:act=(2,B1,1,BLANK,-1,False)
            else:act=(2,BLANK,0,MARK,0,True)
        elif inp in (B0,B1) and work==MARK:
            act=(2,inp,1,inp,-1,False)
        elif inp in (B0,B1,BLANK) and work==BLANK:
            act=(2,inp,0,BLANK,0,True)
        else:act=(2,inp,0,MARK,0,True)
        state,iw,im,ww,wm,halted=act
        I=walk((I[0],iw,I[2]),im)
        W=walk((W[0],ww,W[2]),wm)
        count+=1
    assert halted,(bits,state,count)
    return W[1]==BLANK,count,I,W
def source(bits):
    k=0
    while k<len(bits) and bits[k]==B0:k+=1
    if k==len(bits) or len(bits)<2*k+1:return None
    return bits[k+1:2*k+1],bits[2*k+1:]
def check():
    tested=accepted=rejected=largest=0
    samples=[]
    for n in range(15):
        for w in product((B0,B1),repeat=n):
            bits=list(w);obs=source(bits)
            good,c,I,W=physical(bits)
            assert good==(obs is not None),(bits,good,obs,W)
            assert c<=2*(n+1),(bits,c,n)
            assert len(I[0])+len(I[2])+len(W[0])+len(W[2])+2<=2*(n+1)+2*c
            if good:
                payload,suffix=obs
                assert c==(1 if not payload else 2*len(payload)+2)
                actual_payload=list(reversed([v for v in W[2] if v in (B0,B1)]))
                assert actual_payload==payload,(bits,payload,actual_payload,W)
                remaining=([I[1]]+I[2]) if I[1]!=BLANK else []
                assert remaining==suffix,(bits,remaining,suffix)
                accepted+=1
            else:rejected+=1
            largest=max(largest,c);tested+=1
            if bits in ([],[B0],[B1],[B0,B1],[B0,B1,B0],
                        [B0,B1,B0,B1],[B0,B0,B1,B1]):
                samples.append({'input':''.join(bits),'accepted':good,
                                'steps':c,'work_head':W[1]})
    return {'schema':'karp21-f1-literal-gamma-allwords-exhaustion-v1',
      'result':'PASS','all_binary_words_length_le_14':tested,
      'accepted':accepted,'rejected':rejected,'max_literal_steps':largest,
      'physical_clock':'<=2*(input_bits+1), one gamma invocation only',
      'source_agreement':'exact first gamma payload, untouched suffix, terminal accept/reject',
      'samples':samples,'Agda_kernel_receipt':False,
      'original_F2_F3_F4':False,'original_N21_InNP':False}
if __name__=='__main__':print(json.dumps(check(),indent=2))
