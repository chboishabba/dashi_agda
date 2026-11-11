#!/usr/bin/env python3
"""Dependency-free CPU-only miner/worker/shard gate. Synthetic; never deployment admission."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import unittest

class Reject(ValueError): pass

NODES = {'source':('coordinator','operator',0), 'ma':('miner','A',0),
         'mb':('miner','B',0), 'wa':('worker','A',2048), 'wb':('worker','B',2048)}
EDGES = {('source','ma'),('source','mb'),('ma','wa'),('mb','wb'),('mb','wa')}

def reachable(src, dst):
    if src not in NODES or dst not in NODES: return False
    seen, queue = {src}, [src]
    while queue:
        u = queue.pop()
        for a,b in EDGES:
            if a == u and b not in seen: seen.add(b); queue.append(b)
    return dst in seen

def shards(width, size):
    if width <= 0 or size <= 0: raise Reject('bad widths')
    return tuple(range(i,min(width,i+size)) for i in range(0,width,size))

def check_partition(parts,width):
    if [i for p in parts for i in p] != list(range(width)):
        raise Reject('gap/overlap/order in shard coverage')

def digest(s): return hashlib.sha256(s.encode()).hexdigest()

def check_placements(ps, expected, rev, hashes):
    if len(ps) != len(expected) or {p[0] for p in ps} != set(expected):
        raise Reject('missing/duplicate shard')
    used = {}
    for i, node, nbytes, version, sha in ps:
        if node not in NODES or NODES[node][0] != 'worker' or not reachable('source',node):
            raise Reject('ineligible worker')
        if version != rev or sha != hashes.get(i): raise Reject('stale revision/digest')
        if nbytes < 0: raise Reject('invalid reservation')
        used[node] = used.get(node,0)+nbytes
        if used[node] > NODES[node][2]: raise Reject('overcommitted memory')

def ffn(x, up, gate, down, bias):
    mid = [max(0,sum(a*b for a,b in zip(u,x)))*sum(a*b for a,b in zip(g,x))
           for u,g in zip(up,gate)]
    return tuple(b+sum(a*v for a,v in zip(row,mid)) for b,row in zip(bias,down))

def sharded_ffn(x,up,gate,down,bias,parts):
    check_partition(parts,len(up))
    result = list(bias)  # one bias, not one per shard
    for p in parts:
        partial = ffn(x,[up[i] for i in p],[gate[i] for i in p],
                      [[row[i] for i in p] for row in down],[0]*len(bias))
        result = [a+b for a,b in zip(result,partial)]
    return tuple(result)

def makespan(branch_times,reduce_time):
    if not branch_times or reduce_time < 0 or min(branch_times) < 0:
        raise Reject('invalid schedule')
    return max(branch_times)+reduce_time

def example():
    ids = {i:digest('synthetic-weight-'+str(i)) for i in range(6)}
    ps = [(i,'wa' if i<3 else 'wb',512,'synthetic-v1',ids[i]) for i in range(6)]
    check_partition(shards(3072,512),3072)
    check_placements(ps,range(6),'synthetic-v1',ids)
    return {'scope':'synthetic_cpu_only','num_shards':6,'shard_width':512,
            'intermediate_width':3072,'two_miner_routes':True,
            'abstract_parallel_cost':makespan((5,7),0), 'abstract_serial_cost':12,
            'tests_passed':None,'actual_model_checked':False,'network_measured':False,
            'agda_kernel_checked':False,'gpu_validated':False,'release_admitted':False}

class Tests(unittest.TestCase):
    def setUp(self):
        self.ids = {i:digest(str(i)) for i in range(6)}
        self.ps = [(i,'wa' if i<3 else 'wb',512,'v1',self.ids[i]) for i in range(6)]
    def accept(self,ps): check_placements(ps,range(6),'v1',self.ids)
    def test_reachability(self):
        self.assertTrue(reachable('ma','wa') and reachable('mb','wa'))
        self.assertFalse(reachable('wa','source'))
    def test_ownership_not_route(self): self.assertEqual(NODES['wa'][1],'A')
    def test_coverage(self):
        self.assertEqual(len(shards(3072,512)),6)
        check_partition(shards(3072,512),3072)
        self.assertEqual([len(s) for s in shards(1000,512)],[512,488])
    def test_gap_rejected(self):
        with self.assertRaises(Reject): check_partition((range(0,2),range(3,5)),5)
    def test_capacity_and_manifest(self): self.accept(self.ps)
    def test_missing_rejected(self):
        with self.assertRaises(Reject): self.accept(self.ps[:-1])
    def test_duplicate_rejected(self):
        with self.assertRaises(Reject): self.accept(self.ps+[self.ps[0]])
    def test_stale_revision_rejected(self):
        bad = [(0,'wa',512,'v0',self.ids[0])] + self.ps[1:]
        with self.assertRaises(Reject): self.accept(bad)
    def test_wrong_digest_rejected(self):
        bad = [(0,'wa',512,'v1','wrong')] + self.ps[1:]
        with self.assertRaises(Reject): self.accept(bad)
    def test_overcommit_rejected(self):
        with self.assertRaises(Reject): self.accept([(i,n,1024,v,h) for i,n,_,v,h in self.ps])
    def test_exact_integer_gated_ffn_shards(self):
        x = (2,-3)
        up = [(i%5-2,i%3) for i in range(10)]
        gate = [(1-i%3,i%4-1) for i in range(10)]
        down = [[i%4-1 for i in range(10)],[2-i%5 for i in range(10)]]
        bias = (7,-9)
        expected = ffn(x,up,gate,down,bias)
        for step in range(1,11):
            self.assertEqual(expected,sharded_ffn(x,up,gate,down,bias,shards(10,step)))
    def test_bias_duplicated_changes_result(self):
        self.assertNotEqual(ffn((1,),[(1,),(2,)],[(1,),(1,)],[[1,1]],(4,)),
            sum(ffn((1,),[(a,)],[(1,)],[[1]],(4,))[0] for a in (1,2)))
    def test_parallel_can_win_or_lose(self):
        self.assertEqual(makespan((5,7),0),7)
        self.assertGreater(makespan((5,100),1),12)
    def test_release_fail_closed(self): self.assertFalse(example()['release_admitted'])

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--self-test',action='store_true');ap.add_argument('--receipt',type=Path)
    args=ap.parse_args()
    if args.self_test:
        suite=unittest.defaultTestLoader.loadTestsFromTestCase(Tests)
        ok=unittest.TextTestRunner(verbosity=2).run(suite).wasSuccessful()
        return 0 if ok else 1
    result=example();payload=json.dumps(result,sort_keys=True,indent=2)+'\n'
    if args.receipt:
        args.receipt.parent.mkdir(parents=True,exist_ok=True)
        args.receipt.write_text(payload)
    print(payload,end='');return 0
if __name__=='__main__': raise SystemExit(main())
