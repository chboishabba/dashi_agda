#!/usr/bin/env python3
"""Deterministic finite streaming scheduler: synthetic, NEVER a GPU/WAN receipt."""
from __future__ import annotations
import argparse
import json
from dataclasses import dataclass
from pathlib import Path
import unittest

class AdmissionError(ValueError): pass

@dataclass(frozen=True)
class Task:
    source_id: str
    ready: int
    transfer: int
    compute: int
    model: str = "m1"
    history: int = 0
    refinement: int = 1

def schedule(tasks, *, capacity=2, model="m1", history=0, refinement=1):
    if capacity < 1: raise AdmissionError("zero queue capacity")
    result = []
    free_transfer = free_compute = 0
    last_arrival = -1
    for i,t in enumerate(tasks):
        if (t.model,t.history,t.refinement) != (model,history,refinement):
            raise AdmissionError("stale version")
        if min(t.ready,t.transfer,t.compute) < 0 or t.ready < last_arrival:
            raise AdmissionError("invalid arrival or duration")
        start = max(t.ready,free_transfer)
        if i >= capacity:
            start = max(start,result[i-capacity]["compute_start"])
        transferred = start + t.transfer
        compute_start = max(transferred,free_compute)
        done = compute_start + t.compute
        result.append(dict(id=t.source_id,transfer_start=start,
                           transfer_end=transferred,compute_start=compute_start,
                           compute_end=done))
        free_transfer,free_compute,last_arrival = transferred,done,t.ready
    return result

def serial(tasks):
    now=0
    for t in tasks: now=max(now,t.ready)+t.transfer+t.compute
    return now

def receipt(tasks,steps):
    return dict(scope="synthetic_finite_schedule_only",items=len(steps),
      first_completion=steps[0]["compute_end"] if steps else None,
      makespan=steps[-1]["compute_end"] if steps else 0,
      serial_makespan=serial(tasks),
      gpu_native_executed=False,physical_network_measured=False,
      diffusion_model_trained=False,whole_model_equivalence_proved=False,
      release_admitted=False)

class Tests(unittest.TestCase):
    def task(self,i,**kw): return Task(str(i),**kw)
    def test_pipeline(self):
        t=[self.task(i,ready=0,transfer=8,compute=20) for i in range(3)]
        s=schedule(t)
        self.assertEqual([r["compute_end"] for r in s],[28,48,68])
        self.assertEqual(serial(t),84)
    def test_bandwidth_bottleneck(self):
        t=[self.task(i,ready=0,transfer=20,compute=8) for i in range(3)]
        self.assertEqual([r["compute_end"] for r in schedule(t)],[28,48,68])
    def test_causal_dependency(self):
        t=[self.task(0,ready=0,transfer=8,compute=20),
           self.task(1,ready=28,transfer=8,compute=20)]
        self.assertEqual(schedule(t)[-1]["compute_end"],56)
    def test_backpressure(self):
        t=[self.task(i,ready=0,transfer=1,compute=50) for i in range(5)]
        self.assertEqual([r["transfer_start"] for r in schedule(t,capacity=1)],
                         [0,1,51,101,151])
    def test_zero_queue_reject(self):
        with self.assertRaises(AdmissionError):schedule([],capacity=0)
    def test_stale_model_reject(self):
        with self.assertRaises(AdmissionError):
            schedule([self.task(0,ready=0,transfer=1,compute=1,model="m0")])
    def test_stale_history_reject(self):
        with self.assertRaises(AdmissionError):
            schedule([self.task(0,ready=0,transfer=1,compute=1,history=1)])
    def test_stale_refinement_reject(self):
        with self.assertRaises(AdmissionError):
            schedule([self.task(0,ready=0,transfer=1,compute=1,refinement=0)])
    def test_negative_duration_reject(self):
        with self.assertRaises(AdmissionError):
            schedule([self.task(0,ready=0,transfer=-1,compute=1)])
    def test_out_of_order_arrivals_reject(self):
        with self.assertRaises(AdmissionError):
            schedule([self.task(0,ready=10,transfer=1,compute=1),
                      self.task(1,ready=0,transfer=1,compute=1)])
    def test_empty_schedule(self):
        self.assertEqual(schedule([]),[])
    def test_receipt_fail_closed(self):
        t=[self.task(i,ready=0,transfer=8,compute=20) for i in range(3)]
        r=receipt(t,schedule(t))
        self.assertEqual(r["makespan"],68)
        self.assertFalse(r["release_admitted"])
        self.assertFalse(r["diffusion_model_trained"])

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--self-test",action="store_true")
    p.add_argument("--receipt",type=Path)
    args=p.parse_args()
    if args.self_test:
        return int(not unittest.TextTestRunner(verbosity=2).run(
          unittest.defaultTestLoader.loadTestsFromTestCase(Tests)).wasSuccessful())
    tasks=[Task(str(i),0,8,20) for i in range(3)]
    result=receipt(tasks,schedule(tasks))
    output=json.dumps(result,sort_keys=True,indent=2)+"\n"
    if args.receipt:
        args.receipt.parent.mkdir(parents=True,exist_ok=True)
        if args.receipt.exists():raise FileExistsError("refuse receipt overwrite")
        args.receipt.write_text(output)
    print(output,end="")
    return 0

if __name__=="__main__":raise SystemExit(main())
