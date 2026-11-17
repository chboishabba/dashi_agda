#!/usr/bin/env python3
"""DASHI V2 Ω: pre-registered all-port factorial load/recovery measurement protocol.

No original-V2 measurements are embedded. Input is paired, arm-labelled, physically
calibrated cycle-mean port powers and endpoint energies. A failed protocol is NOT
interpreted as evidence for unusual power generation.
"""
from __future__ import annotations
import argparse
import csv
import json
from dataclasses import dataclass, asdict
from decimal import Decimal
from fractions import Fraction as F
from pathlib import Path
from typing import Iterable

ARM_IDS = ('00','01','10','11')
COLUMNS = ('block','sequence','arm','duration_s','motor_w','aux_w','load_w','other_w',
           'motor_loss_w','generator_loss_w','shaft_w', 'stored_before_j','stored_after_j',
           'motor_abs_error_w','aux_abs_error_w','load_abs_error_w','other_abs_error_w',
           'motor_loss_abs_error_w','generator_loss_abs_error_w','shaft_abs_error_w',
           'storage_abs_error_j')
SIGNED_PORTS = ('motor_w','aux_w','load_w','other_w','motor_loss_w','generator_loss_w','shaft_w')
ERR_PORTS = ('motor_abs_error_w','aux_abs_error_w','load_abs_error_w',
             'other_abs_error_w','motor_loss_abs_error_w','generator_loss_abs_error_w',
             'shaft_abs_error_w','storage_abs_error_j')
EXPERIMENTAL_COLUMNS=('block','sequence','arm')

def exact(x:object)->F:
    if isinstance(x,F):return x
    return F(str(x).strip())

@dataclass(frozen=True)
class Run:
    block: int
    sequence: int
    arm: str
    duration_s:F
    motor_w:F
    aux_w:F
    load_w:F
    other_w:F
    motor_loss_w:F
    generator_loss_w:F
    shaft_w:F
    stored_before_j:F
    stored_after_j:F
    motor_abs_error_w:F
    aux_abs_error_w:F
    load_abs_error_w:F
    other_abs_error_w:F
    motor_loss_abs_error_w:F
    generator_loss_abs_error_w:F
    shaft_abs_error_w:F
    storage_abs_error_j:F

    @classmethod
    def from_row(cls, row:dict)->'Run':
        if set(row)!=set(COLUMNS):
            raise ValueError(f'CSV header mismatch: missing {sorted(set(COLUMNS)-set(row))}; unexpected {sorted(set(row)-set(COLUMNS))}')
        if any(row[k] is None or str(row[k]).strip()=='' for k in COLUMNS):
            raise ValueError('Missing measurement; never substitute an assumed zero')
        arm=row['arm'].strip()
        if arm not in ARM_IDS:raise ValueError('Unknown load/recovery arm')
        if not row['block'].strip().isdigit() or not row['sequence'].strip().isdigit():
            raise ValueError('Block and sequence must be nonnegative integers')
        values={k:exact(row[k]) for k in COLUMNS if k not in EXPERIMENTAL_COLUMNS}
        v=cls(int(row['block']),int(row['sequence']),arm,**values)
        v.validate()
        return v

    def validate(self)->None:
        if self.duration_s<=0: raise ValueError('Nonpositive observation duration')
        if any(getattr(self,k)<0 for k in SIGNED_PORTS):
            raise ValueError('Negative port: change meter orientation convention explicitly')
        if any(getattr(self,k)<0 for k in ERR_PORTS):
            raise ValueError('Negative uncertainty')
        if self.stored_before_j<0 or self.stored_after_j<0:
            raise ValueError('Physical stored-energy inventory cannot be negative')

    @property
    def storage_rate_w(self)->F:
        return (self.stored_after_j-self.stored_before_j)/self.duration_s

    @property
    def storage_error_w(self)->F:
        return self.storage_abs_error_j/self.duration_s

    @property
    def whole_residual_w(self)->F:
        return (self.motor_w+self.aux_w-self.load_w-self.other_w
                -self.motor_loss_w-self.generator_loss_w-self.storage_rate_w)

    @property
    def whole_error_w(self)->F:
        return sum((getattr(self,k) for k in ('motor_abs_error_w','aux_abs_error_w',
            'load_abs_error_w','other_abs_error_w','motor_loss_abs_error_w',
            'generator_loss_abs_error_w')),F(0))+self.storage_error_w

    @property
    def motor_loss_residual_w(self)->F:
        return self.motor_w-self.shaft_w-self.motor_loss_w

    @property
    def motor_loss_error_w(self)->F:
        return self.motor_abs_error_w+self.shaft_abs_error_w+self.motor_loss_abs_error_w

    @property
    def generator_residual_w(self)->F:
        return (self.shaft_w+self.aux_w-self.load_w-self.other_w-
                self.generator_loss_w-self.storage_rate_w)

    @property
    def generator_error_w(self)->F:
        return (self.shaft_abs_error_w+self.aux_abs_error_w+self.load_abs_error_w+
                self.other_abs_error_w+self.generator_loss_abs_error_w+self.storage_error_w)


def make_schedule(blocks:int=4)->list[dict]:
    """Counterbalanced eight-run palindromes; each arm's mean time is 3.5.

    Rotate arm permutations by block; do not randomize after observing results.
    This cancels a linear common clock-time drift in each block's interaction.
    It does NOT remove nonlinear drift, treatment carryover or cross-meter bias.
    """
    if blocks<=0:raise ValueError('At least one block required')
    out=[]
    for block in range(blocks):
        cycle=ARM_IDS[block%4:]+ARM_IDS[:block%4]
        for seq,arm in enumerate(cycle+tuple(reversed(cycle))):
            out.append({'block':block,'sequence':seq,'arm':arm})
    return out

def measured_blocks(runs:Iterable[Run])->dict[int,dict[str,tuple[Run,Run]]]:
    grouped:dict[int,dict[str,list[Run]]]={}
    for r in runs:
        grouped.setdefault(r.block,{}).setdefault(r.arm,[]).append(r)
    if not grouped:raise ValueError('No measurements')
    for block, arms in grouped.items():
        if set(arms)!=set(ARM_IDS):raise ValueError(f'Block {block} lacks a factorial arm')
        if any(len(v)!=2 for v in arms.values()):raise ValueError('Each arm must repeat twice per block')
        clock={r.sequence for pairs in arms.values() for r in pairs}
        if clock!=set(range(8)):raise ValueError('Block must use eight unique sequence positions')
        for arm, pair in arms.items():
            if sum((r.sequence for r in pair))!=7:
                raise ValueError(f'Arm {arm} is not clock-symmetric; drift confounded')
    return {b:{a:tuple(v) for a,v in arms.items()} for b,arms in grouped.items()}

def arm_mean(arms:dict[str,tuple[Run,Run]],arm:str,key:str)->F:
    x,y=arms[arm]
    return (getattr(x,key)+getattr(y,key))/2

def arm_error(arms:dict[str,tuple[Run,Run]],arm:str,key:str)->F:
    x,y=arms[arm]
    return (getattr(x,key)+getattr(y,key))/2

def contrast(arms:dict[str,tuple[Run,Run]],key:str)->F:
    return (arm_mean(arms,'11',key)-arm_mean(arms,'10',key)
            -arm_mean(arms,'01',key)+arm_mean(arms,'00',key))

def error_bound(arms:dict[str,tuple[Run,Run]],key:str)->F:
    return sum((arm_error(arms,a,key) for a in ARM_IDS),F(0))

# Directly stated measurement error bounds must apply to EACH arm, not just differences.
PROBE_FIELDS={
    'motor_w':'motor_abs_error_w', 'aux_w':'aux_abs_error_w',
    'load_w':'load_abs_error_w','other_w':'other_abs_error_w',
    'shaft_w':'shaft_abs_error_w','motor_loss_w':'motor_loss_abs_error_w',
    'generator_loss_w':'generator_loss_abs_error_w',
    'storage_rate_w':'storage_error_w',
}

def assess(runs:Iterable[Run], require_storage_match=True)->dict:
    blocks=measured_blocks(runs)
    output=[]
    for b,arms in sorted(blocks.items()):
        rows=[r for a in ARM_IDS for r in arms[a]]
        # Endpoint energy match tested run-by-run, not only average cancellation.
        if require_storage_match and any(abs(r.stored_after_j-r.stored_before_j)>r.storage_abs_error_j for r in rows):
            raise ValueError(f'Block {b} has unmatched energy-storage endpoints')
        for r in rows:
            if abs(r.whole_residual_w)>r.whole_error_w:
                raise ValueError(f'Block {b} fails complete signed energy closure')
            if abs(r.motor_loss_residual_w)>r.motor_loss_error_w:
                raise ValueError(f'Block {b} fails independent motor/shaft balance')
            if abs(r.generator_residual_w)>r.generator_error_w:
                raise ValueError(f'Block {b} fails independent shaft/generator balance')
        terms={k:contrast(arms,k) for k in PROBE_FIELDS}
        error={k:error_bound(arms,errfield) for k,errfield in PROBE_FIELDS.items()}
        # Whole-system factor interaction must close within propagated meter uncertainty.
        c=terms['motor_w']+terms['aux_w']-terms['load_w']-terms['other_w']-terms['motor_loss_w']-terms['generator_loss_w']-terms['storage_rate_w']
        bound=sum((error[k] for k in ('motor_w','aux_w','load_w','other_w','motor_loss_w','generator_loss_w','storage_rate_w')),F(0))
        if abs(c)>bound:raise ValueError(f'Block {b} interaction fails whole-system energy closure')
        load=terms['load_w'];loaderr=error['load_w']
        output.append({'block':b,'interaction_load_w':float(load),
                       'interaction_load_interval_w':[float(load-loaderr),float(load+loaderr)],
                       'interaction_shaft_w':float(terms['shaft_w']),
                       'interaction_generator_loss_w':float(terms['generator_loss_w']),
                       'interaction_motor_loss_w':float(terms['motor_loss_w']),
                       'interaction_storage_rate_w':float(terms['storage_rate_w']),
                       'whole_interaction_residual_w':float(c),
                       'whole_interaction_bound_w':float(bound),
                       'sign_identified':load-loaderr>0 or load+loaderr<0,
                       'attribution':'Only if all measured powers and actual source paths are covered'})
    return {'schema':'DASHI.V2.Omega.intervention-protocol.v1',
            'evidence_status':'USER-SUPPLIED MEASURED DATA REQUIRED; passing a synthetic fixture does not establish V2',
            'block_count':len(output),'blocks':output,
            'limitation':'Deterministic per-row error intervals; no unmeasured cable, material, common-mode drift, carryover, thermal trend or sensor calibration is assumed bounded',
            'original_V2_identified':False}

def load_csv(path:Path)->list[Run]:
    with path.open(newline='') as f:
        reader=csv.DictReader(f)
        return [Run.from_row(row) for row in reader]

def write_template(path:Path,blocks:int)->None:
    with path.open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=COLUMNS)
        writer.writeheader()
        for x in make_schedule(blocks):
            writer.writerow(x)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--template',type=Path,help='Write an UNFILLED real-measurement template')
    ap.add_argument('--blocks',type=int,default=4)
    ap.add_argument('--measurements',type=Path,help='Read calibrated all-port observations')
    ap.add_argument('--allow-storage-change',action='store_true',help='Still requires measured endpoint energies')
    args=ap.parse_args()
    if args.template:
        write_template(args.template,args.blocks)
        print(json.dumps({'template':str(args.template),'rows':args.blocks*8,'filled':False},indent=2));return
    if not args.measurements:ap.error('Specify --measurements or --template')
    print(json.dumps(assess(load_csv(args.measurements),not args.allow_storage_change),indent=2))
if __name__=='__main__':main()
