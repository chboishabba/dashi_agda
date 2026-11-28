"""Run the complete written X369 regression cut on local clean worktrees.

One unittest module per child, hard timeout <=90s; immutable stdout,
stderr and receipt. Resume the SAME pinned heads/interpreters. This is
regression acceptance only: no actual source/physics/kernel promotion,
no GitHub CI, no GPU training registration changes.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
from collections import Counter
from time import monotonic

DASHI=(
'3b_E_coset_normal_form','3b_cyclotomic_weld','3b_cyclotomic_word_factor',
'3b_nonzero_trace_weld','3b_normalizer_coset_action','actual_3b_atlas_quotient_alignment',
'actual_source_geometry_contracts','actual_weyl_frame_bidi','concrete_leech_golay_glue',
'leech_discriminant_central_weld','mixed_central_monster_source','monster_dyadic_source_action',
'source_product_and_conway_weld','y443_actual_monster_quotient')
LEECH=(
'actual_leech_neural_action','campaign_progress','constructive_maxcut','e8_three_leech_glue_obstruction',
'exact_operator_transport','f3_two_seed_maxcut','fixed_phase_gauge_and_dynamic_null',
'frozen_history_intervention','full_fabric_pants_source_weld','full_native_e8_leech_chart',
'geometry_training','gwb_three_view_boundary','hyperfabric_scope','hypervoxel_stage13_pants_same_object',
'indexed_fibre_acceptance_stage','indexed_source_fibre_audit','leech24_pants_wave_weld',
'mod3_checkpointed','native_independent_semantic_appraisal','native_reasoning_evidence',
'native_stage13_evidence_manifest','original_capacity_fibre_reflections',
'original_marked_fabric_signed_graph','original_marked_seed_fabric',
'original_receipt_four_way_residual_bound','original_receipt_mark_collision_weld',
'original_receipt_multichart_weld','original_receipt_targeted_native',
'original_source_consumer_coarse_fine_maxcut','original_source_face_defect_attribution',
'original_source_minimal_residual_repair','original_source_signed_defect_transport',
'original_source_witness_first_probe','original_source_word_residual_weld',
'projected_router_score_weld','r1_native_source_only','r4_execution_device',
'r4_fair_c2c3_residual','r4b_source_runner','reachable_capacity_orbit_weld',
'reachable_capacity_residual_bounds','registered_campaign_batch','registered_crystallisation',
'registered_learning_campaign','semantic_cap_geometric_section','slr_signed_support_stage',
'sophontic_spiral_retained','source_six_face_receipt','stage13_pants_orbit_source_ports',
'targeted_receipt_capacity_maxcut','transported_seed_action','typed_mod3_prediction_consumer',
'whole_source_indexed_transport')


def require(ok,msg):
    if not ok:raise ValueError(msg)


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def put(p,v):
    with p.open('x') as f:json.dump(v,f,sort_keys=True,indent=2);f.write('\n')


def git(root,*args):
    return subprocess.check_output(['git','-C',str(root),*args],text=True,timeout=20).strip()


def source(root,python,head,modules):
    root=root.resolve();python=python.resolve()
    require(root.is_dir() and python.is_file(),'actual local source and interpreter')
    require(git(root,'rev-parse','HEAD')==head,'source HEAD differs from declared')
    require(not git(root,'status','--porcelain','--untracked-files=no'),'tracked source worktree dirty')
    files={}
    for m in modules:
        path='tests/test_x369_'+m+'.py'
        require((root/path).is_file(),'missing regression owner: '+path)
        git(root,'ls-files','--error-unmatch',path)
        files[m]=sha(root/path)
    return dict(root=str(root),head=head,python=str(python),python_sha256=sha(python),modules=files)


def receipt(root,key,module,contract):
    p=root/key/module/'receipt.json'
    if not p.exists():return None
    v=json.loads(p.read_text())
    require(v['source']==key and v['module']==module and
        v['head']==contract['head'] and v['test_sha256']==contract['modules'][module],
        'regression receipt source changed')
    require(v['stdout_sha256']==sha(p.parent/'stdout.log') and
            v['stderr_sha256']==sha(p.parent/'stderr.log'),'regression logs changed')
    return v


def execute(root,key,module,contract,timeout):
    d=root/key/module;d.mkdir(parents=True,exist_ok=False)
    name='tests.test_x369_'+module
    argv=[contract['python'],'-m','unittest','-v',name]
    env=dict(os.environ,OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1',PYTHONDONTWRITEBYTECODE='1')
    start=monotonic()
    try:
        p=subprocess.run(argv,cwd=contract['root'],env=env,capture_output=True,timeout=timeout)
        stdout,stderr,code=p.stdout,p.stderr,p.returncode
    except subprocess.TimeoutExpired as exc:
        stdout,stderr,code=exc.stdout or b'',exc.stderr or b'',None
    (d/'stdout.log').write_bytes(stdout);(d/'stderr.log').write_bytes(stderr)
    log=(stdout+b'\n'+stderr).decode('utf-8','replace')
    n=re.findall(r'^Ran (\d+) tests? in ',log,re.M)
    count=int(n[-1]) if n else 0
    # Distinguish executed tests and all-skipped modules. Never treat a
    # missing test summary or zero executed cases as a regression pass.
    m=re.findall(r'^OK(?: \(([^)]*)\))?\s*$',log,re.M)
    skipped=sum(int(x) for x in re.findall(r'skipped=(\d+)',m[-1])) if m else 0
    expected_failures=sum(int(x) for x in re.findall(r'expected failures=(\d+)',m[-1])) if m else 0
    status=('TIMEOUT' if code is None else 'FAIL' if code!=0 else
        'PASS_WITH_DECLARED_SKIPS' if m and count>skipped+expected_failures and (skipped or expected_failures) else
        'PASS' if m and count>0 and not (skipped or expected_failures) else 'HELD_NO_EXECUTED_PASS')
    v=dict(source=key,module=module,head=contract['head'],test_sha256=contract['modules'][module],
        command=argv,status=status,exit_code=code,reported_tests=count,skipped=skipped,
        expected_failures=expected_failures,seconds=monotonic()-start,
        stdout_sha256=sha(d/'stdout.log'),stderr_sha256=sha(d/'stderr.log'),
        actual_source_acceptance=False,kernel_acceptance=False)
    put(d/'receipt.json',v);return v


def main():
    p=argparse.ArgumentParser()
    for n in ('dashi','leech'):
        p.add_argument('--'+n,type=Path,required=True)
        p.add_argument('--'+n+'-head',required=True)
        p.add_argument('--'+n+'-python',type=Path,required=True)
    p.add_argument('--directory',type=Path,required=True);p.add_argument('--max-modules',type=int,default=len(DASHI)+len(LEECH))
    p.add_argument('--timeout',type=float,default=90);a=p.parse_args()
    require(0<a.timeout<=90 and a.max_modules>0,'bounded regression scope')
    r=a.directory.resolve();r.mkdir(parents=True,exist_ok=True)
    c=dict(schema='x369.local-regression-cut.v1',runner_sha256=sha(Path(__file__)),
        timeout=a.timeout,sources={
        'dashi':source(a.dashi,a.dashi_python,a.dashi_head,DASHI),
        'leech':source(a.leech,a.leech_python,a.leech_head,LEECH)})
    reg=r/'registration.json'
    if reg.exists():require(json.loads(reg.read_text())==c,'registered source/test scope changed; use new directory')
    else:put(reg,c)
    rows=[];done=0
    for key,contract in c['sources'].items():
        for module in contract['modules']:
            v=receipt(r,key,module,contract)
            if v is None and done<a.max_modules:
                v=execute(r,key,module,contract,a.timeout);done+=1
                print(key,module,v['status'],v['reported_tests'],flush=True)
            if v is not None:rows.append(v)
    for key,contract in c['sources'].items():
        require(git(contract['root'],'rev-parse','HEAD')==contract['head'] and
            not git(contract['root'],'status','--porcelain','--untracked-files=no'),'source mutated during run')
    required=len(DASHI)+len(LEECH)
    counts=dict(Counter(x['status'] for x in rows))
    complete=len(rows)==required
    out=dict(status='REGRESSION_CUT_COMPLETE' if complete else 'REGRESSION_CUT_IN_PROGRESS',
        required_modules=required,recorded_modules=len(rows),counts=counts,
        all_regression_modules_pass=complete and counts.get('PASS',0)==required,
        actual_source_acceptance=False,kernel_acceptance=False,
        receipts=[dict(source=x['source'],module=x['module'],status=x['status'],
            sha256=sha(r/x['source']/x['module']/'receipt.json')) for x in rows])
    n=len(list(r.glob('summary-*.json')))+1
    put(r/f'summary-{n:04d}.json',out)
    print(json.dumps(out,sort_keys=True))
    if not out['all_regression_modules_pass']:raise SystemExit(2)

if __name__=='__main__':main()
