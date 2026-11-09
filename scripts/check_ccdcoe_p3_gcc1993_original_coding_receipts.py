#!/usr/bin/env python3
"""Fail-closed dual-coder intake for original GCC source passages.

Inputs are user-provided local byte files and independent review receipts;
this validator does not validate the truth or independence of reviewer claims.
"""
import argparse
import hashlib
import json
import tempfile
from collections import Counter
from pathlib import Path

VALID = {
    'uncertainty': {'acknowledged_with_bounds', 'emphasised_without_bounds', 'minimised', 'not_addressed', 'undeterminable'},
    'scientific_voice': {'named_supported', 'named_disputed', 'unnamed_consensus', 'unnamed_dissensus', 'not_addressed', 'undeterminable'},
    'risk_time_horizon': {'short_term', 'long_term', 'both', 'unstated', 'undeterminable'},
    'responsibility': {'institutional', 'individual', 'collective', 'undistributed', 'not_addressed', 'undeterminable'},
    'agency': {'enables_revision', 'closes_revision', 'neutral_procedural', 'not_addressed', 'undeterminable'},
    'selective_reuse': {'verbatim_contextual', 'verbatim_decontextualised', 'paraphrase_contextual', 'paraphrase_decontextualised', 'referenced_without_passage', 'not_reused', 'undeterminable'},
}

def demand(ok, reason):
    if not ok: raise ValueError(reason)

def kappa(pairs):
    if not pairs: return {'n': 0, 'agreement': None, 'kappa': None}
    n=len(pairs); counts_a=Counter(a for a,b in pairs); counts_b=Counter(b for a,b in pairs)
    observed=sum(a==b for a,b in pairs)/n
    expected=sum(counts_a[c]*counts_b[c] for c in (set(counts_a)|set(counts_b)))/(n*n)
    return {'n': n, 'agreement': observed, 'kappa': None if expected == 1 else (observed-expected)/(1-expected)}

def validate(manifest, source_root):
    demand(manifest.get('schema')=='dashi.ccdcoe.p3.dual_coder_receipts.v1', 'schema')
    root=Path(source_root).resolve(); items=manifest.get('passages',[])
    demand(len(items)==len({p['id'] for p in items}), 'duplicate passage')
    grades={}
    pairings={name: [] for name in VALID}
    for p in items:
        demand(p['source_id'] in ('rensberger_original','hansen_original_correction','gcc_june_response','gcc_september_bulletin','gcc_march_baseline'), 'source cohort')
        local=p['relative_path']; demand(isinstance(local,str) and local and not Path(local).is_absolute(), 'relative path')
        file=(root/local).resolve(); demand(file.is_relative_to(root) and file.is_file(), 'source file traversal/missing')
        raw=file.read_bytes(); digest=hashlib.sha256(raw).hexdigest()
        demand(digest==p['sha256'], 'original bytes digest')
        a,b=p['start_byte'],p['end_byte']; demand(type(a) is int and type(b) is int and 0<=a<b<=len(raw),'byte interval')
        demand(hashlib.sha256(raw[a:b]).hexdigest()==p['passage_sha256'],'passage digest')
        demand(bool(p['original_author'].strip()) and bool(p['edition'].strip()), 'original ownership')
        demand(len(p['reviews'])==2,'independent review count')
        r1,r2=p['reviews']; demand(r1['reviewer_id']!=r2['reviewer_id'], 'reviewer independence ID')
        for r in (r1,r2):
            demand(bool(r['reviewer_id'].strip()) and bool(r['receipt'].strip()),'review receipt')
            demand(set(r['codes'])==set(VALID),'six coding dimensions')
            for name,value in r['codes'].items(): demand(value in VALID[name], 'invalid code: '+name)
        for name in VALID: pairings[name].append((r1['codes'][name],r2['codes'][name]))
        demand(not p.get('claims_audience_effect',False) and not p.get('claims_hostile_intent',False),'unearned promotion')
        grades[p['id']]={'original_bytes_sha256':digest, 'reviewers': [r1['reviewer_id'],r2['reviewer_id']]}
    return {'passages':len(items),'validated_hashes':len(grades),'reliability':{name:kappa(pairs) for name,pairs in pairings.items()},'human_independence_authenticated':False,'audience_effect_identified':False,'hostile_intent_identified':False}

def self_test():
    with tempfile.TemporaryDirectory() as tmp:
        root=Path(tmp); raw=b'Original SYNTHETIC passage. Not original historical footage.'
        (root/'text.bin').write_bytes(raw)
        codes_a={key:sorted(values)[0] for key,values in VALID.items()}
        codes_b=codes_a.copy()
        p={'id':'test1','source_id':'gcc_march_baseline','relative_path':'text.bin','sha256':hashlib.sha256(raw).hexdigest(), 'start_byte':0,'end_byte':len(raw),'passage_sha256':hashlib.sha256(raw).hexdigest(), 'original_author':'SYNTHETIC GCC test only','edition':'synthetic', 'reviews':[{'reviewer_id':'A','receipt':'synthetic A', 'codes':codes_a},{'reviewer_id':'B','receipt':'synthetic B', 'codes':codes_b}]}
        item={'schema':'dashi.ccdcoe.p3.dual_coder_receipts.v1','passages':[p]}
        positive=validate(item,root); demand(all(x['kappa'] is None for x in positive['reliability'].values()),'constant kappa undefined')
        import copy
        tests=[('bytes_hash',lambda x:x['passages'][0].update(sha256='0'*64)),('passage_hash',lambda x:x['passages'][0].update(passage_sha256='0'*64)),('path_traversal',lambda x:x['passages'][0].update(relative_path='../outside')),('same_reviewer',lambda x:x['passages'][0]['reviews'][1].update(reviewer_id='A')),('effect',lambda x:x['passages'][0].update(claims_audience_effect=True)),('fake_intent',lambda x:x['passages'][0].update(claims_hostile_intent=True)),('no_second_coder',lambda x:x['passages'][0].update(reviews=x['passages'][0]['reviews'][:1])),('bad_code',lambda x:x['passages'][0]['reviews'][0]['codes'].update(uncertainty='promoted')),('fake_source',lambda x:x['passages'][0].update(source_id='invented')),('invalid_span',lambda x:x['passages'][0].update(end_byte=len(raw)+10))]
        for name,change in tests:
            changed=copy.deepcopy(item); change(changed)
            try:validate(changed,root)
            except (ValueError,KeyError,TypeError):continue
            raise AssertionError('negative test accepted: '+name)
        demand(kappa([('a','a'),('b','b')])['kappa']==1,'agreement test')
        demand(kappa([('a','b'),('b','a')])['kappa']==-1,'disagreement test')
        return {'synthetic_passage_positive':True,'negative_controls':len(tests),'kappa_cases':3,'real_historical_passages_admitted':0}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--self-test',action='store_true');ap.add_argument('--receipts',type=Path);ap.add_argument('--source-root',type=Path);args=ap.parse_args()
    if args.self_test:print(json.dumps(self_test(),indent=2))
    else:
        demand(args.receipts is not None and args.source_root is not None,'--receipts and --source-root required')
        print(json.dumps(validate(json.loads(args.receipts.read_text()),args.source_root),indent=2))
