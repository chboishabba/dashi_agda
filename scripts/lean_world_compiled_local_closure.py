#!/usr/bin/env python3
"""Build and reuse source-hash-keyed compiled local Lean import closure.

Requires a pinned worker-verified source list and a compatible Lean binary.
Never treats successful olean compilation as a kernel-term export or proof.
"""
from __future__ import annotations
import hashlib,json,os,re,resource,signal,shutil,subprocess
from pathlib import Path

MODULE=re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")
IMPORT=re.compile(r"^\s*(?:(?:public|protected)\s+)?import\s+(.+?)\s*(?:--.*)?$",re.M)
class ClosureError(ValueError): pass

def source_imports(raw:bytes)->tuple[str,...]:
    try: text=raw.decode("utf-8")
    except UnicodeDecodeError as exc:raise ClosureError("non UTF-8 source") from exc
    result=[]
    for match in IMPORT.finditer(text):
        for name in match.group(1).split():
            if not MODULE.fullmatch(name):raise ClosureError("unsupported import syntax")
            result.append(name)
    return tuple(dict.fromkeys(result))

def compile_order(root:Path,sources:list[dict],target:str)->list[str]:
    paths={x["path"] for x in sources}
    if target not in paths:raise ClosureError("target missing from verified source closure")
    graph={}
    for path in paths:
        if not path.endswith(".lean") or ".." in Path(path).parts or Path(path).is_absolute():
            raise ClosureError("unsafe source path")
        refs=[]
        for name in source_imports((root/path).read_bytes()):
            sibling=name.replace(".","/")+".lean"
            if sibling in paths:refs.append(sibling)
        graph[path]=sorted(set(refs))
    seen=set();active=set();order=[]
    def walk(path):
        if path in active:raise ClosureError("cyclic local Lean imports")
        if path in seen:return
        active.add(path)
        for dep in graph[path]:walk(dep)
        active.remove(path);seen.add(path)
        if path!=target:order.append(path)
    walk(target)
    return order

def closure_key(*,sources:list[dict],repo:str,revision:str,lean_version:str,
                target:str,external_digest:str)->str:
    identity={"schema":"dashi-lean-local-olean-cache-v1","repository":repo,
      "revision":revision,"toolchain":lean_version,"target":target,
      "external_digest":external_digest,
      "sources":sorted((x["path"],x["sha256"]) for x in sources)}
    return hashlib.sha256(json.dumps(identity,sort_keys=True).encode()).hexdigest()

def compile_deps(root:Path,sources:list[dict],target:str,*,lean:str,
                 lean_version:str,repo:str,revision:str,external_digest:str,
                 external_path:str="",cache_dir:Path|None=None,timeout:int=180,
                 memory_mib:int=4096,runner=None)->dict:
    if timeout<1 or memory_mib<128:raise ClosureError("invalid resource limits")
    order=compile_order(root,sources,target)
    key=closure_key(sources=sources,repo=repo,revision=revision,
       lean_version=lean_version,target=target,external_digest=external_digest)
    output=root/".lean-local-compiled"
    output.mkdir(exist_ok=True)
    cache=(cache_dir/key) if cache_dir else None
    if cache and (cache/"receipt.json").is_file():
        manifest=json.loads((cache/"receipt.json").read_text(encoding="utf-8"))
        if manifest.get("cache_key")==key and set(manifest.get("compiled",{}))==set(order):
            valid=all((cache/Path(p).with_suffix(".olean")).is_file() and
                hashlib.sha256((cache/Path(p).with_suffix(".olean")).read_bytes()).hexdigest()==h
                for p,h in manifest["compiled"].items())
            if valid:
                for path in order:
                    name=Path(path).with_suffix(".olean")
                    dest=output/name;dest.parent.mkdir(parents=True,exist_ok=True)
                    shutil.copyfile(cache/name,dest)
                return {"cache_key":key,"compiled_modules":len(order),
                    "cache_reused":True,"olean_directory":str(output),
                    "compiler_checked":False,"cache_bound_to_source":True}
    env={k:os.environ[k] for k in ("PATH","LANG","LC_ALL","LC_CTYPE","TZ") if k in os.environ}
    env["LEAN_PATH"]=str(output)+(os.pathsep+external_path if external_path else "")
    env["HOME"]=str(root/".local-compile-home")
    Path(env["HOME"]).mkdir(exist_ok=True)
    def limits():
        resource.setrlimit(resource.RLIMIT_AS,(memory_mib*1048576,memory_mib*1048576))
    compiled={}
    for path in order:
        dest=output/Path(path).with_suffix(".olean")
        dest.parent.mkdir(parents=True,exist_ok=True)
        argv=[lean,f"--root={root}","-o",str(dest),str(root/path)]
        if runner:
            code=runner(argv,root,env,timeout,memory_mib)
        else:
            proc=subprocess.Popen(argv,cwd=root,env=env,stdin=subprocess.DEVNULL,
                stdout=subprocess.PIPE,stderr=subprocess.PIPE,
                start_new_session=True,preexec_fn=limits)
            try: stdout,stderr=proc.communicate(timeout=timeout)
            except subprocess.TimeoutExpired as exc:
                os.killpg(proc.pid,signal.SIGKILL);proc.communicate()
                raise ClosureError("local compilation timeout") from exc
            code=proc.returncode
        if code!=0 or not dest.is_file():
            raise ClosureError("local dependency compile failed: "+path)
        compiled[path]=hashlib.sha256(dest.read_bytes()).hexdigest()
    if cache:
        cache.mkdir(parents=True,exist_ok=True)
        for path in order:
            name=Path(path).with_suffix(".olean")
            dest=cache/name;dest.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(output/name,dest)
        (cache/"receipt.json").write_text(json.dumps({
            "cache_key":key,"compiled":compiled},sort_keys=True),encoding="utf-8")
    return {"cache_key":key,"compiled_modules":len(order),
        "cache_reused":False,"olean_directory":str(output),
        "compiler_checked":bool(order),"cache_bound_to_source":True}
