"""Offline verification for the CAT review release. Run 'python review.py --help'."""
import argparse
import concurrent.futures
from fractions import Fraction as F
from numeric_policy import compare, regression
import hashlib
import json
from math import comb, cos, isclose, isfinite, pi, sqrt
import os
from pathlib import Path
import shutil
import platform
import subprocess
import sys
import tarfile
import uuid
import zipfile

BASE=Path(__file__).resolve().parent
WORK=BASE/"evidence/workspace"
COMMIT="65a1391a0106c9204fe45bc73a039f056558cb83"
PROOFS=("CompactMatrixRadiation","PreterminalMatching","LayerMatrixParent","CATRelationalCollapse",
        "CATRelationalWaves","CATRadiusComparison","BoundaryExchangeRecovery","CATVacuaSky","CATReviewChannel","CATObserverDomain")
NUMERICS={
    "cat_domain_calibration":("cat-domain-calibration",()),
    "cat_joint_receiver_revision":("cat-joint-receiver-revision",()),
    "cat_relational_collapse":("cat-relational-collapse",("clifford","fall","hydrogen","angular_receipt","predictions")),
    "preterminal_matching":("preterminal-matching",("links","interference","inclusive")),
    "compact_matrix_radiation":("compact-matrix-radiation",("adopted_action","cat_matrix_forms")),
    "cat_relational_waves":("cat-relational-waves",("curvature","wave","receipts")),
    "cat_sky_geometry":("cat-sky-geometry",("pantheon_local","bao","sky_tests")),
    "cat_vacua_sky":("cat-vacua-sky",("orientifold","sky","collapse")),
    "cat_radius_comparison":("cat-radius-comparison",("static_sector","cat_contacts","force_at_contact")),
}


def need(test,message):
    if not test: raise ValueError(message)


def audit():
    manifest=json.loads((BASE/"manifest.json").read_text("utf8"))
    for name,expected in manifest["files"].items():
        actual=hashlib.sha256((BASE/name).read_bytes()).hexdigest()
        need(actual==expected,"Checksum mismatch: "+name)
    ex=json.loads((BASE/"evidence/experiments.json").read_text("utf8"))
    need(set(ex)=={f"RES-{n:04d}" for n in range(93,184)},"Coverage gap")
    for key,row in ex.items():
        paths=row["checks"]+row["artifacts"]+row["records"]
        if row["derivation"]:paths.append(row["derivation"])
        need(all((BASE/f).is_file() for f in paths) and row["database_pages"],key)
    print("SHA-256:",len(manifest["files"]),"files. Result records:",len(ex))


def quick():
    # No third-party dependency. Populate shifted columns by linear constraints on every entry.
    for n in range(1,12):
        for m in range(0,13):
            nodes=[(i,j) for i in range(n+1) for j in range(m+1)]
            parent={u:u for u in nodes}
            def root(u):
                while parent[u]!=u:
                    parent[u]=parent[parent[u]];u=parent[u]
                return u
            for i in range(n):
                for j in range(m):
                    parent[root((i+1,j+1))]=root((i,j))
            dead={root((i,0)) for i in range(1,n+1)} | {root((i,m)) for i in range(n)}
            dimension=len({root(u) for u in nodes}-dead)
            need(dimension==max(m-n+1,0),"inward link dimension")
    bits=[F(comb(4,k),16) for k in range(5)]
    any_echo=bits[0]**2+(1-bits[0])**2
    count_echo=sum(p*p for p in bits)
    fine_echo=16*F(1,16)**2
    need((any_echo,count_echo,fine_echo)==(F(226,256),F(70,256),F(1,16)),"charge grouping")
    for deg in (0,30,60,90):
        x=cos(deg*pi/180)
        need(isclose((1+x*x)/2,1-(1-x*x)/2),"spin-axis survival")
    axial=(1+sqrt((15/16)*(1/2))+sqrt((1/16)*(1/2)))/2
    need(isclose(axial,0.9307149457,abs_tol=1e-8),"axial receiver")
    need(isclose(2*sqrt(.25)/(1+.25)*.5,.4),"two-image visibility")
    need(isclose(1/sqrt(.9),1.0540925534),"siren/distance ratio")
    need(isclose(1/(1-.9**2),5.263157895),"dephased repeated tide")
    print("143 independent finite-link counts passed; four-receiver echoes =",any_echo,count_echo,fine_echo)
    print("Flagged qubit fidelity = %.9f; FRB visibility cap = 0.4"%axial)


def prepare_lean(cache,external):
    if external: loc=external.resolve()
    else:
        loc=cache/"lean-runtime";loc.mkdir(parents=True,exist_ok=True)
        packs=BASE/"evidence/lean-toolchain"
        if not (loc/"ready").exists():
            if os.name=="nt":
                with zipfile.ZipFile(packs/"lean-win.zip") as z:z.extractall(loc)
            elif sys.platform=="linux" and platform.machine()=="x86_64":
                with tarfile.open(packs/"lean-linux.tar.gz") as tar:tar.extractall(loc,filter="data")
            with tarfile.open(packs/"mathlib-src.tar.gz") as tar:tar.extractall(loc,filter="data")
            math=loc/("mathlib3-"+COMMIT)
            with tarfile.open(packs/"mathlib-cache.tar.xz") as tar:tar.extractall(math,filter="data")
            (loc/"ready").write_text(COMMIT,"utf8")
    math=loc/("mathlib3-"+COMMIT)/"src"
    if os.name=="nt":
        lean=loc/"lean-3.51.1-windows/bin/lean.exe"
        core=loc/"lean-3.51.1-windows/lib/lean/library"
    else:
        bundled=loc/"lean-3.51.1-linux/bin/lean"
        command=str(bundled) if bundled.is_file() else shutil.which("lean")
        need(command,"Install Lean 3.51.1 on this operating system.")
        lean=Path(command)
        env=os.environ.copy();env.pop("LEAN_PATH",None)
        paths=json.loads(subprocess.check_output([str(lean),"--path"],env=env,text=True))["path"]
        core=next(Path(s) for s in paths if (Path(s)/"init").is_dir())
    need(math.is_dir() and core.is_dir(),"Missing Lean library or mathlib")
    version=subprocess.check_output([str(lean),"--version"],text=True).strip()
    need("3.51.1" in version,"Incorrect Lean version: "+version)
    env=os.environ.copy();env["LEAN_PATH"]=os.pathsep.join(map(str,(core,math,WORK/"verification")))
    return lean,env,version


def lean_checks(cache,external,names,jobs):
    lean,env,version=prepare_lean(cache,external)
    print(version,flush=True)
    logdir=cache/"proof-logs";logdir.mkdir(parents=True,exist_ok=True)
    def compile_one(name):
        path=WORK/"verification"/(name+".lean")
        need(path.is_file() and path.parent==WORK/"verification","Unknown proof module "+name)
        run=subprocess.run([str(lean),"-T","120000","-j","2",str(path)],env=env,
                           capture_output=True,text=True,encoding="utf8",errors="replace")
        log=run.stdout+run.stderr
        (logdir/(name+".log")).write_text(log,"utf8")
        need(run.returncode==0 and "uses 'sorry'" not in log and "error:" not in log,name+" failed: "+log[-900:])
        print(name,"verified",flush=True)
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
        list(pool.map(compile_one,names))


def numerical(cache,names):
    env=os.environ.copy();env.update(OPENBLAS_NUM_THREADS="1",OMP_NUM_THREADS="1",MKL_NUM_THREADS="1",
                                     MPLBACKEND="Agg",PYTHONDONTWRITEBYTECODE="1",PYTHONUTF8="1")
    cache.mkdir(parents=True,exist_ok=True)
    root=(cache/("numeric-"+uuid.uuid4().hex)).resolve()
    need(root.parent==cache.resolve(),"Unexpected scratch path")
    root.mkdir()
    try:
        for part in ("code","data","verification"):
            shutil.copytree(WORK/part,root/part)
        for name in names:
            target,keys=NUMERICS[name]
            file=target+"-results.json"
            old=json.loads((WORK/"verification"/file).read_text("utf8"))
            fresh=root/"verification"/file
            fresh.unlink(missing_ok=True)
            run=subprocess.run([sys.executable,"-B",str(root/"code"/(name+".py"))],cwd=root,env=env,
                               stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding="utf8",errors="replace")
            need(run.returncode==0,name+": "+run.stdout[-1500:])
            need(fresh.is_file(),name+" did not regenerate its table")
            new=json.loads(fresh.read_text("utf8"))
            count=compare(old,new,target)
            print(name, len(old), "groups,",count,"floating values compared",flush=True)
    except Exception:
        print("Reproduction inputs and outputs retained in",root)
        raise
    else:
        shutil.rmtree(root)

def study(cache,names):
    if not names:raise SystemExit("Provide a result ID, optionally followed by one program name.")
    entries=json.loads((BASE/"evidence/experiments.json").read_text("utf8"))
    record=entries[names[0].upper()]
    candidates=[BASE/p for p in record["artifacts"] if "/code/" in p and p.endswith(".py")]
    runnable=[p for p in candidates if p.name!="prepare_cat_sky_sample.py"
              and "__main__" in p.read_text("utf-8-sig")]
    print("Programs linked to this result:",", ".join(p.name for p in candidates),flush=True)
    if len(names)>1:
        requested={p.removesuffix(".py") for p in names[1:]}
        runnable=[p for p in runnable if p.stem in requested]
        need({p.stem for p in runnable}==requested,"Unknown program, helper module, or source acquisition program")
    need(runnable,"See this result's verification record for its shared driver.")
    root=(cache/("study-"+uuid.uuid4().hex)).resolve()
    need(root.parent==cache.resolve(),"Unexpected scratch path")
    root.mkdir(parents=True)
    for part in ("code","data","verification"):shutil.copytree(WORK/part,root/part)
    (root/"manuscripts").mkdir()
    (root/".research-tools").mkdir()
    env=os.environ.copy()
    env.update(OPENBLAS_NUM_THREADS="1",OMP_NUM_THREADS="1",MKL_NUM_THREADS="1",MPLBACKEND="Agg",
               MPLCONFIGDIR=str(root/".matplotlib"),PYTHONDONTWRITEBYTECODE="1",PYTHONUTF8="1")
    print("Scratch workspace, including generated outputs:",root,flush=True)
    for p in runnable:
        dest=root/(p.stem+".log")
        with dest.open("w",encoding="utf8") as log:
            run=subprocess.run([sys.executable,"-B",str(root/"code"/p.name)],cwd=root,env=env,
                               stdout=log,stderr=subprocess.STDOUT)
        need(run.returncode==0,f"{p.name}: inspect {dest}")
        print(p.name,"completed",flush=True)


def cli():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command",choices=("check","quick","numerical","lean","study"))
    parser.add_argument("names",nargs="*",help="Optional numerical program or Lean module name")
    parser.add_argument("--cache",type=Path,default=BASE/".review-cache",help="Local scratch directory")
    parser.add_argument("--toolchain",type=Path,help="Existing extracted Lean and mathlib root")
    parser.add_argument("--jobs",type=int,default=2)
    args=parser.parse_args()
    if args.command=="check":audit();quick();regression()
    elif args.command=="quick":quick()
    elif args.command=="lean":lean_checks(args.cache,args.toolchain,args.names or PROOFS,max(1,args.jobs))
    elif args.command=="numerical":numerical(args.cache,args.names or NUMERICS)
    elif args.command=="study":study(args.cache,args.names)


if __name__=="__main__":
    cli()

