"""Execute and record validation; never claim an unexecuted check passed."""
from pathlib import Path
import hashlib,json,os,platform,subprocess,sys,time,shutil
ROOT=Path(__file__).resolve().parents[1]
EV=ROOT/'evidence';EV.mkdir(exist_ok=True)
commands=[
 ('python-tests',[sys.executable,'-m','pytest','-q','tests/test_two_tail_uniform.py']),
 ('independent-replay',[sys.executable,'tools/independent_replay.py']),
 ('receipt-regenerated',[sys.executable,'oracles/two_tail_uniform.py','--receipt']),
]
runs=[]
for label,cmd in commands:
    start=time.monotonic()
    proc=subprocess.run(cmd,cwd=ROOT,env={**os.environ,'PYTEST_DISABLE_PLUGIN_AUTOLOAD':'1'},capture_output=True,text=True)
    (EV/(label+'.stdout.txt')).write_text(proc.stdout)
    (EV/(label+'.stderr.txt')).write_text(proc.stderr)
    runs.append({'argv':cmd,'cwd':'.','label':label,'exit_code':proc.returncode,
                 'seconds':round(time.monotonic()-start,3),'stdout':label+'.stdout.txt','stderr':label+'.stderr.txt'})
    if proc.returncode:
        print(proc.stdout,proc.stderr);raise SystemExit(proc.returncode)
    if label=='receipt-regenerated':
        if json.loads(proc.stdout)!=json.loads((EV/'receipt.json').read_text()):
            raise SystemExit('receipt mismatch')
        runs[-1]['committed_receipt_equal']=True
    if label=='independent-replay':
        (EV/'independent-replay.json').write_text(proc.stdout)
manifest={'date':'2026-11-06','repo_main_inspected':'ba09fdbd770248905a297303b8de45b3d7c5018d',
          'scope':'two infinite literal run families; unbounded proof separate from finite controls',
          'python':sys.version,'platform':platform.platform(),'executed':runs,
          'compiler_availability':{s:shutil.which(s) for s in ('mojo','pixi','lean','lake')},
          'not_executed':['native Mojo','Lean/proof-assistant formalization','hosted CI','repository-wide gates','independent human review'],
          'previous_failed_attempt':{'stdout':'independent-initial.stdout.txt','stderr':'independent-initial.stderr.txt',
                                     'exit_code':1,'reason':'SymPy same-named symbols with different assumptions; cross-check harness repaired'},
          'source_hashes':{}}
for p in sorted(ROOT.rglob('*')):
    if not p.is_file() or '__pycache__' in p.parts or '.pytest_cache' in p.parts:continue
    if p.name=='local-validation.json':continue
    data=p.read_bytes();relative=p.relative_to(ROOT).as_posix()
    manifest['source_hashes'][relative]={'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest(),
       'git_blob_sha':hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()}
(EV/'local-validation.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'passed','commands':len(runs),'tests_stdout':(EV/'python-tests.stdout.txt').read_text(),
                   'independent':json.loads((EV/'independent-replay.json').read_text()),
                   'compiler_availability':manifest['compiler_availability']},indent=2))
