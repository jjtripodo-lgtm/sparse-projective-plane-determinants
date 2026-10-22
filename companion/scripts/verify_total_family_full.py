#!/usr/bin/env python3
"""Pinned, source-bound fresh replay of the unrestricted total-density family through fourteen."""
from __future__ import annotations
import argparse, datetime, hashlib, json, os, pathlib, re, shutil, subprocess, time
ROOT=pathlib.Path(__file__).resolve().parents[1]
COMPILER='fd009949156901e6cf15b6d9bf1122294b8e697a'
MATHLIB='0ed37c9258f123a2c76a2175596f75c2bd50f941'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--lean',required=True);ap.add_argument('--mathlib',type=pathlib.Path,required=True);ap.add_argument('--memory',type=int,default=4096);ap.add_argument('--build',type=pathlib.Path,default=ROOT/'.build-total-family-full');ap.add_argument('--output',type=pathlib.Path,default=ROOT/'audit/total_family_full/replay');a=ap.parse_args()
 a.mathlib=a.mathlib.resolve();a.output.mkdir(parents=True,exist_ok=True)
 if subprocess.check_output([a.lean,'--githash'],text=True).strip()!=COMPILER:raise RuntimeError('Wrong compiler')
 if subprocess.check_output(['git','-C',str(a.mathlib),'rev-parse','HEAD'],text=True).strip()!=MATHLIB:raise RuntimeError('Wrong mathlib pin')
 manifest=json.loads((ROOT/'audit/total_family_full/SOURCE_MANIFEST.json').read_text())
 for p,h in manifest['files'].items():
  if sha(ROOT/p)!=h:raise RuntimeError('Source changed: '+p)
  if p.startswith('SparseComponent/') and p.endswith('.lean'):
   text=re.sub(r'/\-.*?\-/','',(ROOT/p).read_text(),flags=re.S);text=re.sub(r'--[^\n]*','',text)
   if re.search(r'\b(sorry|admit|native_decide|axiom|unsafe|implemented_by|extern)\b',text):raise RuntimeError('Forbidden proof escape: '+p)
 if a.build.exists():shutil.rmtree(a.build)
 lib=a.build/'lib/lean';lib.mkdir(parents=True)
 env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,[lib,*sorted((a.mathlib/'.lake/packages').glob('*/.lake/build/lib/lean')),a.mathlib/'.lake/build/lib/lean']))
 runs=[]
 def run(label,p,out=None,strict=False):
  cmd=[a.lean,'-j','1','-M',str(a.memory),'-D','Elab.async=false']
  if strict:cmd+=['-t','0']
  if out:out.parent.mkdir(parents=True,exist_ok=True);cmd+=['-o',str(out)]
  cmd+=[str(p)];log=a.output/(label+'.log');start=time.monotonic()
  (a.output/'CURRENT_STAGE.json').write_text(json.dumps({'label':label,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'command':cmd},indent=2)+'\n')
  with log.open('w') as f:
   proc=subprocess.Popen(cmd,cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT);_,st,use=os.wait4(proc.pid,0);proc.returncode=os.waitstatus_to_exitcode(st)
  row={'label':label,'returncode':proc.returncode,'seconds':round(time.monotonic()-start,3),'max_rss_kib':use.ru_maxrss,'command':cmd,'source_sha256':sha(p),'log_sha256':sha(log),'object_sha256':sha(out) if out and out.exists() else None};runs.append(row)
  (a.output/'RUNS.json').write_text(json.dumps(runs,indent=2)+'\n');print(json.dumps(row),flush=True)
  if proc.returncode:raise RuntimeError(log.read_text())
 for m in manifest['modules']:
  p=pathlib.Path(m.replace('.','/')+'.lean');run(m.replace('.','_'),ROOT/p,lib/p.with_suffix('.olean'))
 run('BodyAudit',ROOT/'audit/total_family_full/BodyAudit.lean')
 run('StrictFullFamily',ROOT/'SparseComponent/TotalFamily/FullFamily.lean',strict=True)
 body=[json.loads(l[len('BODY_AUDIT '):]) for l in (a.output/'BodyAudit.log').read_text().splitlines() if l.startswith('BODY_AUDIT ')]
 if len(body)!=1:raise RuntimeError('Missing body audit')
 decls=[json.loads(l[5:]) for l in (a.output/'BodyAudit.log').read_text().splitlines() if l.startswith('DECL ')]
 if not decls or len({d['name'] for d in decls})!=len(decls):raise RuntimeError('Empty/duplicate audit')
 (a.output/'ALL_DECLARATIONS.json').write_text(json.dumps(decls,indent=2)+'\n')
 rec={'status':'passed','compiler':COMPILER,'mathlib_pin':MATHLIB,'project_object_reuse':False,'mathlib_object_reuse':True,'memory_mb':a.memory,'jobs':1,'source_manifest_sha256':sha(ROOT/'audit/total_family_full/SOURCE_MANIFEST.json'),'runs':runs,'declaration_count':len(decls),'body_audit':body[0],'scope':manifest['scope']}
 (a.output/'VALIDATION.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps({'status':'passed','body_audit':body[0]}))
if __name__=='__main__':main()
