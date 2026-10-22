#!/usr/bin/env python3
"""Bounded negative controls for source-integrity gates; no theorem claims."""
import hashlib,json,pathlib,subprocess,sys,tempfile
BASE=pathlib.Path(__file__).resolve().parent
CASES=[('clean','namespace SparseComponent.Bad\ndef value : Nat := 3\nend SparseComponent.Bad\n',False,False),('wrong_hash','namespace SparseComponent.Bad\ndef value : Nat := 3\nend SparseComponent.Bad\n',True,True),('explicit_axiom','axiom bad : False\n',False,True),('sorry_body','theorem bad : False := by sorry\n',False,True),('comment_only','/- outer /- nested -/ axiom bad : False -/\ndef value : Nat := 3\n',False,False)]
rows=[]
with tempfile.TemporaryDirectory(prefix='sparse-source-negative-') as t:
 root=pathlib.Path(t);(root/'SparseComponent').mkdir();p=root/'SparseComponent/Bad.lean'
 for optimized in [False,True]:
  for name,source,wrong,fail in CASES:
   p.write_text(source);h=hashlib.sha256(p.read_bytes()).hexdigest();m={'source_commit':'test-fixture-only','modules':['SparseComponent.Bad'],'files':{'SparseComponent/Bad.lean':'0'*64 if wrong else h}}
   manifest=root/'MANIFEST.json';manifest.write_text(json.dumps(m));cmd=[sys.executable]+(['-O'] if optimized else [])+[str(BASE/'check_publication_sources.py'),'--root',str(root),'--manifest',str(manifest)]
   r=subprocess.run(cmd,text=True,capture_output=True);j=json.loads(r.stdout);expected=(r.returncode!=0)==fail
   rows.append({'case':name,'optimized':optimized,'returncode':r.returncode,'expected_failure':fail,'expected_result_observed':expected,'result':j})
   if not expected:raise RuntimeError(name)
(BASE/'CHECKER_NEGATIVE_CONTROLS.json').write_text(json.dumps({'status':'PASS','checks':len(rows),'tests':rows},indent=2)+'\n');print('PASS',len(rows),'source-checker controls')
