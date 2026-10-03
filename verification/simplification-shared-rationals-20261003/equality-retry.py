
import json,os,subprocess,time
from pathlib import Path
B=Path('/home/admin0486/forest-verification-fc5696db-20261002');R=B/'simplification-20261003-shared-rationals';C=B/'benchmark-128x64-20261002/source/.lake/build/lib/lean';O=R/'equality-overlay';O.mkdir()
for p in C.rglob('*'):
 q=O/p.relative_to(C)
 if p.is_dir():q.mkdir(exist_ok=True)
 else:q.symlink_to(p)
for label,name in [('simplified','Batch018'),('baseline','ReferenceBatch018')]:
 rel=Path('ForestUnimodality/Stage80MessageSourceData/Case005')/(name+'.olean');q=O/rel
 if q.is_symlink():q.unlink()
 assert not q.exists();q.symlink_to(R/label/'lib'/rel)
cache=json.loads((B/'benchmark-128x64-20261002/run/progress.json').read_text())['lean_path'];E=R/'equality-retry';E.mkdir();(E/'Equality.lean').write_bytes((R/'equality/Equality.lean').read_bytes())
cmd=['/usr/bin/time','-v','-o',str(E/'time.txt'),str(B/'toolchain/bin/lean'),'-j','1','-Dpp.fullNames=true','-o',str(E/'Equality.olean'),'Equality.lean'];env=dict(os.environ,LEAN_PATH=str(O)+':'+cache,LEAN_NUM_THREADS='1')
start=time.monotonic()
with (E/'lean.log').open('wb') as f:p=subprocess.run(cmd,cwd=E,env=env,stdout=f,stderr=subprocess.STDOUT)
report=dict(exit_code=p.returncode,wall_seconds=time.monotonic()-start,log=(E/'lean.log').read_text(),command=cmd,overlay='Symlinks to verified benchmark imports, overriding only the two tested module objects; original object trees unchanged.')
(E/'report.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
