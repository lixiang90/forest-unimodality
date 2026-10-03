import concurrent.futures,hashlib,json,os,subprocess,time
from pathlib import Path
R=Path(__file__).resolve().parent;B=R.parent
cache=json.loads((B/'benchmark-128x64-20261002/run/progress.json').read_text())['lean_path']
lean=B/'toolchain/bin/lean'
owner=dict(pid=os.getpid(),start_ticks=Path('/proc/self/stat').read_text().split()[21],boot_id=Path('/proc/sys/kernel/random/boot_id').read_text().strip(),command=str(Path(__file__).resolve()))
def save(name,data):
 tmp=R/(name+'.tmp');tmp.write_text(json.dumps(data,indent=2));tmp.replace(R/name)
save('owner.json',owner);save('status.json',dict(owner,phase='running'))
def run(label,module,extra=''):
 root=R/label;source=root/(module.replace('.','/')+'.lean');output=root/'lib'/(module.replace('.','/')+'.olean');output.parent.mkdir(parents=True,exist_ok=True)
 env=dict(os.environ,LEAN_PATH=extra+cache,LEAN_NUM_THREADS='1')
 cmd=['/usr/bin/time','-v','-o',str(root/'time.txt'),str(lean),'-j','1','-Dpp.fullNames=true','-o',str(output),str(source.relative_to(root))]
 start=time.monotonic()
 with (root/'lean.log').open('wb') as f:p=subprocess.run(cmd,cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT)
 log=(root/'lean.log').read_text();rss=None
 for line in (root/'time.txt').read_text().splitlines():
  if 'Maximum resident set size (kbytes):' in line:rss=int(line.split(':')[-1])
 return dict(label=label,module=module,exit_code=p.returncode,wall_seconds=time.monotonic()-start,peak_rss_kib=rss,source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),output_bytes=output.stat().st_size if output.exists() else None,log=log,command=cmd)
try:
 prefix='ForestUnimodality.Stage80MessageSourceData.Case005.'
 with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
  futures=[pool.submit(run,'baseline',prefix+'ReferenceBatch018'),pool.submit(run,'simplified',prefix+'Batch018')]
  results=[f.result() for f in futures]
 save('status.json',dict(owner,phase='equality-check',results=results))
 assert all(x['exit_code']==0 for x in results),results
 equality=run('equality','Equality',str(R/'simplified/lib')+':'+str(R/'baseline/lib')+':')
 passed=equality['exit_code']==0 and all('cells_checked' in x['log'] and 'sorryAx' not in x['log'] and 'ofReduceBool' not in x['log'] for x in results)
 report=dict(owner,phase='complete',passed=passed,results=results,equality=equality,scope='Paired module test with cached verified imports; baseline batch namespace renamed ReferenceBatch018 so the exact cell values can be compared by rfl. Not a downstream closure rebuild.')
except Exception as e:report=dict(owner,phase='failed',error=repr(e))
save('report.json',report);save('status.json',report)
