import ForestUnimodality.BridgeFlowData.Stage99.Cell075Term01.Batch000

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell075Term01
open CoupledFlow


def rows : List Row := Batch000.rows

theorem rows_length : rows.length=600 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  exact Batch000.rows_checked

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (3538949671545868208022198292965648397/2000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (862833596509703487483263751837877598127/500000000000000000000000000000000000000)

def table : Table :=
  ⟨600, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨3, (-59914645471079819868704471522850815513/60000000000000000000000000000000000000), 64, (4605039373300483257224778541974759027437406487217/12500000000000000000000000000000000000000000000000), (36840314986403866057798228335798072219499251897737/100000000000000000000000000000000000000000000000000)⟩, (97656250000000000000000000000000000002597814745014753494723315905157561892807411726594318829266784716510931828011077048260729532569505846228247313/1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (50000000000000000000000000000000000001330081149451625415723230103297948823321914037823571110152898755664273356198610395875778832610752934758824094553/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

theorem header_checked : table.headerCheck=true := by decide +kernel

theorem connections_checked : (List.range table.n).all table.connectionCheck=true := by decide +kernel

theorem table_rows_checked : (List.range table.n).all (fun i=>(table.row i).check table.environment)=true := by

  apply List.all_eq_true.mpr
  intro i hi
  apply check_getD rows Batch000.row000 environment rows_checked i
  rw [rows_length]
  exact List.mem_range.mp hi

#print axioms header_checked

#print axioms connections_checked

#print axioms table_rows_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell075Term01
