import ForestUnimodality.BridgeFlowData.Stage99.Cell057Term03.Batch000

import ForestUnimodality.BridgeFlowData.Stage99.Cell057Term03.Batch001

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell057Term03
open CoupledFlow


def rows : List Row := Batch000.rows ++ Batch001.rows

theorem rows_length : rows.length=30 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  simp only [rows,List.all_append,Batch000.rows_checked, Batch001.rows_checked,Bool.and_self]

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (20787742693221904784465793661012071969/10000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (1688328035433794310945562903075835906979/1000000000000000000000000000000000000000)

def table : Table :=
  ⟨30, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨3, (-59914645471079819868704471522850815513/60000000000000000000000000000000000000), 64, (4605039373300483257224778541974759027437406487217/12500000000000000000000000000000000000000000000000), (36840314986403866057798228335798072219499251897737/100000000000000000000000000000000000000000000000000)⟩, (97656250000000000000000000000000000002597814745014753494723315905157561892807411726594318829266784716510931828011077048260729532569505846228247313/1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (50000000000000000000000000000000000001330081149451625415723230103297948823321914037823571110152898755664273356198610395875778832610752934758824094553/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage99.Cell057Term03
