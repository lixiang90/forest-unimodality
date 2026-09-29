import ForestUnimodality.LowActivityFlowData.Cell004.Batch000

import ForestUnimodality.LowActivityFlowData.Cell004.Batch001

import ForestUnimodality.LowActivityFlowData.Cell004.Batch002

import ForestUnimodality.LowActivityFlowData.Cell004.Batch003

import ForestUnimodality.LowActivityFlowData.Cell004.Batch004

import ForestUnimodality.LowActivityFlowData.Cell004.Batch005

import ForestUnimodality.LowActivityFlowData.Cell004.Batch006

import ForestUnimodality.LowActivityFlowData.Cell004.Batch007

import ForestUnimodality.LowActivityFlowData.Cell004.Batch008

import ForestUnimodality.LowActivityFlowData.Cell004.Batch009

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.LowActivityFlowData.Cell004
open LowActivityFlow


def rows : List Row := Batch000.rows ++ Batch001.rows ++ Batch002.rows ++ Batch003.rows ++ Batch004.rows ++ Batch005.rows ++ Batch006.rows ++ Batch007.rows ++ Batch008.rows ++ Batch009.rows

theorem rows_length : rows.length=300 := rfl

theorem rows_checked : rows.all (fun r=>r.check b beta)=true := by

  simp only [rows,List.all_append,Batch000.rows_checked, Batch001.rows_checked, Batch002.rows_checked, Batch003.rows_checked, Batch004.rows_checked, Batch005.rows_checked, Batch006.rows_checked, Batch007.rows_checked, Batch008.rows_checked, Batch009.rows_checked,Bool.and_self]

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (20375011245895617149334575085304028669/10000000000000000000000000000000000000000)

def table : Table :=
  ⟨300, qa, b, beta, retention, rate, timeAt, lowerAt, rowAt, ⟨3, (-59914645471079819868704471522850815513/60000000000000000000000000000000000000), 64, (4605039373300483257224778541974759027437406487217/12500000000000000000000000000000000000000000000000), (36840314986403866057798228335798072219499251897737/100000000000000000000000000000000000000000000000000)⟩, (97656250000000000000000000000000000002597814745014753494723315905157561892807411726594318829266784716510931828011077048260729532569505846228247313/1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (50000000000000000000000000000000000001330081149451625415723230103297948823321914037823571110152898755664273356198610395875778832610752934758824094553/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

theorem header_checked : table.headerCheck=true := by decide +kernel

theorem connections_checked : (List.range table.n).all table.connectionCheck=true := by decide +kernel

theorem table_rows_checked : (List.range table.n).all (fun i=>(table.row i).check table.b table.beta)=true := by

  apply List.all_eq_true.mpr
  intro i hi
  apply check_getD rows Batch000.row000 b beta rows_checked i
  rw [rows_length]
  exact List.mem_range.mp hi

#print axioms header_checked

#print axioms connections_checked

#print axioms table_rows_checked

end ForestUnimodality.LowActivityFlowData.Cell004
