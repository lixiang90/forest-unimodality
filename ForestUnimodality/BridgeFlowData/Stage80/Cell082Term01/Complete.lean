import ForestUnimodality.BridgeFlowData.Stage80.Cell082Term01.Batch000

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell082Term01
open CoupledFlow


def rows : List Row := Batch000.rows

theorem rows_length : rows.length=24 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  exact Batch000.rows_checked

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (11528870732482263314502679764973036037/100000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (5514438288794763107940497243676889033479/5000000000000000000000000000000000000000)

def table : Table :=
  ⟨24, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨1, (-1996269240544429/2500000000000000), 64, (45000000000000000479012989603387024036655636261287/100000000000000000000000000000000000000000000000000), (5625000000000000059876623700423378004581954532661/12500000000000000000000000000000000000000000000000)⟩, (45000000000000000479012989603387024036655636261287/100000000000000000000000000000000000000000000000000), (5625000000000000059876623700423378004581954532661/12500000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage80.Cell082Term01
