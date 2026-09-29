import ForestUnimodality.BridgeFlowData.Stage99.Cell046Term01.Batch000

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell046Term01
open CoupledFlow


def rows : List Row := Batch000.rows

theorem rows_length : rows.length=160 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  exact Batch000.rows_checked

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (555102391771566575464557637441484475721/5000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (2117296717328610294323681083370943395807/2000000000000000000000000000000000000000)

def table : Table :=
  ⟨160, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨1, (-19962692405444290266118327557437234159/25000000000000000000000000000000000000), 64, (22500000000000000000000000000000000000486461415229/50000000000000000000000000000000000000000000000000), (45000000000000000000000000000000000000972922830459/100000000000000000000000000000000000000000000000000)⟩, (22500000000000000000000000000000000000486461415229/50000000000000000000000000000000000000000000000000), (45000000000000000000000000000000000000972922830459/100000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage99.Cell046Term01
