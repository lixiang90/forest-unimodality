import ForestUnimodality.BridgeFlowData.Stage99.Cell154Term01.Batch000

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell154Term01
open CoupledFlow


def rows : List Row := Batch000.rows

theorem rows_length : rows.length=8 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  exact Batch000.rows_checked

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (2107435012108793973322258891561654995051/10000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (11411812406929301912207058910323634855011/10000000000000000000000000000000000000000)

def table : Table :=
  ⟨8, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨1, (-10205496262783/20000000000000), 64, (30016528870526093820041069364048504541677286926109/50000000000000000000000000000000000000000000000000), (60033057741052187640082138728097009083354573852219/100000000000000000000000000000000000000000000000000)⟩, (30016528870526093820041069364048504541677286926109/50000000000000000000000000000000000000000000000000), (60033057741052187640082138728097009083354573852219/100000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage99.Cell154Term01
