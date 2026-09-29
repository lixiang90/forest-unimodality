import ForestUnimodality.BridgeFlowData.Stage80.Cell220Term01.Batch000

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell220Term01
open CoupledFlow


def rows : List Row := Batch000.rows

theorem rows_length : rows.length=14 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  exact Batch000.rows_checked

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (8217400804898796449144314007434548381/1250000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (10436775410584931068326878847452796121759/5000000000000000000000000000000000000000)

def table : Table :=
  ⟨14, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨2, (-138629436111989061883446424291635313613/200000000000000000000000000000000000000), 64, (12500000000000000000000000000000000000131251679503/25000000000000000000000000000000000000000000000000), (50000000000000000000000000000000000000525006718013/100000000000000000000000000000000000000000000000000)⟩, (156250000000000000000000000000000000003281291987575000000000000000000000000017227003372358230327009/625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (2500000000000000000000000000000000000052500671801300000000000000000000000000275632053958781698668169/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage80.Cell220Term01
