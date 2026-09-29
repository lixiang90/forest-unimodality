import ForestUnimodality.BridgeFlowData.Stage80.Cell219Term01.Batch000

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell219Term01
open CoupledFlow


def rows : List Row := Batch000.rows

theorem rows_length : rows.length=13 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  exact Batch000.rows_checked

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (910676800808794317523706090451101167169/2500000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (6256045323772820720684124366726144066463/5000000000000000000000000000000000000000)

def table : Table :=
  ⟨13, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨1, (-4462871026284195115325901806196690067/20000000000000000000000000000000000000), 64, (250000000000000000000000000000000000006150271387/312500000000000000000000000000000000000000000000), (80000000000000000000000000000000000001968086843841/100000000000000000000000000000000000000000000000000)⟩, (250000000000000000000000000000000000006150271387/312500000000000000000000000000000000000000000000), (80000000000000000000000000000000000001968086843841/100000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage80.Cell219Term01
