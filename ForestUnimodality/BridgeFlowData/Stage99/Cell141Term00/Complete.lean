import ForestUnimodality.BridgeFlowData.Stage99.Cell141Term00.Batch000

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell141Term00
open CoupledFlow


def rows : List Row := Batch000.rows

theorem rows_length : rows.length=6 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  exact Batch000.rows_checked

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (117753640875201659055352957292483145887/312500000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (10811337118484900741472172257058632177529/10000000000000000000000000000000000000000)

def table : Table :=
  ⟨6, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨1, (-22313309274318957/100000000000000000), 64, (4000041834502844921286619619830855915972509703653/5000000000000000000000000000000000000000000000000), (80000836690056898425732392396617118319450194073061/100000000000000000000000000000000000000000000000000)⟩, (4000041834502844921286619619830855915972509703653/5000000000000000000000000000000000000000000000000), (80000836690056898425732392396617118319450194073061/100000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage99.Cell141Term00
