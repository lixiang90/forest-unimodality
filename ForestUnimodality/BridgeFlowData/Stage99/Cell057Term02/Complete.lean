import ForestUnimodality.BridgeFlowData.Stage99.Cell057Term02.Batch000

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell057Term02
open CoupledFlow


def rows : List Row := Batch000.rows

theorem rows_length : rows.length=24 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  exact Batch000.rows_checked

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (1417476058550881931519094671962805196659/10000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (10805314249277048420422374061114076242439/10000000000000000000000000000000000000000)

def table : Table :=
  ⟨24, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨1, (-6931471805599453/10000000000000000), 64, (12500000000000000117715401518227207655220381863401/25000000000000000000000000000000000000000000000000), (10000000000000000094172321214581766124176305490721/20000000000000000000000000000000000000000000000000)⟩, (12500000000000000117715401518227207655220381863401/25000000000000000000000000000000000000000000000000), (10000000000000000094172321214581766124176305490721/20000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage99.Cell057Term02
