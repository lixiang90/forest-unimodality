import ForestUnimodality.BridgeFlowData.Stage99.Cell175Term00.Batch000

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell175Term00
open CoupledFlow


def rows : List Row := Batch000.rows

theorem rows_length : rows.length=11 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  exact Batch000.rows_checked

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (1998756861137589287254413607005979974973/10000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (3537284887114400108649722815662346959169/2500000000000000000000000000000000000000)

def table : Table :=
  ⟨11, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨1, (-17833747196936618945631935562059223897/50000000000000000000000000000000000000), 64, (70000000000000000000000000000000000001681173133283/100000000000000000000000000000000000000000000000000), (17500000000000000000000000000000000000420293283321/25000000000000000000000000000000000000000000000000)⟩, (70000000000000000000000000000000000001681173133283/100000000000000000000000000000000000000000000000000), (17500000000000000000000000000000000000420293283321/25000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage99.Cell175Term00
