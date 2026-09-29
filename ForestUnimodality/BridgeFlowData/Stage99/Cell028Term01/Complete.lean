import ForestUnimodality.BridgeFlowData.Stage99.Cell028Term01.Batch000

import ForestUnimodality.BridgeFlowData.Stage99.Cell028Term01.Batch001

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell028Term01
open CoupledFlow


def rows : List Row := Batch000.rows ++ Batch001.rows

theorem rows_length : rows.length=72 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  simp only [rows,List.all_append,Batch000.rows_checked, Batch001.rows_checked,Bool.and_self]

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (2569346612187627977201956410988454267433/10000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (73518193077076469261695446245761891623/78125000000000000000000000000000000000)

def table : Table :=
  ⟨72, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨1, (-17833747196936618945631935562059223897/50000000000000000000000000000000000000), 64, (70000000000000000000000000000000000001681173133283/100000000000000000000000000000000000000000000000000), (17500000000000000000000000000000000000420293283321/25000000000000000000000000000000000000000000000000)⟩, (70000000000000000000000000000000000001681173133283/100000000000000000000000000000000000000000000000000), (17500000000000000000000000000000000000420293283321/25000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage99.Cell028Term01
