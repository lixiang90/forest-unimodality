import ForestUnimodality.CoupledFlowData.Cell097Term00.Batch000

import ForestUnimodality.CoupledFlowData.Cell097Term00.Batch001

import ForestUnimodality.CoupledFlowData.Cell097Term00.Batch002

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell097Term00
open CoupledFlow


def rows : List Row := Batch000.rows ++ Batch001.rows ++ Batch002.rows

theorem rows_length : rows.length=36 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  simp only [rows,List.all_append,Batch000.rows_checked, Batch001.rows_checked, Batch002.rows_checked,Bool.and_self]

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (339845509808108967715354374104352088599/1250000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (5126127428456548873783720119688929305331/5000000000000000000000000000000000000000)

def table : Table :=
  ⟨36, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨1, (-17833747196936618945631935562059223897/50000000000000000000000000000000000000), 64, (70000000000000000000000000000000000001681173133283/100000000000000000000000000000000000000000000000000), (17500000000000000000000000000000000000420293283321/25000000000000000000000000000000000000000000000000)⟩, (70000000000000000000000000000000000001681173133283/100000000000000000000000000000000000000000000000000), (17500000000000000000000000000000000000420293283321/25000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.CoupledFlowData.Cell097Term00
