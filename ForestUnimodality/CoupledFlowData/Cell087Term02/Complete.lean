import ForestUnimodality.CoupledFlowData.Cell087Term02.Batch000

import ForestUnimodality.CoupledFlowData.Cell087Term02.Batch001

import ForestUnimodality.CoupledFlowData.Cell087Term02.Batch002

import ForestUnimodality.CoupledFlowData.Cell087Term02.Batch003

import ForestUnimodality.CoupledFlowData.Cell087Term02.Batch004

import ForestUnimodality.CoupledFlowData.Cell087Term02.Batch005

import ForestUnimodality.CoupledFlowData.Cell087Term02.Batch006

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell087Term02
open CoupledFlow


def rows : List Row := Batch000.rows ++ Batch001.rows ++ Batch002.rows ++ Batch003.rows ++ Batch004.rows ++ Batch005.rows ++ Batch006.rows

theorem rows_length : rows.length=105 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  simp only [rows,List.all_append,Batch000.rows_checked, Batch001.rows_checked, Batch002.rows_checked, Batch003.rows_checked, Batch004.rows_checked, Batch005.rows_checked, Batch006.rows_checked,Bool.and_self]

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (696598002227399401215049418699498191269/10000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (11387339126270435880558225430830881697367/10000000000000000000000000000000000000000)

def table : Table :=
  ⟨105, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨2, (-104982212449867768832987083269936104601/200000000000000000000000000000000000000), 64, (59160797830996160425673282915616170485028133789673/100000000000000000000000000000000000000000000000000), (29580398915498080212836641457808085242514066894837/50000000000000000000000000000000000000000000000000)⟩, (3500000000000000000000000000000000000103309126925008964750908110198511874320246192312931364601446929/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (875000000000000000000000000000000000025827281731281821586642525629840805221519356163475355217256569/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.CoupledFlowData.Cell087Term02
