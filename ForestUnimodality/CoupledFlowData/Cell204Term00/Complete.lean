import ForestUnimodality.CoupledFlowData.Cell204Term00.Batch000

import ForestUnimodality.CoupledFlowData.Cell204Term00.Batch001

import ForestUnimodality.CoupledFlowData.Cell204Term00.Batch002

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell204Term00
open CoupledFlow


def rows : List Row := Batch000.rows ++ Batch001.rows ++ Batch002.rows

theorem rows_length : rows.length=45 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  simp only [rows,List.all_append,Batch000.rows_checked, Batch001.rows_checked, Batch002.rows_checked,Bool.and_self]

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (3656427487496905655695462474155549727821/10000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (1418593881095187439694484287754070716437/1250000000000000000000000000000000000000)

def table : Table :=
  ⟨45, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨1, (-4462871026284195115325901806196690067/20000000000000000000000000000000000000), 64, (250000000000000000000000000000000000006150271387/312500000000000000000000000000000000000000000000), (80000000000000000000000000000000000001968086843841/100000000000000000000000000000000000000000000000000)⟩, (250000000000000000000000000000000000006150271387/312500000000000000000000000000000000000000000000), (80000000000000000000000000000000000001968086843841/100000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.CoupledFlowData.Cell204Term00
