import ForestUnimodality.BridgeFlowData.Stage80.Cell212Term01.Batch000

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell212Term01
open CoupledFlow


def rows : List Row := Batch000.rows

theorem rows_length : rows.length=7 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  exact Batch000.rows_checked

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (213027343277154685185294449517963925843/10000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (615945667863929106010468334217234150703/400000000000000000000000000000000000000)

def table : Table :=
  ⟨7, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨2, (-104982212449867768832987083269936104601/200000000000000000000000000000000000000), 64, (59160797830996160425673282915616170485028133789673/100000000000000000000000000000000000000000000000000), (29580398915498080212836641457808085242514066894837/50000000000000000000000000000000000000000000000000)⟩, (3500000000000000000000000000000000000103309126925008964750908110198511874320246192312931364601446929/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (875000000000000000000000000000000000025827281731281821586642525629840805221519356163475355217256569/2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage80.Cell212Term01
