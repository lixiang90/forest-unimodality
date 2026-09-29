import ForestUnimodality.BridgeFlowData.Stage99.Cell156Term00.Batch000

import ForestUnimodality.BridgeFlowData.Stage99.Cell156Term00.Batch001

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell156Term00
open CoupledFlow


def rows : List Row := Batch000.rows ++ Batch001.rows

theorem rows_length : rows.length=17 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  simp only [rows,List.all_append,Batch000.rows_checked, Batch001.rows_checked,Bool.and_self]

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (3743922429661561717062607751722069765451/10000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (10948574475394117256791840704106367209141/10000000000000000000000000000000000000000)

def table : Table :=
  ⟨17, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨1, (-2231435513142097/10000000000000000), 64, (80000000000000004461303607224786884665154810824433/100000000000000000000000000000000000000000000000000), (40000000000000002230651803612393442332577405412217/50000000000000000000000000000000000000000000000000)⟩, (80000000000000004461303607224786884665154810824433/100000000000000000000000000000000000000000000000000), (40000000000000002230651803612393442332577405412217/50000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage99.Cell156Term00
