import ForestUnimodality.BridgeFlowData.Stage80.Cell188Term01.Batch000

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell188Term01
open CoupledFlow


def rows : List Row := Batch000.rows

theorem rows_length : rows.length=10 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  exact Batch000.rows_checked

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (20701029195157177559063817532369509143/10000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (1027780222319829803929827488361534431141/625000000000000000000000000000000000000)

def table : Table :=
  ⟨10, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨2, (-18843956942215073/20000000000000000), 64, (38977023787849123272364231250675752808605627162267/100000000000000000000000000000000000000000000000000), (9744255946962280818091057812668938202151406790567/25000000000000000000000000000000000000000000000000)⟩, (1519208383358556417339792852702785694537116735687249958558325978490279317862872778051147579148579289/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (94950523959909776083737053293924105908569795980457994537868854796051502895335883097297799400181489/625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage80.Cell188Term01
