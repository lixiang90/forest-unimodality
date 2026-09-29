import ForestUnimodality.BridgeFlowData.Stage99.Cell141Term02.Batch000

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell141Term02
open CoupledFlow


def rows : List Row := Batch000.rows

theorem rows_length : rows.length=13 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  exact Batch000.rows_checked

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (129476579562331183392095314994011633797/10000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (3035319160930811617881859968569748731407/2000000000000000000000000000000000000000)

def table : Table :=
  ⟨13, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨2, (-916563286279147/1000000000000000), 64, (39989099309383425745805154825411508357903368808527/100000000000000000000000000000000000000000000000000), (2499318706836464109112822176588219272368960550533/6250000000000000000000000000000000000000000000000)⟩, (1599128063575729977934406468257548968234558439959967506167481242343734357463690061924497491587909729/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (6246593998342695226306275266631050657166243906093935485805078160918851436614612831801614446584089/39062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage99.Cell141Term02
