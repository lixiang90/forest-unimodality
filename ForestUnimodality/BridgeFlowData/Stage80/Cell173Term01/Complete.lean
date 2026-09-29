import ForestUnimodality.BridgeFlowData.Stage80.Cell173Term01.Batch000

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell173Term01
open CoupledFlow


def rows : List Row := Batch000.rows

theorem rows_length : rows.length=4 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  exact Batch000.rows_checked

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (11592162072264884208513335794895071857/5000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (12887104574137056395538802895094504641/8000000000000000000000000000000000000)

def table : Table :=
  ⟨4, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨2, (-9316092161051/10000000000000), 64, (1969596493880636550946321275595756601253448196121/5000000000000000000000000000000000000000000000000), (39391929877612731018926425511915132025068963922421/100000000000000000000000000000000000000000000000000)⟩, (3879310348706896374478501166192010082580798475054500115708026963236409621315492677558988879446641/25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (1551724139482758549791400466476804033032319390021878830142966010756601701377220901287645689706501241/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage80.Cell173Term01
