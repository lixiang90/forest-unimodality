import ForestUnimodality.BridgeFlowData.Stage80.Cell226Term02.Batch000

import ForestUnimodality.BridgeFlowData.Stage80.Cell226Term02.Batch001

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell226Term02
open CoupledFlow


def rows : List Row := Batch000.rows ++ Batch001.rows

theorem rows_length : rows.length=22 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  simp only [rows,List.all_append,Batch000.rows_checked, Batch001.rows_checked,Bool.and_self]

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (15658901877318147468876147462693896481/10000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (3164453666089761136757484841170125026551/1250000000000000000000000000000000000000)

def table : Table :=
  ⟨22, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨2, (-2987963976195263/3200000000000000), 64, (9827033244078791461743256275460861185320192078943/25000000000000000000000000000000000000000000000000), (39308132976315165846973025101843444741280768315773/100000000000000000000000000000000000000000000000000)⟩, (96570582380229736163794875317974647595255933981707757696583826937340092661611092022327840343997249/625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (1545129318083675778620718005087594361524094943707402739411293861329135428635981159246728007040587529/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage80.Cell226Term02
