import ForestUnimodality.BridgeFlowData.Stage80.Cell079Term01.Batch000

import ForestUnimodality.BridgeFlowData.Stage80.Cell079Term01.Batch001

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell079Term01
open CoupledFlow


def rows : List Row := Batch000.rows ++ Batch001.rows

theorem rows_length : rows.length=29 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  simp only [rows,List.all_append,Batch000.rows_checked, Batch001.rows_checked,Bool.and_self]

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (69517340191963352707319038766150629141/10000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (14868977874302000138230331740346990503317/10000000000000000000000000000000000000000)

def table : Table :=
  ⟨29, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨3, (-7641613320025139/10000000000000000), 64, (1862897421382778439869175893070387565854080744301/4000000000000000000000000000000000000000000000000), (23286217767284730498364698663379844573176009303763/50000000000000000000000000000000000000000000000000)⟩, (6464974625754315340723519997370683470102803183951857620968907943008052487461929225554701168598870034510062647269230659406972354310556455496702901/64000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (12626903565926397149850624994864616152544537468656785287861756436776205616612647957842936820818268404074964256412580110558655531098919260963999815947/125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage80.Cell079Term01
