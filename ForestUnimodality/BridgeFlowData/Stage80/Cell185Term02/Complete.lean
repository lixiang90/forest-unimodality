import ForestUnimodality.BridgeFlowData.Stage80.Cell185Term02.Batch000

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell185Term02
open CoupledFlow


def rows : List Row := Batch000.rows

theorem rows_length : rows.length=14 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  exact Batch000.rows_checked

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (6072491754153508780000463543169120659/5000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (848274597593021194005068402136278594363/500000000000000000000000000000000000000)

def table : Table :=
  ⟨14, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨3, (-20867177405258537/30000000000000000), 64, (49878876964491057601623702969160250370952030290189/100000000000000000000000000000000000000000000000000), (4987887696449105760162370296916025037095203029019/10000000000000000000000000000000000000000000000000)⟩, (124093776075171981570254767370231224397623692161700987664382722620061189685794303633443989308279600386357310257651521759008842904437530654906674021269/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (124093776075171981570254767370231224397623692161708451371484439130043240162849156924402009019823314098398936558226189681535118900971021659817413859/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage80.Cell185Term02
