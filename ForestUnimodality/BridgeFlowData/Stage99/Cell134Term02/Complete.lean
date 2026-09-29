import ForestUnimodality.BridgeFlowData.Stage99.Cell134Term02.Batch000

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell134Term02
open CoupledFlow


def rows : List Row := Batch000.rows

theorem rows_length : rows.length=13 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  exact Batch000.rows_checked

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (26019311039821539471418077180934623543/2000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (7571258872479642240546302286957075757883/5000000000000000000000000000000000000000)

def table : Table :=
  ⟨13, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨2, (-914618989546949/1000000000000000), 64, (40066925618696474151514004408068290239571544510339/100000000000000000000000000000000000000000000000000), (2003346280934823707575700220403414511978577225517/5000000000000000000000000000000000000000000000000)⟩, (1605358528534155837971627629650519760555400388691025879494529094870563634092371039689340647277894921/10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (4013396321335389594929069074126299401388500971727765033364416219547166655252967940674549475917289/25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage99.Cell134Term02
