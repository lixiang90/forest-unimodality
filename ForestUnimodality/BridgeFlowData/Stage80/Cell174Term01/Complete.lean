import ForestUnimodality.BridgeFlowData.Stage80.Cell174Term01.Batch000

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell174Term01
open CoupledFlow


def rows : List Row := Batch000.rows

theorem rows_length : rows.length=6 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  exact Batch000.rows_checked

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (1880284015022078036071402717873710921/2500000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (17534508720525238610609797490773298481681/10000000000000000000000000000000000000000)

def table : Table :=
  ⟨6, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨3, (-115129254649702284200899572734218210379/150000000000000000000000000000000000000), 64, (2900993021007986807756297719324654110364998293547/6250000000000000000000000000000000000000000000000), (46415888336127788924100763509194465765839972696753/100000000000000000000000000000000000000000000000000)⟩, (24414062500000000000000000000000000000515173062225636650771337541477310479717165710197941378699459979947267739157031662094680447803933706123378323/244140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (100000000000000000000000000000000000002110148862882671025629494221056341605621068800456636845537790779548945135767508132969913684394875304283329749777/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage80.Cell174Term01
