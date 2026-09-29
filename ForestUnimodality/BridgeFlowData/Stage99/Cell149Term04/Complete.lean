import ForestUnimodality.BridgeFlowData.Stage99.Cell149Term04.Batch000

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell149Term04
open CoupledFlow


def rows : List Row := Batch000.rows

theorem rows_length : rows.length=12 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  exact Batch000.rows_checked

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (52366112044364595998288519721437061557/10000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (16707541895043599420225157930421396868951/10000000000000000000000000000000000000000)

def table : Table :=
  ⟨12, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨3, (-2295976662299297/3000000000000000), 64, (23259123213098349788658342294038580925809486878761/50000000000000000000000000000000000000000000000000), (46518246426196699577316684588077161851618973757523/100000000000000000000000000000000000000000000000000)⟩, (12582878931903735019580119350765000806444261240052934673807420880097194339083166853642507191814432113884077570563004514623086262818173364359435425081/125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (100663031455229880156640954806120006451554089920429969232211072126814439874178562917126289725774577284768524900654822350739138737098569304443359414667/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage99.Cell149Term04
