import ForestUnimodality.BridgeFlowData.Stage99.Cell125Term02.Batch000

import ForestUnimodality.CoupledFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell125Term02
open CoupledFlow


def rows : List Row := Batch000.rows

theorem rows_length : rows.length=12 := rfl

theorem rows_checked : rows.all (fun r=>r.check environment)=true := by

  exact Batch000.rows_checked

def rowAt (i : ℕ) : Row := rows.getD i Batch000.row000

def timeAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).start else finish

def lowerAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).lower else (26780947309685155048296490608123330131/5000000000000000000000000000000000000000)

def upperAt (i : ℕ) : ℚ := if i<rows.length then (rowAt i).totalUpper else (3307613033871313874576834168025015281533/2000000000000000000000000000000000000000)

def table : Table :=
  ⟨12, environment, qa, 2*qb, retention, rate, timeAt, lowerAt, upperAt, rowAt, ⟨3, (-759386201753331/1000000000000000), 64, (4679535679571238574102936664189976619813203360221/10000000000000000000000000000000000000000000000000), (46795356795712385741029366641899766198132033602211/100000000000000000000000000000000000000000000000000)⟩, (102472725831555369123577804345710290931598913576454054003192092494130863198782290686457168000627445576681515005970745379958728222424183000728073861/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000), (102472725831555369123577804345710290931598913576460623419445006570216502559358106175671884720943795461027439352335870542195933472838683412769725319931/1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)⟩

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

end ForestUnimodality.BridgeFlowData.Stage99.Cell125Term02
